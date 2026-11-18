import sys
import os
import ctypes
import subprocess
import re
import tempfile
import time
import shlex
import stat
import traceback
import adbutils
import platform
from PyQt6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, 
                             QHBoxLayout, QLabel, QLineEdit, QPushButton, 
                             QTextEdit, QFileDialog, QMessageBox, QInputDialog,
                             QRadioButton, QDialog, QScrollArea, QStyle,
                             QCheckBox, QGroupBox) 
from PyQt6.QtCore import (QSettings, QTimer, QProcess, Qt, QMimeData, QUrl, 
                          QThread, pyqtSignal, QObject)
from PyQt6.QtGui import QDrag
try:
    from PyQt6.QtGui import QAccessible, QAccessibleEvent
    QT_ACCESSIBILITY_AVAILABLE = True
except ImportError:
    QT_ACCESSIBILITY_AVAILABLE = False

# --- macOS / PyObjC availability -------------------------------------------------
# Split into two independent capability flags:
#   PYOBJC_AVAILABLE                -> core file-promise *providing* (drag OUT)
#   PYOBJC_PROMISE_RECEIVER_AVAILABLE -> file-promise *receiving* (drag IN)
# so that a missing symbol in one doesn't silently disable the other.
try:
    import objc
    from AppKit import (NSObject, NSFilePromiseProvider, NSDraggingItem, NSImage,
                         NSSize, NSApp, NSDragOperationCopy, NSPasteboard)
    from Foundation import NSURL, NSError, NSProgress
    PYOBJC_AVAILABLE = True
except ImportError:
    PYOBJC_AVAILABLE = False

PYOBJC_PROMISE_RECEIVER_AVAILABLE = False
if PYOBJC_AVAILABLE:
    try:
        from AppKit import NSFilePromiseReceiver
        from Foundation import NSOperationQueue
        try:
            from AppKit import NSPasteboardNameDrag
        except ImportError:
            # Older PyObjC/AppKit bridges may not export the modern constant name.
            NSPasteboardNameDrag = "com.apple.pasteboard.drag"
        PYOBJC_PROMISE_RECEIVER_AVAILABLE = True
    except ImportError:
        PYOBJC_PROMISE_RECEIVER_AVAILABLE = False


def _promise_uti(is_directory):
    """The UTI a file promise must advertise. NSFilePromiseProvider requires a
    type conforming to public.data or public.directory; using one value when
    creating the provider and another in the delegate makes Finder reject or
    mis-type the drop."""
    return "public.folder" if is_directory else "public.data"


def _qt_ns_view(widget):
    """Return the AppKit NSView behind a Qt top-level widget, or None.

    On macOS a QWidget's winId() is the pointer to its NSView. Wrapping it with
    objc.objc_object is the only reliable way to talk to AppKit from PyQt:
    NSApp.mainWindow() is NOT dependable in a Qt app (it is often None, or it
    is a different window than the one the user actually dragged from)."""
    if sys.platform != "darwin" or not PYOBJC_AVAILABLE or widget is None:
        return None
    try:
        return objc.objc_object(c_void_p=ctypes.c_void_p(int(widget.winId())))
    except Exception:
        return None


def _find_ancestor_with(widget, attribute):
    """Walk a Qt widget's parent chain looking for an object with `attribute`.

    Used both to find the real ADBClient window (the only object that owns
    promise_bridge) and the file-manager dialog that owns the selection."""
    w = widget
    while w is not None:
        if hasattr(w, attribute):
            return w
        try:
            w = w.parent()
        except Exception:
            break
    return None


def _promise_host(widget):
    """Locate the ADBClient instance that owns the promise bridge."""
    return _find_ancestor_with(widget, "promise_bridge")


def _should_accept_drag(event):
    """Decide whether to accept a drag Enter/Move event.

    Native file promises are not always described by QMimeData.formats(), and
    Qt does not always give them hasUrls(). Because a native view is only
    asked about pasteboard types we explicitly registered, it is safe on
    macOS to accept anything once promise support is loaded."""
    if event.mimeData().hasUrls():
        return True
    if sys.platform == "darwin" and PYOBJC_PROMISE_RECEIVER_AVAILABLE:
        # Accept immediately rather than repeatedly sniffing the drag
        # pasteboard on every dragMoveEvent.
        return True
    return _mime_has_file_promise(event.mimeData())


class _PromiseBridge(QObject):
    """Thread-safe bridge between AppKit's background file-promise callback
    threads and the Qt GUI thread.

    AppKit invokes filePromiseProvider:writePromiseToURL:completionHandler:
    on a background operation queue, not the main thread. Touching Qt
    objects (QTimer, widgets, etc.) directly from that thread is unsafe.
    Emitting a Qt signal here IS safe from any thread, because Qt detects
    the emitting thread differs from the receiving object's thread and
    automatically queues delivery onto that object's event loop."""
    pull_requested = pyqtSignal(str, str, object, object)
    error_logged = pyqtSignal(str)


class _VisibilityGroup:
    """Shows/hides several widgets together WITHOUT wrapping them in a
    container widget. A container widget becomes an extra 'group' in the
    macOS accessibility tree, which VoiceOver makes the user interact into
    before reaching the controls inside it."""
    def __init__(self, widgets):
        self._widgets = list(widgets)

    def show(self):
        for w in self._widgets:
            w.show()

    def hide(self):
        for w in self._widgets:
            w.hide()


# --- macOS file promise *provider* (drag OUT of this app) ------------------------
if sys.platform == "darwin" and PYOBJC_AVAILABLE:
    class AdbPromiseDelegate(NSObject):
        # NOTE: these are deliberately plain Python attributes, not
        # objc.ivar()s. The values include a PyQt QObject (the ADBClient host)
        # and an Objective-C completion block; storing those in `id` ivars
        # can hand back a different bridge object on read, which is exactly
        # how `main_window.promise_bridge` used to disappear on the AppKit
        # callback thread.

        def filePromiseProvider_fileTypeForURL_(self, provider, url):
            return _promise_uti(self.is_directory)

        def filePromiseProvider_fileNameForType_(self, provider, fileType):
            return self.file_name

        def _fail(self, handler, message):
            """Complete the promise with an error, without touching Qt."""
            try:
                if PYOBJC_AVAILABLE:
                    err = NSError.errorWithDomain_code_userInfo_(
                        "com.devtools.adbclient", 1,
                        {"NSLocalizedDescriptionKey": str(message)[:200]}
                    )
                    handler(err)
                else:
                    handler(None)
            except Exception as e:
                print(f"[File Promise] Could not report error to Finder: {e}")

        def filePromiseProvider_writePromiseToURL_completionHandler_(self, provider, url, handler):
            dest_path = url.path()

            try:
                if self.is_directory:
                    if not os.path.exists(dest_path):
                        os.makedirs(dest_path, exist_ok=True)
                else:
                    if not os.path.exists(dest_path):
                        open(dest_path, 'ab').close()
            except Exception as e:
                self._fail(handler, f"Could not create the drop destination: {e}")
                return

            # Finder expects long promise-writes to publish an NSProgress so
            # it can show real percentage feedback instead of a static
            # "Preparing..." spinner. Without this, large/slow transfers can
            # look stalled or failed even though they're still running.
            progress = None
            try:
                progress = NSProgress.progressWithTotalUnitCount_(100)
            except Exception:
                progress = None
            self.progress = progress
            # The progress must be attached to the provider, otherwise Finder
            # never sees it and the promise still looks stalled.
            if progress is not None and provider is not None:
                try:
                    provider.setProgress_(progress)
                except Exception:
                    try:
                        provider.progress = progress
                    except Exception:
                        pass

            # Re-resolve the host here rather than assuming the object stored
            # at drag-start is the main window. A DraggableItemButton lives in
            # AccessibleAndroidBrowser (a QDialog); that dialog has no
            # promise_bridge, so the old code silently dropped every promise
            # and handed Finder an EMPTY file.
            host = _promise_host(getattr(self, "main_window", None))
            if host is None:
                host = getattr(self, "main_window", None)
            if host is not None and hasattr(host, "promise_bridge"):
                try:
                    host.promise_bridge.pull_requested.emit(
                        self.remote_path, dest_path, handler, progress
                    )
                    return
                except Exception as e:
                    try:
                        host.log_error_from_thread(f"File Promise Handoff Error: {e}")
                    except Exception:
                        print(f"File Promise Handoff Error: {e}")

            self._fail(handler, "The app could not start the file transfer for this drop.")

        def draggingSession_sourceOperationMaskForDraggingContext_(self, session, context):
            return NSDragOperationCopy


# --- Shared drop resolution (handles both plain URLs and file promises) ----------
_PROMISE_FORMAT_HINTS = (
    "com.apple.nsfilepromiseitemmetadata",
    "com.apple.pasteboard.promised-file-content-type",
    "com.apple.pasteboard.promised-file-url",
    "nsfilespromisepboardtype",
    "com.apple.filepromise",
)

# Pasteboard types Qt normally accepts on its own. They are re-added whenever
# we register the extra file-promise types so that registering can never
# accidentally REMOVE plain Finder file-drop support.
_BASELINE_DRAG_TYPES = (
    "public.file-url",
    "public.url",
    "public.utf8-plain-text",
    "NSFilenamesPboardType",
)

# Root the watchdog QTimers used by incoming file promises. A parentless QTimer
# that is only referenced by a closure cycle can be garbage-collected while it
# is still supposed to be running.
_ACTIVE_PROMISE_TIMERS = set()


def _drag_pasteboards():
    """Yield the possible native drag pasteboards. Different PyObjC/AppKit
    versions expose NSPasteboardNameDrag under different names, so trying the
    literal values as well avoids silently seeing an empty drag pasteboard."""
    if sys.platform != "darwin" or not PYOBJC_PROMISE_RECEIVER_AVAILABLE:
        return
    names = []
    for candidate in (globals().get("NSPasteboardNameDrag"),
                      "com.apple.pasteboard.drag", "NSDragPboard"):
        if candidate and candidate not in names:
            names.append(candidate)
    for name in names:
        try:
            pb = NSPasteboard.pasteboardWithName_(name)
        except Exception:
            continue
        if pb is not None:
            yield pb


def _mime_has_file_promise(mime_data):
    """Best-effort check for whether a drag is carrying native macOS file
    promises (as opposed to plain file URLs, which Finder always uses for
    existing files). Used only to decide whether to accept a dragEnterEvent
    when hasUrls() is False."""
    if sys.platform != "darwin" or not PYOBJC_PROMISE_RECEIVER_AVAILABLE:
        return False
    try:
        formats = [f.lower() for f in mime_data.formats()]
    except Exception:
        formats = []
    if any(hint in fmt for fmt in formats for hint in _PROMISE_FORMAT_HINTS):
        return True
    # Qt does not always surface promise types through mime_data.formats(),
    # so also ask the drag pasteboard directly.
    try:
        return any(
            bool(pb.canReadObjectForClasses_options_([NSFilePromiseReceiver], None))
            for pb in _drag_pasteboards()
        )
    except Exception:
        return False


def register_file_promise_drop_types(widget):
    """Qt registers its window's NSView only for the pasteboard types Qt
    itself understands. Native file promises (Photos, Mail, Safari, ...) use
    additional types, and a view that never registered for them never gets
    the drag at all - dragEnterEvent is simply not called. This adds the
    NSFilePromiseReceiver types to the window's native view.

    Safe to call repeatedly. Returns (ok, detail)."""
    if sys.platform != "darwin" or not PYOBJC_PROMISE_RECEIVER_AVAILABLE:
        return False, "not applicable on this platform"
    try:
        ns_view = _qt_ns_view(widget)
        if ns_view is None:
            return False, "could not obtain the native NSView for this window"
        promise_types = list(NSFilePromiseReceiver.readableDraggedTypes() or [])
        try:
            existing = list(ns_view.registeredDraggedTypes() or [])
        except Exception:
            existing = []
        merged = []
        for t in existing + list(_BASELINE_DRAG_TYPES) + promise_types:
            if t not in merged:
                merged.append(t)
        ns_view.registerForDraggedTypes_(merged)
        return True, f"registered {len(promise_types)} file promise drag types"
    except Exception as e:
        return False, str(e)


def _report_drop_error(widget, message):
    """Send a drop-related error to the visible Terminal Output log of the
    main window (walking up the parent chain from whichever widget got the
    drop), falling back to print() only if no window with a log exists."""
    w = widget
    while w is not None:
        log_fn = getattr(w, "log", None)
        if callable(log_fn):
            try:
                log_fn(message)
                return
            except Exception:
                break
        try:
            w = w.parent()
        except Exception:
            break
    print(message)


def resolve_drop_paths(mime_data, temp_dir_hint, callback, error_callback=None):
    """
    Resolves a drop's contents into local filesystem paths, then calls
    callback(list_of_paths).

    Handles two cases:
      1. Plain file URLs (Finder, other file managers, most apps) -
         resolved synchronously, callback is invoked immediately.
      2. Native macOS file promises (apps that hand over a "promise" to
         write files rather than an existing path - e.g. Photos, Mail,
         some browsers) - resolved asynchronously via
         NSFilePromiseReceiver; callback is invoked once the OS finishes
         writing the promised files to a temp folder.

    error_callback(message), if given, is called when a file promise drop
    fails or delivers no files, so the failure is visible to the user.

    Returns True if the drop was recognized and is being handled (even if
    the actual callback fires later, asynchronously), False if nothing
    usable was found (caller should fall back to default handling).
    """
    if mime_data.hasUrls():
        paths = [u.toLocalFile() for u in mime_data.urls()
                 if u.isLocalFile() and os.path.exists(u.toLocalFile())]
        if paths:
            callback(paths)
            return True

    if sys.platform == "darwin" and PYOBJC_PROMISE_RECEIVER_AVAILABLE:
        # Try every spelling of the drag pasteboard. Older code only tried
        # NSPasteboardNameDrag; when that lookup returned an empty board,
        # promise drops silently did nothing (no error, no files).
        items = None
        for pb in _drag_pasteboards():
            try:
                found = pb.readObjectsForClasses_options_([NSFilePromiseReceiver], None)
            except Exception:
                found = None
            if found:
                items = found
                break

        if items:
            try:
                dest_dir = tempfile.mkdtemp(prefix="adbtool_promise_", dir=temp_dir_hint)
                dest_url = NSURL.fileURLWithPath_isDirectory_(dest_dir, True)
            except Exception as e:
                if error_callback is not None:
                    error_callback(f"File promise drop failed: could not create a temporary folder ({e})")
                return False

            # The reader block is invoked once PER PROMISED FILE, and a single
            # NSFilePromiseReceiver can promise several files. So the number of
            # completions to wait for is the total number of file names, not the
            # number of receivers (counting receivers made multi-file drops fire
            # the callback early and/or more than once).
            results = []
            errors = []
            counts = []
            state = {"remaining": 0, "done": False, "timer": None}
            for item in items:
                try:
                    n = len(item.fileNames() or [])
                except Exception:
                    n = 0
                n = max(1, n)
                counts.append(n)
                state["remaining"] += n

            queue = NSOperationQueue.mainQueue()

            def _maybe_finish():
                if state["remaining"] > 0 or state["done"]:
                    return
                state["done"] = True
                timer = state.get("timer")
                if timer is not None:
                    try:
                        timer.stop()
                    except Exception:
                        pass
                    _ACTIVE_PROMISE_TIMERS.discard(timer)
                if errors and error_callback is not None:
                    error_callback("File promise drop problem: " + "; ".join(errors))
                if results:
                    callback(results)
                elif not errors and error_callback is not None:
                    error_callback("File promise drop delivered no files.")

            # A promise can be fulfilled by the source app much later (or never,
            # if that app quits). A watchdog makes the failure visible instead
            # of leaving the drop permanently "pending".
            timer = QTimer()
            timer.setSingleShot(True)
            state["timer"] = timer

            def _on_timeout():
                if state["done"]:
                    return
                errors.append("timed out waiting for the source app to write the promised files")
                state["remaining"] = 0
                _maybe_finish()

            timer.timeout.connect(_on_timeout)
            _ACTIVE_PROMISE_TIMERS.add(timer)
            timer.start(45000)

            def _make_reader():
                def reader(file_url, error):
                    if error is not None:
                        try:
                            errors.append(str(error.localizedDescription()))
                        except Exception:
                            errors.append("unknown error")
                    elif file_url is not None:
                        try:
                            results.append(file_url.path())
                        except Exception as e:
                            errors.append(str(e))
                    state["remaining"] -= 1
                    _maybe_finish()
                return reader

            for item, n in zip(items, counts):
                try:
                    item.receivePromisedFilesAtDestination_options_operationQueue_reader_(
                        dest_url, {}, queue, _make_reader()
                    )
                except Exception as e:
                    errors.append(str(e))
                    state["remaining"] -= n
            _maybe_finish()

            return True

        # Promise-looking data that we could not read is a real failure; make
        # it visible rather than pretending the drop never happened.
        try:
            formats = [f.lower() for f in mime_data.formats()]
        except Exception:
            formats = []
        if any(hint in fmt for fmt in formats for hint in _PROMISE_FORMAT_HINTS):
            if error_callback is not None:
                error_callback("A file promise was dropped, but no readable promised files were found "
                               "on the macOS drag pasteboard.")

    return False


APP_VERSION = "0.0.18-beta"
class TerminalLineEdit(QLineEdit):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
    def dragEnterEvent(self, event):
        if _should_accept_drag(event):
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)
    def dragMoveEvent(self, event):
        # Qt requires the drag to be re-accepted on every move, or macOS
        # shows the "not allowed" cursor and dropEvent never fires.
        if _should_accept_drag(event):
            event.acceptProposedAction()
        else:
            super().dragMoveEvent(event)
    def dropEvent(self, event):
        handled = resolve_drop_paths(event.mimeData(), tempfile.gettempdir(), self._insert_paths,
                                     lambda msg: _report_drop_error(self, msg))
        if handled:
            event.acceptProposedAction()
        else:
            super().dropEvent(event)
    def _insert_paths(self, paths):
        if not paths:
            return
        current_text = self.text()
        paths_str = " ".join([shlex.quote(p) for p in paths])
        new_text = f"{current_text} {paths_str}".strip()
        self.setText(new_text)
class TrackedFile:
    def __init__(self, filepath, update_callback):
        self.file = open(filepath, 'rb')
        self.update_callback = update_callback
        self.last_pos = 0
    def read(self, size=-1):
        chunk = self.file.read(size)
        self._report()
        return chunk
    def __iter__(self):
        return self
    def __next__(self):
        chunk = self.file.read(65536) 
        if not chunk:
            raise StopIteration
        self._report()
        return chunk
    def _report(self):
        pos = self.file.tell()
        diff = pos - self.last_pos
        if diff > 0:
            self.update_callback(diff)
            self.last_pos = pos
    def close(self):
        self.file.close()
class AdbTransferThread(QThread):
    progress_update = pyqtSignal(int, float, float, str)
    finished_transfer = pyqtSignal(bool, str)
    def __init__(self, adb_path, serial, action, src_list, dest):
        super().__init__()
        self.adb_path = adb_path
        self.serial = serial
        self.action = action 
        self.src_list = src_list
        self.dest = dest.replace('//', '/') if dest.startswith('//') else dest
        self.is_cancelled = False
    def cancel(self):
        self.is_cancelled = True
    def run(self):
        try:
            subprocess.run([self.adb_path, "start-server"], check=False)
            client = adbutils.AdbClient(host="127.0.0.1", port=5037)
            device = client.device(self.serial) if self.serial else client.device()
            total_bytes = 0
            transfer_list = []
            if self.action == "push":
                for src in self.src_list:
                    src = src.replace('//', '/') if src.startswith('//') else src
                    if os.path.isfile(src):
                        size = os.path.getsize(src)
                        total_bytes += size
                        target = f"{self.dest.rstrip('/')}/{os.path.basename(src)}" if self.dest.endswith('/') else self.dest
                        transfer_list.append((src, target, size))
                    elif os.path.isdir(src):
                        base_name = os.path.basename(os.path.normpath(src))
                        remote_base = f"{self.dest.rstrip('/')}/{base_name}"
                        device.shell(["mkdir", "-p", remote_base])
                        
                        for root, _, files in os.walk(src):
                            rel_dir = os.path.relpath(root, src)
                            remote_dir = remote_base if rel_dir == '.' else f"{remote_base}/{rel_dir}".replace('\\', '/')
                            if rel_dir != '.':
                                device.shell(["mkdir", "-p", remote_dir])
                            
                            for f in files:
                                local_f = os.path.join(root, f)
                                remote_f = f"{remote_dir}/{f}"
                                size = os.path.getsize(local_f)
                                total_bytes += size
                                transfer_list.append((local_f, remote_f, size))
            
            elif self.action in ["pull", "move_to_mac"]:
                def recursive_remote_list(remote_path, local_base):
                    nonlocal total_bytes
                    fi = device.sync.stat(remote_path)
                    if fi.mode == 0:
                        raise Exception(f"Remote path not found or inaccessible: {remote_path}")
                    
                    if stat.S_ISDIR(fi.mode):
                        os.makedirs(local_base, exist_ok=True)
                        for item in device.sync.list(remote_path):
                            if item.path in ['.', '..']: continue
                            r_path = f"{remote_path.rstrip('/')}/{item.path}"
                            l_path = os.path.join(local_base, item.path)
                            recursive_remote_list(r_path, l_path)
                    else:
                        total_bytes += fi.size
                        transfer_list.append((local_base, remote_path, fi.size))
                for src in self.src_list:
                    src = src.replace('//', '/') if src.startswith('//') else src
                    src_stat = device.sync.stat(src)
                    if src_stat.mode != 0 and stat.S_ISDIR(src_stat.mode):
                        base_name = os.path.basename(src.rstrip('/'))
                        local_target = os.path.join(self.dest, base_name)
                    else:
                        if os.path.isdir(self.dest):
                            local_target = os.path.join(self.dest, os.path.basename(src))
                        else:
                            local_target = self.dest
                    recursive_remote_list(src, local_target)
            elif self.action in ["android_move", "android_copy"]:
                # Multiple selected items are copied/moved one after another in
                # the same thread so progress stays on a single progress bar.
                dest = self.dest
                start_time = time.time()
                sources = []
                for raw_src in self.src_list:
                    src = raw_src.replace('//', '/') if raw_src.startswith('//') else raw_src
                    fi = device.sync.stat(src)
                    if fi.mode == 0:
                        raise Exception(f"Source not found: {src}")
                    size = fi.size
                    if self.action == "android_copy" and stat.S_ISDIR(fi.mode):
                        try:
                            res = device.shell(["du", "-sk", src])
                            match = re.search(r'^(\d+)', res.strip())
                            if match:
                                size = int(match.group(1)) * 1024
                        except Exception:
                            pass
                    sources.append((src, size, os.path.basename(src.rstrip('/'))))
                    total_bytes += size

                if self.action == "android_move":
                    for src, size, fname in sources:
                        if self.is_cancelled:
                            self.finished_transfer.emit(False, "Transfer cancelled by user.")
                            return
                        device.shell(["mv", src, dest])
                        self.progress_update.emit(100, 0, 0, fname)
                else:
                    dest_is_dir = False
                    try:
                        dest_is_dir = bool(device.sync.stat(dest).mode & stat.S_IFDIR)
                    except Exception:
                        pass
                    bytes_done = 0
                    for src, size, fname in sources:
                        if self.is_cancelled:
                            self.finished_transfer.emit(False, "Transfer cancelled by user.")
                            return
                        cmd_list = [self.adb_path]
                        if self.serial:
                            cmd_list.extend(["-s", self.serial])
                        cmd_list.extend(["shell", "cp", "-a", src, dest])

                        proc = subprocess.Popen(cmd_list)
                        dest_path = f"{dest.rstrip('/')}/{fname}" if dest_is_dir else dest

                        while proc.poll() is None:
                            if self.is_cancelled:
                                proc.kill()
                                self.finished_transfer.emit(False, "Transfer cancelled by user.")
                                return

                            try:
                                fi_dest = device.sync.stat(dest_path)
                                if stat.S_ISDIR(fi_dest.mode):
                                    res = device.shell(["du", "-sk", dest_path])
                                    match = re.search(r'^(\d+)', res.strip())
                                    current_bytes = int(match.group(1)) * 1024 if match else 0
                                else:
                                    current_bytes = fi_dest.size
                                current_bytes = min(current_bytes, size)

                                done = bytes_done + current_bytes
                                percent = int(done / total_bytes * 100) if total_bytes > 0 else 0
                                percent = min(100, percent)
                                elapsed = time.time() - start_time
                                mb_trans = done / (1024 * 1024)
                                mb_sec = mb_trans / elapsed if elapsed > 0 else 0

                                self.progress_update.emit(percent, mb_sec, mb_trans, fname)
                            except Exception:
                                pass
                            time.sleep(1)

                        if proc.returncode != 0:
                            raise Exception("Internal copy failed.")
                        bytes_done += size
                        pct = min(100, int(bytes_done / total_bytes * 100)) if total_bytes else 100
                        self.progress_update.emit(pct, 0, 0, fname)

                self.finished_transfer.emit(True, "File transfer completed successfully.")
                return
            if total_bytes == 0 and len(transfer_list) == 0:
                self.finished_transfer.emit(True, "Nothing to transfer or size is 0 bytes.")
                return
            start_time = time.time()
            bytes_transferred = 0
            for local_f, remote_f, size in transfer_list:
                if self.is_cancelled:
                    self.finished_transfer.emit(False, "Transfer cancelled by user.")
                    return
                fname = os.path.basename(local_f)
                def update_progress(chunk_size):
                    nonlocal bytes_transferred
                    if self.is_cancelled:
                        raise InterruptedError("Cancelled")
                    bytes_transferred += chunk_size
                    percent = int((bytes_transferred / total_bytes) * 100) if total_bytes > 0 else 0
                    percent = min(100, percent) 
                    elapsed = time.time() - start_time
                    mb_trans = bytes_transferred / (1024 * 1024)
                    mb_sec = mb_trans / elapsed if elapsed > 0 else 0
                    self.progress_update.emit(percent, mb_sec, mb_trans, fname)
                try:
                    if self.action == "push":
                        tracked_file = TrackedFile(local_f, update_progress)
                        device.sync.push(tracked_file, remote_f)
                        tracked_file.close()
                    elif self.action in ["pull", "move_to_mac"]:
                        with open(local_f, 'wb') as f:
                            for chunk in device.sync.iter_content(remote_f):
                                f.write(chunk)
                                update_progress(len(chunk))
                except InterruptedError:
                    self.finished_transfer.emit(False, "Transfer cancelled by user.")
                    return
            if self.action == "move_to_mac" and not self.is_cancelled:
                for src in self.src_list:
                    device.shell(["rm", "-rf", src])
            self.finished_transfer.emit(True, "File transfer completed successfully.")
        except Exception as e:
            err_msg = f"Exception: {str(e)}\n\nTraceback:\n{traceback.format_exc()}"
            self.finished_transfer.emit(False, err_msg)
class PreferencesDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.main_app = parent
        self.setWindowTitle("Preferences")
        self.setAccessibleName("Preferences Dialog")
        self.resize(550, 600)
        
        layout = QVBoxLayout(self)
        
        layout.addWidget(QLabel("ADB Executable Path:"))
        self.adb_input = QLineEdit(self.main_app.adb_path)
        self.adb_input.setAccessibleName("ADB Path")
        self.adb_btn = QPushButton("Browse ADB")
        self.adb_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileIcon))
        self.adb_btn.clicked.connect(lambda: self.browse_file(self.adb_input))
        adb_layout = QHBoxLayout()
        adb_layout.addWidget(self.adb_input)
        adb_layout.addWidget(self.adb_btn)
        layout.addLayout(adb_layout)
        
        layout.addWidget(QLabel("Fastboot Executable Path:"))
        self.fb_input = QLineEdit(self.main_app.fastboot_path)
        self.fb_input.setAccessibleName("Fastboot Path")
        self.fb_btn = QPushButton("Browse Fastboot")
        self.fb_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileIcon))
        self.fb_btn.clicked.connect(lambda: self.browse_file(self.fb_input))
        fb_layout = QHBoxLayout()
        fb_layout.addWidget(self.fb_input)
        fb_layout.addWidget(self.fb_btn)
        layout.addLayout(fb_layout)
        
        layout.addWidget(QLabel("Default Local Save Directory:"))
        self.save_input = QLineEdit(self.main_app.save_dir)
        self.save_input.setAccessibleName("Local Save Directory")
        self.save_btn = QPushButton("Browse Save Dir")
        self.save_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DirIcon))
        self.save_btn.clicked.connect(lambda: self.browse_dir(self.save_input))
        save_layout = QHBoxLayout()
        save_layout.addWidget(self.save_input)
        save_layout.addWidget(self.save_btn)
        layout.addLayout(save_layout)
        
        layout.addWidget(QLabel("Default Android Start Directory:"))
        self.android_input = QLineEdit(self.main_app.default_android_dir)
        self.android_input.setAccessibleName("Default Android Directory")
        self.android_btn = QPushButton("Browse Android Dir")
        self.android_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ComputerIcon))
        self.android_btn.clicked.connect(lambda: self.browse_android_dir(self.android_input))
        android_layout = QHBoxLayout()
        android_layout.addWidget(self.android_input)
        android_layout.addWidget(self.android_btn)
        layout.addLayout(android_layout)
        
        acc_heading = QLabel("Accessibility Controls")
        font = acc_heading.font()
        font.setBold(True)
        acc_heading.setFont(font)
        acc_heading.setStyleSheet("margin-top: 10px;")
        layout.addWidget(acc_heading)
        self.announce_checkbox = QCheckBox("Announce Terminal Updates Instantly")
        self.announce_checkbox.setAccessibleName("Announce Terminal Updates Instantly")
        self.announce_checkbox.setChecked(self.main_app.announce_terminal)
        layout.addWidget(self.announce_checkbox)
        self.announce_transfers_checkbox = QCheckBox("Announce File Transfer Progress")
        self.announce_transfers_checkbox.setAccessibleName("Announce File Transfer Progress")
        self.announce_transfers_checkbox.setAccessibleDescription("When enabled, the screen reader will dynamically read percentage updates during file transfers.")
        self.announce_transfers_checkbox.setChecked(self.main_app.announce_transfers)
        layout.addWidget(self.announce_transfers_checkbox)
        self.skip_announce_checkbox = QCheckBox("Skip Announcing Executable Paths")
        self.skip_announce_checkbox.setAccessibleName("Skip Announcing Executable Paths")
        self.skip_announce_checkbox.setChecked(self.main_app.skip_command_announce)
        layout.addWidget(self.skip_announce_checkbox)
        
        self.read_final_checkbox = QCheckBox("Read Terminal Output Only After Command Finishes")
        self.read_final_checkbox.setAccessibleName("Read Terminal Output Only After Command Finishes")
        self.read_final_checkbox.setChecked(self.main_app.read_final_only)
        layout.addWidget(self.read_final_checkbox)
        self.show_sizes_checkbox = QCheckBox("Show file sizes within file manager (takes longer to load)")
        self.show_sizes_checkbox.setAccessibleName("Show file sizes within file manager")
        self.show_sizes_checkbox.setChecked(self.main_app.show_file_sizes)
        layout.addWidget(self.show_sizes_checkbox)
        
        layout.addStretch()
        
        os_name = sys.platform
        arch = platform.machine()
        plat_label = QLabel(f"Detected Platform: {os_name} ({arch})")
        plat_label.setStyleSheet("font-weight: bold; color: #888888;")
        layout.addWidget(plat_label)
        rn_heading = QLabel("Release Notes")
        rn_heading.setFont(font)
        layout.addWidget(rn_heading)
        rn_text = QTextEdit()
        rn_text.setReadOnly(True)
        rn_text.setText(f"Version {APP_VERSION}\n"
                        "- File Manager now supports multi-select: Control/Command-click to add items, or use Select All / Clear Selection. Copy, Move, Delete, and drag-out all operate on the whole selection.\n"
                        "- Fixed macOS File Promises: drag-out now finds the real main window instead of the file-manager dialog (the old path silently produced empty files), starts the native drag from the correct NSView, advertises the right folder/file type, and completes Finder's promise reliably.\n"
                        "- Incoming File Promise drops now try every drag pasteboard name, report failures visibly, and time out instead of hanging forever.\n"
                        "- Main window accessibility: the section boxes and the hidden progress container that VoiceOver treated as groups have been removed. Section titles are now plain headings and every control sits directly on the page.\n"
                        "- Fixed multi-file drops of macOS File Promises firing early or more than once. The app now waits for every promised file.\n"
                        "- File Promise drop failures are now reported in the Terminal Output log instead of failing silently.\n"
                        "- The window now registers for native file promise drag types, which Qt does not do on its own.\n"
                        "- Added an accessibility debug dump (launch with ADB_A11Y_DEBUG=1) that lists the roles Qt exposes to VoiceOver.\n"
                        "- Fixed a real bug behind large drag-out failures: the old fallback drag path buffered adb's progress text in a never-trimmed string for the whole transfer, which slowed to a crawl on big files. Replaced with a byte-counted chunked pull.\n"
                        "- Outgoing macOS File Promises now publish real NSProgress so Finder shows an actual percentage on large/slow transfers instead of a static 'Preparing...' spinner.\n"
                        "- File-promise and drag errors are now written to the visible Terminal Output log instead of a console print() that a packaged app's user could never see.\n"
                        "- Added a one-time startup check that reports whether native macOS drag-out support actually loaded, with install instructions if not.\n"
                        "- Large-file drags on the non-native fallback path now warn up front and suggest 'Copy to Computer' instead of silently struggling.\n"
                        "- Fixed drag-and-drop acceptance: added missing dragMoveEvent handlers so drags from Finder (and elsewhere) are no longer rejected mid-drag.\n"
                        "- Fixed a thread-safety bug in outgoing macOS File Promises: AppKit's write callback now hands off to the Qt main thread through a proper signal instead of touching Qt objects from a background thread.\n"
                        "- Outgoing File Promises now correctly handle dragging whole folders, not just single files.\n"
                        "- Added support for receiving native macOS File Promises dropped into the app (e.g. from Photos, Mail, or browsers), in addition to plain Finder file drops.\n"
                        "- Added an 'Insert File Path' button next to the terminal input as a non-drag, screen-reader-friendly alternative to drag-and-drop.")
        rn_text.setMaximumHeight(140)
        rn_text.setStyleSheet("background-color: #1e1e1e; color: #d4d4d4;")
        layout.addWidget(rn_text)
        version_label = QLabel(f"Developers: Elwin Rivera, Claude AI, and Gemini AI")
        version_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        version_label.setAccessibleName(f"Developers: Elwin Rivera, Claude AI, and Gemini AI.")
        layout.addWidget(version_label)
        
        self.save_prefs_btn = QPushButton("Save Preferences")
        self.save_prefs_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogSaveButton))
        self.save_prefs_btn.setAccessibleName("Save Preferences")
        self.save_prefs_btn.clicked.connect(self.save_preferences)
        layout.addWidget(self.save_prefs_btn)
        
    def browse_file(self, line_edit):
        path, _ = QFileDialog.getOpenFileName(self, "Select Executable")
        if path:
            line_edit.setText(path)
            
    def browse_dir(self, line_edit):
        path = QFileDialog.getExistingDirectory(self, "Select Directory")
        if path:
            line_edit.setText(path)
    def browse_android_dir(self, line_edit):
        serial = self.main_app.get_current_serial()
        dialog = AccessibleAndroidBrowser(self.main_app.adb_path, serial=serial, mode="select_dir", start_path=line_edit.text(), parent=self)
        if dialog.exec() == QDialog.DialogCode.Accepted and dialog.selected_path:
            line_edit.setText(dialog.selected_path)
            
    def save_preferences(self):
        self.main_app.adb_path = self.adb_input.text().strip()
        self.main_app.fastboot_path = self.fb_input.text().strip()
        self.main_app.save_dir = self.save_input.text().strip()
        self.main_app.announce_terminal = self.announce_checkbox.isChecked()
        self.main_app.announce_transfers = self.announce_transfers_checkbox.isChecked()
        self.main_app.skip_command_announce = self.skip_announce_checkbox.isChecked()
        self.main_app.read_final_only = self.read_final_checkbox.isChecked()
        self.main_app.show_file_sizes = self.show_sizes_checkbox.isChecked()
        
        android_dir = self.android_input.text().strip()
        if not android_dir.endswith('/'):
            android_dir += '/'
        self.main_app.default_android_dir = android_dir
        
        self.main_app.settings.setValue("adb_path", self.main_app.adb_path)
        self.main_app.settings.setValue("fastboot_path", self.main_app.fastboot_path)
        self.main_app.settings.setValue("save_dir", self.main_app.save_dir)
        self.main_app.settings.setValue("default_android_dir", self.main_app.default_android_dir)
        self.main_app.settings.setValue("announce_terminal", self.main_app.announce_terminal)
        self.main_app.settings.setValue("announce_transfers", self.main_app.announce_transfers)
        self.main_app.settings.setValue("skip_command_announce", self.main_app.skip_command_announce)
        self.main_app.settings.setValue("read_final_only", self.main_app.read_final_only)
        self.main_app.settings.setValue("show_file_sizes", self.main_app.show_file_sizes)
        
        self.main_app.update_live_region_settings()
        
        QMessageBox.information(self, "Saved", "Preferences have been updated.")
        self.accept()
class DeviceSelectionDialog(QDialog):
    def __init__(self, adb_path, current_serial, parent=None):
        super().__init__(parent)
        self.adb_path = adb_path
        self.selected_serial = current_serial
        
        self.setWindowTitle("Device Manager")
        self.setAccessibleName("Device Manager Dialog")
        self.resize(400, 300)
        layout = QVBoxLayout(self)
        layout.addWidget(QLabel("Select a device to target with commands:"))
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_content = QWidget()
        self.scroll_layout = QVBoxLayout(self.scroll_content)
        self.scroll_layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        self.scroll_area.setWidget(self.scroll_content)
        layout.addWidget(self.scroll_area)
        self.radio_buttons = []
        default_radio = QRadioButton("Default / Any Device")
        default_radio.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DesktopIcon))
        if not current_serial:
            default_radio.setChecked(True)
        self.scroll_layout.addWidget(default_radio)
        self.radio_buttons.append((default_radio, None))
        self.fetch_devices(current_serial)
        btn_layout = QHBoxLayout()
        ok_btn = QPushButton("OK")
        ok_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogOkButton))
        ok_btn.clicked.connect(self.accept_selection)
        
        cancel_btn = QPushButton("Cancel")
        cancel_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogCancelButton))
        cancel_btn.clicked.connect(self.reject)
        btn_layout.addWidget(ok_btn)
        btn_layout.addWidget(cancel_btn)
        layout.addLayout(btn_layout)
    def fetch_devices(self, current_serial):
        if not self.adb_path or not os.path.exists(self.adb_path):
            return
            
        try:
            res = subprocess.run([self.adb_path, "devices"], capture_output=True, text=True, timeout=2)
            lines = res.stdout.strip().split('\n')[1:] 
            
            for line in lines:
                if '\t' in line:
                    serial, state = line.split('\t')
                    if state == 'device':
                        rb = QRadioButton(f"Device: {serial}")
                        rb.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DriveHDIcon))
                        if serial == current_serial:
                            rb.setChecked(True)
                        self.scroll_layout.addWidget(rb)
                        self.radio_buttons.append((rb, serial))
        except Exception:
            pass
    def accept_selection(self):
        for rb, serial in self.radio_buttons:
            if rb.isChecked():
                self.selected_serial = serial
                break
        self.accept()
class DraggableItemButton(QPushButton):
    def __init__(self, text, adb_cmd, remote_path, is_dir):
        super().__init__(text)
        self.adb_cmd = adb_cmd  
        self.remote_path = remote_path
        self.is_dir = is_dir
        self.drag_start_pos = None
    def mousePressEvent(self, event):
        if sys.platform == "darwin" and PYOBJC_AVAILABLE:
            try:
                self._mac_press_event = NSApp.currentEvent()
            except Exception:
                self._mac_press_event = None
        if event.button() == Qt.MouseButton.LeftButton:
            self.drag_start_pos = event.pos()
        super().mousePressEvent(event)
    def mouseMoveEvent(self, event):
        if not self.drag_start_pos or not (event.buttons() & Qt.MouseButton.LeftButton):
            super().mouseMoveEvent(event)
            return
        if (event.pos() - self.drag_start_pos).manhattanLength() < QApplication.startDragDistance():
            return

        main_win = self.window()
        host = _promise_host(self)

        # If this button is part of a multi-selection, drag every selected
        # item, not just the one that happened to receive the mouse-down.
        browser = _find_ancestor_with(self, "selected_targets")
        targets = browser.selected_targets() if browser is not None else []
        normalized_remote = self.remote_path.rstrip('/')
        if normalized_remote not in [path.rstrip('/') for path, _ in targets]:
            targets = [(self.remote_path, self.is_dir)]

        def report_error(message):
            if host is not None and hasattr(host, "log_error_from_thread"):
                host.log_error_from_thread(message)
            else:
                print(message)

        if sys.platform == "darwin" and PYOBJC_AVAILABLE:
            try:
                delegates = []
                providers = []
                drag_items = []
                for remote_path, is_directory in targets:
                    delegate = AdbPromiseDelegate.alloc().init()
                    delegate.adb_cmd = self.adb_cmd
                    delegate.remote_path = remote_path
                    delegate.file_name = os.path.basename(remote_path.rstrip('/'))
                    delegate.is_directory = is_directory
                    # Store the ADBClient, not the file-manager dialog: the
                    # dialog has no promise_bridge.
                    delegate.main_window = host or main_win

                    uti = _promise_uti(is_directory)
                    provider = NSFilePromiseProvider.alloc().initWithFileType_delegate_(uti, delegate)
                    item = NSDraggingItem.alloc().initWithPasteboardWriter_(provider)
                    img = NSImage.alloc().initWithSize_(NSSize(32, 32))
                    item.setDraggingFrame_contents_(((0, 0), (32, 32)), img)
                    delegates.append(delegate)
                    providers.append(provider)
                    drag_items.append(item)

                # Keep strong references alive for the whole drag session.
                self._mac_delegates = delegates
                self._mac_providers = providers
                self._mac_drag_items = drag_items

                # Do NOT use NSApp.mainWindow() here: in a Qt app it is often
                # None or points at a different window. Use the NSView behind
                # the window the button actually belongs to.
                ns_view = _qt_ns_view(main_win)
                mac_event = getattr(self, '_mac_press_event', None) or NSApp.currentEvent()
                if ns_view is None:
                    raise RuntimeError("no native NSView for the file manager window")
                if mac_event is None:
                    raise RuntimeError("no native mouse-down event for this drag")

                ns_view.beginDraggingSessionWithItems_event_source_(drag_items, mac_event, delegates[0])
                return
            except Exception as e:
                report_error(f"Native drag-out failed to start ({e}); falling back to a slower method.")
            # fall through to the generic fallback below rather than just
            # silently returning and doing nothing.

        self._run_fallback_drag(main_win, targets)

    def _estimate_remote_size(self):
        """Quick stat call so we can show real percentages and warn about
        very large items before committing to a blocking pull."""
        return self._estimate_remote_size_for(self.remote_path)

    def _pull_for_drag(self, remote_path, local_dest, size_bytes):
        """Chunked pull using adbutils directly, tracking raw byte counts.

        The previous implementation shelled out to `adb pull -p` and
        scraped percentages out of its text output into a string buffer
        that was NEVER TRIMMED - it grew for the entire length of the
        transfer. For a small file that finishes in a second or two this
        was invisible; for a 60GB transfer, that unbounded string kept
        getting re-copied on every append (classic O(n^2) behavior),
        which could make the whole thing grind to a crawl or appear to
        hang/fail long before completion. Tracking a plain integer byte
        count instead avoids that entirely, and is also more reliable
        than parsing `-p` output (format varies across adb versions)."""
        subprocess.run([self.adb_cmd[0], "start-server"], check=False)
        client = adbutils.AdbClient(host="127.0.0.1", port=5037)
        serial = None
        if "-s" in self.adb_cmd:
            idx = self.adb_cmd.index("-s")
            serial = self.adb_cmd[idx + 1]
        device = client.device(serial) if serial else client.device()

        bytes_done = 0
        last_ui_update = 0.0
        with open(local_dest, 'wb') as f:
            for chunk in device.sync.iter_content(remote_path):
                f.write(chunk)
                bytes_done += len(chunk)
                now = time.time()
                if now - last_ui_update > 0.1:  # throttle UI text updates
                    last_ui_update = now
                    if size_bytes:
                        pct = min(100, int(bytes_done / size_bytes * 100))
                        self.setText(f"Preparing for drop... {pct}%")
                    else:
                        self.setText(f"Preparing for drop... {bytes_done / (1024 * 1024):.1f} MB")
                    QApplication.processEvents()
        return True

    def _estimate_remote_size_for(self, remote_path):
        subprocess.run([self.adb_cmd[0], "start-server"], check=False)
        client = adbutils.AdbClient(host="127.0.0.1", port=5037)
        serial = None
        if "-s" in self.adb_cmd:
            idx = self.adb_cmd.index("-s")
            serial = self.adb_cmd[idx + 1]
        device = client.device(serial) if serial else client.device()
        return device.sync.stat(remote_path).size

    def _run_fallback_drag(self, main_win, targets=None):
        """Generic (non-macOS-promise) drag-out: the file has to be fully
        downloaded locally before Qt's QDrag can start, which means
        holding the mouse button down for the whole pull. There is no
        real equivalent of macOS file promises exposed through Qt on
        Windows/Linux, so for very large items we warn up front and
        point at the non-drag 'Copy to Computer' action instead, rather
        than let it silently struggle."""
        targets = targets or [(self.remote_path, self.is_dir)]
        original_text = self.text()
        file_targets = [(p, d) for p, d in targets if not d]
        skipped_dirs = [p for p, d in targets if d]

        sizes = {}
        for path, _ in file_targets:
            try:
                sizes[path] = self._estimate_remote_size_for(path)
            except Exception:
                sizes[path] = None

        LARGE_THRESHOLD = 500 * 1024 * 1024  # 500 MB
        if any(size and size > LARGE_THRESHOLD for size in sizes.values()):
            proceed = QMessageBox.question(
                self, "Large File",
                "One or more selected items are very large. Dragging them out has to "
                "fully download them first, and the mouse button has to stay held down "
                "the whole time - for large files this is slow and easy to interrupt by "
                "accident.\n\n"
                "For large files, the item menu's 'Copy to Computer' action is much "
                "more reliable.\n\nContinue with the drag anyway?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No
            )
            if proceed != QMessageBox.StandardButton.Yes:
                return

        if skipped_dirs:
            QMessageBox.information(
                self, "Folders Cannot Be Dragged Here",
                "Native drag support is unavailable, so folders cannot be dragged out "
                "with this method. Use the item menu's 'Copy to Computer' action for them."
            )
        if not file_targets:
            return

        self.setText("Preparing...")
        self.setEnabled(False)
        QApplication.processEvents()

        temp_dir = tempfile.gettempdir()
        local_paths = []
        error_message = None
        try:
            for path, _ in file_targets:
                base_name = os.path.basename(path.rstrip('/')) or "file"
                local_dest = os.path.join(temp_dir, base_name)
                self._pull_for_drag(path, local_dest, sizes.get(path))
                if os.path.exists(local_dest):
                    local_paths.append(local_dest)
        except Exception as e:
            error_message = f"{e}\n\n{traceback.format_exc()}"

        self.setText(original_text)
        self.setEnabled(True)

        if local_paths:
            drag = QDrag(self)
            mime = QMimeData()
            mime.setUrls([QUrl.fromLocalFile(p) for p in local_paths])
            drag.setMimeData(mime)
            drag.exec(Qt.DropAction.CopyAction)
        else:
            msg = "Could not prepare the selected items for dragging."
            if main_win is not None and hasattr(main_win, "log"):
                main_win.log(f"Drag-out failed: {msg}\n{error_message or ''}")
            QMessageBox.warning(self, "Drag Failed", msg + (f"\n\n{error_message}" if error_message else ""))
class AccessibleAndroidBrowser(QDialog):
    def __init__(self, adb_path, serial=None, mode="pull", start_path="/sdcard/", parent=None):
        super().__init__(parent)
        self.adb_path = adb_path
        self.serial = serial
        self.adb_cmd = [adb_path]
        if serial:
            self.adb_cmd.extend(["-s", serial])
            
        self.mode = mode 
        self.current_path = start_path if start_path.endswith('/') else start_path + '/'
        # Multi-selection. Names are relative to current_path so the selection
        # is invalidated naturally whenever the folder changes.
        self.selected_names = []
        self.selected_is_dir = {}
        self.selected_path = None
        self.current_items = []
        self.item_buttons = []
        
        self.setWindowTitle("Android Device File Manager")
        self.setAccessibleName("Android Device File Manager Dialog")
        self.resize(650, 500)
        self.setAcceptDrops(True)
        
        layout = QVBoxLayout(self)
        
        top_layout = QVBoxLayout()
        
        self.path_label = QLabel(f"Current Directory: {self.current_path}")
        top_layout.addWidget(self.path_label)
        self.selected_label = QLabel("Selected: None (actions apply to the current folder)")
        self.selected_label.setAccessibleName("No items selected; actions apply to the current folder")
        self.selected_label.setStyleSheet("font-weight: bold; color: #FFA500;")
        top_layout.addWidget(self.selected_label)
        
        action_layout = QHBoxLayout()
        
        self.up_btn = QPushButton("Go Up One Directory")
        self.up_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ArrowUp))
        self.up_btn.setAccessibleName("Go Up One Directory")
        self.up_btn.clicked.connect(self.go_up)
        action_layout.addWidget(self.up_btn)
        self.menu_btn = QPushButton("Menu")
        self.menu_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_TitleBarMenuButton))
        self.menu_btn.setAccessibleName("Open Menu for selected items or current folder")
        self.menu_btn.setAccessibleDescription("Copy, move, or delete every selected item at once.")
        self.menu_btn.clicked.connect(self.open_menu)
        action_layout.addWidget(self.menu_btn)

        self.select_all_btn = QPushButton("Select All")
        self.select_all_btn.setAccessibleName("Select All Items in This Folder")
        self.select_all_btn.clicked.connect(self.select_all)
        action_layout.addWidget(self.select_all_btn)
        self.clear_selection_btn = QPushButton("Clear Selection")
        self.clear_selection_btn.setAccessibleName("Clear Selection")
        self.clear_selection_btn.clicked.connect(self.clear_selection)
        action_layout.addWidget(self.clear_selection_btn)

        if self.mode == "select_dir":
            self.select_all_btn.hide()
            self.clear_selection_btn.hide()
            self.select_dir_btn = QPushButton("SELECT THIS DIRECTORY")
            self.select_dir_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogOkButton))
            self.select_dir_btn.setAccessibleName("Confirm and select this entire directory")
            self.select_dir_btn.clicked.connect(self.select_current_directory)
            action_layout.addWidget(self.select_dir_btn)
            
        top_layout.addLayout(action_layout)
        layout.addLayout(top_layout)
        
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_content = QWidget()
        self.scroll_layout = QVBoxLayout(self.scroll_content)
        self.scroll_layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        self.scroll_area.setWidget(self.scroll_content)
        layout.addWidget(self.scroll_area)
        
        self.cancel_btn = QPushButton("Cancel / Close")
        self.cancel_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DialogCancelButton))
        self.cancel_btn.setAccessibleName("Cancel File Browser")
        self.cancel_btn.clicked.connect(self.reject)
        layout.addWidget(self.cancel_btn)
        
        self.load_directory(self.current_path)
    def showEvent(self, event):
        super().showEvent(event)
        # Qt only registers its native view for the drag types it understands.
        # Add the native file promise types (best-effort; never raises).
        register_file_promise_drop_types(self)
        QTimer.singleShot(500, lambda: register_file_promise_drop_types(self))
    def dragEnterEvent(self, event):
        if _should_accept_drag(event):
            event.acceptProposedAction()
    def dragMoveEvent(self, event):
        # Required or macOS will show a "not allowed" cursor and dropEvent
        # will never fire, even though dragEnterEvent accepted the drag.
        if _should_accept_drag(event):
            event.acceptProposedAction()
    def dropEvent(self, event):
        handled = resolve_drop_paths(event.mimeData(), tempfile.gettempdir(), self._push_dropped_paths,
                                     lambda msg: _report_drop_error(self, msg))
        if handled:
            event.acceptProposedAction()
    def _push_dropped_paths(self, local_paths):
        if local_paths and self.parent():
            self.parent().execute_tool("ADB", ["push"] + local_paths + [self.current_path])

    # --- Multi-selection -------------------------------------------------------
    def selected_targets(self):
        """Return [(remote_path, is_directory), ...] for all selected items.

        With no selection the current folder itself is the target, which is
        what the existing menu actions did before multi-select existed."""
        if self.selected_names:
            return [(f"{self.current_path}{name}", self.selected_is_dir.get(name, False))
                    for name in self.selected_names]
        return [(self.current_path, True)]

    def selected_paths(self):
        return [path for path, _ in self.selected_targets()]

    def _reset_selection(self):
        self.selected_names = []
        self.selected_is_dir = {}
        self._update_selection_display()

    def _update_selection_display(self):
        count = len(self.selected_names)
        if count == 0:
            text = "Selected: None (actions apply to the current folder)"
        elif count == 1:
            text = f"Selected: {self.selected_names[0]}"
        else:
            text = f"Selected: {count} items"
        self.selected_label.setText(text)
        self.selected_label.setAccessibleName(text)
        for btn in self.item_buttons:
            name = getattr(btn, "_item_name", None)
            selected = name in self.selected_names
            btn.setStyleSheet("background-color: #005599; color: white;" if selected else "")
            state = "Selected." if selected else "Not selected."
            btn.setAccessibleDescription(state + " Control-click or Command-click to add this item to a multi-selection.")

    def _set_single_selection(self, name, is_dir):
        self.selected_names = [name]
        self.selected_is_dir = {name: is_dir}
        self._update_selection_display()

    def _toggle_selection(self, name, is_dir):
        if name in self.selected_names:
            self.selected_names.remove(name)
            self.selected_is_dir.pop(name, None)
        else:
            self.selected_names.append(name)
            self.selected_is_dir[name] = is_dir
        self._update_selection_display()

    def select_all(self):
        if self.mode == "select_dir":
            return
        self.selected_names = list(self.current_items)
        self.selected_is_dir = {name: getattr(btn, "_item_is_dir", False)
                                for btn in self.item_buttons
                                for name in [getattr(btn, "_item_name", None)] if name}
        self._update_selection_display()

    def clear_selection(self):
        self._reset_selection()

    def go_up(self):
        if self.current_path != "/":
            parent = os.path.dirname(self.current_path.rstrip('/'))
            if not parent: 
                parent = "/"
            else: 
                parent += "/"
            self.load_directory(parent)
    def open_menu(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("File Manager Menu")
        dialog.setAccessibleName("File Manager Action Menu")
        layout = QVBoxLayout(dialog)

        targets = self.selected_paths()
        count = len(targets)
        if self.selected_names:
            target_name = ", ".join(self.selected_names)
            if len(target_name) > 90:
                target_name = target_name[:87] + "..."
        else:
            target_name = "Current Folder"

        item_lbl = QLabel(f"Target ({count}): {target_name}")
        item_lbl.setStyleSheet("font-weight: bold;")
        layout.addWidget(item_lbl)

        # Selection controls are here too so a keyboard/screen-reader user can
        # build a multi-selection without needing modifier-key mouse clicks.
        sel_layout = QHBoxLayout()
        btn_all = QPushButton("Select All Items")
        btn_all.clicked.connect(lambda: [self.select_all(), dialog.accept()])
        sel_layout.addWidget(btn_all)
        btn_none = QPushButton("Clear Selection")
        btn_none.clicked.connect(lambda: [self.clear_selection(), dialog.accept()])
        sel_layout.addWidget(btn_none)
        layout.addLayout(sel_layout)

        btn_copy_mac = QPushButton("Copy to Computer")
        btn_copy_mac.clicked.connect(lambda: [dialog.accept(), self.action_pull(targets, move=False)])
        layout.addWidget(btn_copy_mac)
        btn_move_mac = QPushButton("Move to Computer")
        btn_move_mac.clicked.connect(lambda: [dialog.accept(), self.action_pull(targets, move=True)])
        layout.addWidget(btn_move_mac)
        btn_copy_and = QPushButton("Copy file or folder within Android")
        btn_copy_and.clicked.connect(lambda: [dialog.accept(), self.action_copy(targets)])
        layout.addWidget(btn_copy_and)
        btn_move_and = QPushButton("Move file or folder within Android")
        btn_move_and.clicked.connect(lambda: [dialog.accept(), self.action_move(targets)])
        layout.addWidget(btn_move_and)
        del_text = f"Delete selected {'items' if count > 1 else 'item'}"
        btn_delete = QPushButton(del_text)
        btn_delete.setStyleSheet("color: red;")
        btn_delete.clicked.connect(lambda: [dialog.accept(), self.action_delete(targets)])
        layout.addWidget(btn_delete)
        layout.addWidget(QLabel("Global Actions:"))
        btn_push_mac = QPushButton("Push File/Folder from Computer")
        btn_push_mac.clicked.connect(lambda: [dialog.accept(), self.action_push_from_mac()])
        layout.addWidget(btn_push_mac)
        btn_mkdir = QPushButton("Create New Folder Here")
        btn_mkdir.clicked.connect(lambda: [dialog.accept(), self.create_folder()])
        layout.addWidget(btn_mkdir)
        btn_cancel = QPushButton("Close Menu")
        btn_cancel.clicked.connect(dialog.reject)
        layout.addWidget(btn_cancel)
        dialog.exec()
    def action_push_from_mac(self):
        msg = QMessageBox(self)
        msg.setWindowTitle("Push to Device")
        msg.setText("What would you like to push?")
        btn_file = msg.addButton("File(s)", QMessageBox.ButtonRole.ActionRole)
        btn_folder = msg.addButton("Folder", QMessageBox.ButtonRole.ActionRole)
        msg.addButton(QMessageBox.StandardButton.Cancel)
        msg.exec()
        
        paths = []
        if msg.clickedButton() == btn_file:
            files, _ = QFileDialog.getOpenFileNames(self, "Select Files to Push")
            paths = files
        elif msg.clickedButton() == btn_folder:
            folder = QFileDialog.getExistingDirectory(self, "Select Folder to Push")
            if folder: paths = [folder]
            
        if paths and self.parent():
            self.parent().execute_tool("ADB", ["push"] + paths + [self.current_path])
            self.accept()
    def create_folder(self):
        name, ok = QInputDialog.getText(self, "Create Folder", "Enter new folder name:")
        if ok and name.strip():
            new_dir = f"{self.current_path}{name.strip()}"
            cmd = self.adb_cmd + ["shell", "mkdir", shlex.quote(new_dir)]
            subprocess.run(cmd)
            self.load_directory(self.current_path)
    def action_delete(self, targets):
        targets = targets if isinstance(targets, (list, tuple)) else [targets]
        listing = "\n".join(f"  - {p}" for p in targets)
        reply = QMessageBox.warning(self, "Confirm Delete",
                                    f"Are you sure you want to PERMANENTLY delete {len(targets)} item(s)?\n\n{listing}\n\nThis cannot be undone.",
                                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)

        if reply == QMessageBox.StandardButton.Yes:
            for target_path in targets:
                # adb shell joins its arguments and the device shell parses
                # them again, so shlex.quote is correct here.
                subprocess.run(self.adb_cmd + ["shell", "rm", "-rf", shlex.quote(target_path)])
            if self.current_path in targets:
                self.go_up()
            else:
                self._reset_selection()
                self.load_directory(self.current_path)

    def action_pull(self, targets, move=False):
        local_dest = QFileDialog.getExistingDirectory(self, "Select Save Destination")
        if local_dest:
            host = _promise_host(self) or self.parent()
            if host and hasattr(host, "execute_internal_transfer"):
                action = "move_to_mac" if move else "pull"
                target_list = list(targets) if isinstance(targets, (list, tuple)) else [targets]
                host.execute_internal_transfer(action, target_list, local_dest)
            self.accept()

    def action_move(self, targets):
        self._internal_copy_or_move("android_move", targets)

    def action_copy(self, targets):
        self._internal_copy_or_move("android_copy", targets)

    def _internal_copy_or_move(self, action, targets):
        target_list = list(targets) if isinstance(targets, (list, tuple)) else [targets]
        label = os.path.basename(target_list[0].rstrip('/')) or "Current Folder"
        if len(target_list) > 1:
            label += f" and {len(target_list) - 1} more"
        dest, ok = QInputDialog.getText(self, "Destination", f"Enter destination path for {label}:", text=self.current_path)
        if ok and dest.strip():
            host = _promise_host(self) or self.parent()
            if host and hasattr(host, "execute_internal_transfer"):
                host.execute_internal_transfer(action, target_list, dest.strip())
            self.accept()
    def select_current_directory(self):
        self.selected_path = self.current_path
        self.accept()
    def load_directory(self, path):
        self.current_path = path
        self.path_label.setText(f"Current Directory: {self.current_path}")
        self._reset_selection()
        self.current_items.clear()
        self.item_buttons.clear()
        
        for i in reversed(range(self.scroll_layout.count())): 
            widget = self.scroll_layout.itemAt(i).widget()
            if widget:
                widget.setParent(None)
                
        try:
            subprocess.run([self.adb_path, "start-server"], check=False)
            client = adbutils.AdbClient(host="127.0.0.1", port=5037)
            device = client.device(self.serial) if self.serial else client.device()
            
            dir_sizes = {}
            show_sizes = False
            if self.parent() and hasattr(self.parent(), "show_file_sizes"):
                show_sizes = self.parent().show_file_sizes
            if show_sizes:
                try:
                    cmd = ["sh", "-c", f"du -sk {shlex.quote(self.current_path)}*"]
                    du_output = device.shell(cmd)
                    for line in du_output.strip().split('\n'):
                        parts = line.split('\t')
                        if len(parts) >= 2:
                            try:
                                dir_sizes[os.path.basename(parts[1].strip())] = int(parts[0]) * 1024
                            except ValueError:
                                pass
                except Exception:
                    pass
            items = device.sync.list(self.current_path)
            items.sort(key=lambda x: (not stat.S_ISDIR(x.mode), x.path.lower()))
            for item in items:
                name = item.path
                if name in ['.', '..']:
                    continue
                
                is_dir = stat.S_ISDIR(item.mode)
                
                size_str = ""
                if show_sizes:
                    size = dir_sizes.get(name, item.size) if is_dir else item.size
                    if size < 1024: size_str = f"{size} B"
                    elif size < 1024**2: size_str = f"{size/1024:.1f} KB"
                    elif size < 1024**3: size_str = f"{size/1024**2:.1f} MB"
                    else: size_str = f"{size/1024**3:.2f} GB"
                    
                self.current_items.append(name)
                
                display_name = f"{name}/" if is_dir else name
                btn_text = f"{display_name} ({size_str})" if size_str else display_name
                item_remote_path = f"{self.current_path}{name}"
                if is_dir:
                    item_remote_path += "/"
                    
                btn = DraggableItemButton(btn_text, self.adb_cmd, item_remote_path, is_dir)
                btn._item_name = name
                btn._item_is_dir = is_dir
                
                type_str = "Folder" if is_dir else "File"
                acc_name = f"{type_str}: {name}, Size: {size_str}" if size_str else f"{type_str}: {name}"
                btn.setAccessibleName(acc_name)
                btn.setAccessibleDescription("Control-click or Command-click to add this item to a multi-selection.")
                
                if is_dir:
                    btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DirIcon))
                else:
                    btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileIcon))
                
                btn.clicked.connect(lambda checked=False, n=name, d=is_dir, b=btn: self.on_item_clicked(n, d, b))
                
                btn.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
                btn.customContextMenuRequested.connect(lambda pos, n=name, d=is_dir, b=btn: self.on_item_context_menu(n, d, b))
                
                self.scroll_layout.addWidget(btn)
                self.item_buttons.append(btn)
        except Exception as e:
            QMessageBox.warning(self, "Error", f"Could not read directory. Ensure device is connected and authorized.\nError: {e}")
    def on_item_clicked(self, name, is_dir, btn):
        if self.mode == "select_dir":
            if is_dir:
                new_path = f"{self.current_path}{name}/"
                self.load_directory(new_path)
            else:
                QMessageBox.information(self, "Invalid Selection", "You are looking for a directory. Please navigate to the correct folder and click the 'SELECT THIS DIRECTORY' button.")
            return

        modifiers = QApplication.keyboardModifiers()
        multi = bool(modifiers & (Qt.KeyboardModifier.ControlModifier |
                                  Qt.KeyboardModifier.MetaModifier))
        if is_dir and not multi:
            # Preserve the original single-click navigation for folders.
            self.load_directory(f"{self.current_path}{name}/")
            return
        if multi:
            self._toggle_selection(name, is_dir)
        else:
            self._set_single_selection(name, is_dir)

    def on_item_context_menu(self, name, is_dir, btn):
        # Right-clicking an already selected item keeps the whole selection so
        # the menu can act on all of it at once.
        if name not in self.selected_names:
            self._set_single_selection(name, is_dir)
        else:
            self._update_selection_display()
        self.open_menu()
class ADBClient(QMainWindow):
    def __init__(self):
        super().__init__()
        
        self.setAcceptDrops(True)
        
        self.settings = QSettings("DevTools", "ADBAccessibleClient")
        self.adb_path = self.settings.value("adb_path", "")
        self.fastboot_path = self.settings.value("fastboot_path", "")
        self.save_dir = self.settings.value("save_dir", "")
        
        self.announce_terminal = self.settings.value("announce_terminal", True, type=bool)
        self.announce_transfers = self.settings.value("announce_transfers", True, type=bool)
        self.skip_command_announce = self.settings.value("skip_command_announce", True, type=bool)
        self.read_final_only = self.settings.value("read_final_only", True, type=bool)
        self.show_file_sizes = self.settings.value("show_file_sizes", False, type=bool)
        
        self.is_file_transfer = False
        self.current_percent = 0
        self.last_announced_percent = 0
        self.command_output_buffer = ""
        self.default_android_dir = self.settings.value("default_android_dir", "")
        self.current_target_serial = None
        self._promise_registration_logged = False
        
        self.setWindowTitle("ADB and Fastboot Tool")
        self.setAccessibleName("ADB and Fastboot Main Window")
        
        self.process = QProcess(self)
        self.process.readyReadStandardOutput.connect(self.handle_stdout)
        self.process.readyReadStandardError.connect(self.handle_stderr)
        self.process.finished.connect(self.handle_finished)
        self.transfer_thread = None
        
        # Bridge for receiving thread-safe callbacks from AppKit's file
        # promise machinery (see AdbPromiseDelegate / _PromiseBridge above).
        self.promise_bridge = _PromiseBridge()
        self.promise_bridge.pull_requested.connect(self._handle_promise_pull)
        self.promise_bridge.error_logged.connect(self._log_promise_error)
        # Finder can deliver one writePromise callback per dragged item at
        # almost the same instant. Only one transfer can run at a time, so the
        # rest wait here instead of being failed with "another transfer is
        # already running".
        self._promise_queue = []
        
        self.setup_ui()
        QTimer.singleShot(500, self.check_configuration)
        QTimer.singleShot(1500, self.check_promise_support)
        if os.environ.get("ADB_A11Y_DEBUG"):
            QTimer.singleShot(2500, self.dump_accessibility_tree)
    def get_current_serial(self):
        return self.current_target_serial
    def log_error_from_thread(self, message):
        """Safe to call from ANY thread (including AppKit's background
        promise-writing queue). Errors from that code used to go to
        print(), which is invisible once the app is packaged - nothing
        the person running it could ever see. Routing through this signal
        guarantees it lands in the visible terminal log."""
        try:
            self.promise_bridge.error_logged.emit(str(message))
        except Exception:
            print(message)
    def _log_promise_error(self, message):
        self.log(f"[File Promise] {message}")
    def showEvent(self, event):
        super().showEvent(event)
        # Qt only registers its native view for the drag types it understands.
        # Add the native file promise types, and re-apply once shortly after in
        # case Qt re-registers its own types during window setup.
        QTimer.singleShot(0, self._register_promise_drop_types)
        QTimer.singleShot(2000, self._register_promise_drop_types)
    def _register_promise_drop_types(self):
        try:
            ok, detail = register_file_promise_drop_types(self)
            if sys.platform == "darwin" and not self._promise_registration_logged:
                self._promise_registration_logged = True
                state = "OK" if ok else "FAILED"
                self.log(f"macOS file promise drop registration: {state} ({detail}).", skip_announce=True)
        except Exception:
            pass
    def check_promise_support(self):
        """One-time, visible diagnostic: on macOS, tell the person plainly
        whether native drag-out (file promise) support actually loaded,
        instead of silently falling back to the much slower/less reliable
        QDrag path with no explanation."""
        if sys.platform != "darwin":
            return
        if PYOBJC_AVAILABLE:
            receiver = "available" if PYOBJC_PROMISE_RECEIVER_AVAILABLE else "NOT available"
            self.log(f"macOS file promise support: drag-out available; drag-in {receiver}.",
                     skip_announce=True)
        else:
            self.log("macOS file promise support: NOT available. Falling back to a slower, "
                     "less reliable drag method - large drags may fail or appear stuck. "
                     "Install the required package with: pip install pyobjc-framework-Cocoa", skip_announce=True)
    def dump_accessibility_tree(self):
        """Debug aid (only runs when launched with ADB_A11Y_DEBUG=1): writes the
        roles Qt exposes to the OS accessibility layer for this window into the
        Terminal Output log, WITHOUT announcing them. If VoiceOver says 'group'
        for something that shows up here as PushButton, the problem is in Qt's
        macOS bridge rather than in this app's widget structure."""
        if not QT_ACCESSIBILITY_AVAILABLE:
            self.log_output.append("[A11y debug] QAccessible is not available.")
            return
        try:
            lines = ["[A11y debug] Qt accessibility tree (role | name):"]

            def walk(iface, depth):
                if iface is None or depth > 12:
                    return
                try:
                    role = iface.role().name
                except Exception:
                    role = str(iface.role())
                try:
                    name = iface.text(QAccessible.Text.Name)
                except Exception:
                    name = ""
                lines.append(f"{'  ' * depth}{role} | {name}")
                for i in range(iface.childCount()):
                    walk(iface.child(i), depth + 1)

            walk(QAccessible.queryAccessibleInterface(self), 0)
            self.log_output.append("\n".join(lines))
        except Exception as e:
            self.log_output.append(f"[A11y debug] Could not dump accessibility tree: {e}")
    def open_device_picker(self):
        dialog = DeviceSelectionDialog(self.adb_path, self.current_target_serial, self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.current_target_serial = dialog.selected_serial
            display_name = self.current_target_serial if self.current_target_serial else "Default / Any"
            self.target_dev_label.setText(f"Target Device: {display_name}")
            self.target_dev_label.setAccessibleName(f"Current Target Device: {display_name}")
    def dragEnterEvent(self, event):
        if _should_accept_drag(event):
            event.acceptProposedAction()
    def dragMoveEvent(self, event):
        # Required or macOS will show a "not allowed" cursor and dropEvent
        # will never fire, even though dragEnterEvent accepted the drag.
        if _should_accept_drag(event):
            event.acceptProposedAction()
    def dropEvent(self, event):
        handled = resolve_drop_paths(event.mimeData(), tempfile.gettempdir(), self._push_dropped_paths_default,
                                     lambda msg: _report_drop_error(self, msg))
        if handled:
            event.acceptProposedAction()
    def _push_dropped_paths_default(self, local_paths):
        if local_paths:
            self.execute_tool("ADB", ["push"] + local_paths + [self.default_android_dir])
    def _handle_promise_pull(self, remote_path, dest_path, handler, progress):
        """Runs on the main thread (queued from AdbPromiseDelegate via
        promise_bridge) to fulfill a macOS file-promise drag by pulling the
        requested file/folder off the device to the destination Finder
        has already allocated for us. `progress` is an NSProgress that
        Finder watches, so it can show a real percentage on large/slow
        transfers instead of a static "Preparing..." spinner."""
        if self.process.state() != QProcess.ProcessState.NotRunning or (self.transfer_thread and self.transfer_thread.isRunning()):
            self._promise_queue.append((remote_path, dest_path, handler, progress))
            self.log(f"Drag-out queued: {os.path.basename(remote_path.rstrip('/'))}", skip_announce=True)
            return

        def on_progress(percent, mb_sec, mb_trans, filename):
            if progress is not None:
                try:
                    progress.setCompletedUnitCount_(min(100, max(0, int(percent))))
                except Exception:
                    pass

        completed = {"value": False}

        def on_complete(success, message):
            if completed["value"]:
                return
            completed["value"] = True
            if progress is not None:
                try:
                    progress.setCompletedUnitCount_(100)
                except Exception:
                    pass
            if success:
                self.log(f"Drag-out to Finder completed: {os.path.basename(dest_path)}", skip_announce=True)
                self._call_promise_handler(handler, None)
            else:
                # Log the FULL detail visibly in-app (the NSError message
                # shown by Finder itself is often just a generic "The
                # operation could not be completed" with no real detail).
                self.log(f"Drag-out to Finder FAILED for {remote_path}:\n{message}")
                self._call_promise_handler(handler, str(message)[:200])
            # Defer: finished_transfer is emitted from run() before QThread
            # actually stops, so starting the next one inline would look like
            # "still busy" and leave the queue stranded.
            QTimer.singleShot(0, self._drain_promise_queue)

        # Connect the callbacks BEFORE the thread starts. The old code started
        # the thread first and connected afterwards, so a fast transfer could
        # finish before on_complete was attached and Finder's promise was never
        # completed (it just spun forever).
        thread = self.execute_internal_transfer(
            "pull", remote_path, dest_path,
            on_progress=on_progress, on_finished=on_complete
        )
        if thread is None:
            self.log(f"Drag-out to Finder FAILED: could not start a transfer thread for {remote_path}.")
            self._call_promise_handler(handler, "Could not start transfer.")
            QTimer.singleShot(0, self._drain_promise_queue)
    def _drain_promise_queue(self):
        """Start the next queued Finder drag-out once the GUI thread is idle."""
        if not self._promise_queue:
            return
        if self.process.state() != QProcess.ProcessState.NotRunning or (self.transfer_thread and self.transfer_thread.isRunning()):
            QTimer.singleShot(200, self._drain_promise_queue)
            return
        item = self._promise_queue.pop(0)
        self._handle_promise_pull(*item)

    def _call_promise_handler(self, handler, error_message):
        if handler is None:
            return
        try:
            if error_message and PYOBJC_AVAILABLE:
                err = NSError.errorWithDomain_code_userInfo_(
                    "com.devtools.adbclient", 1, {"NSLocalizedDescriptionKey": error_message}
                )
                handler(err)
            else:
                handler(None)
        except Exception as e:
            self.log(f"[File Promise] Completion Error: {e}")
            try:
                handler(None)
            except Exception:
                pass
    def announce(self, message):
        if not message.strip():
            return
            
        if QT_ACCESSIBILITY_AVAILABLE:
            self.log_output.setAccessibleDescription(message.strip())
            QAccessible.updateAccessibility(QAccessibleEvent(self.log_output, QAccessible.Event.Alert))
    def _section_heading(self, text):
        """A plain text heading used instead of a QGroupBox. QGroupBox (and
        any wrapper container widget) shows up to VoiceOver as an AXGroup,
        which has to be 'interacted with' before the controls inside it can
        be reached. A QLabel is just text, so the controls stay directly on
        the page."""
        label = QLabel(text)
        label.setStyleSheet(
            "font-weight: bold; font-size: 14px; margin-top: 10px; "
            "padding-bottom: 3px; border-bottom: 1px solid #666666;"
        )
        return label
    def setup_ui(self):
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout()
        main_layout.setContentsMargins(15, 15, 15, 15)
        central_widget.setLayout(main_layout)

        # Everything below is added straight to main_layout. No QGroupBox or
        # wrapper QWidget containers, so the accessibility tree stays flat:
        # window -> content -> headings, buttons, fields.

        # Configuration
        main_layout.addWidget(self._section_heading("Configuration"))
        prefs_layout = QHBoxLayout()
        self.prefs_btn = QPushButton("Preferences")
        self.prefs_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileDialogListView))
        self.prefs_btn.setAccessibleName("Preferences")
        self.prefs_btn.clicked.connect(self.open_preferences)
        prefs_layout.addStretch()
        prefs_layout.addWidget(self.prefs_btn)
        main_layout.addLayout(prefs_layout)

        # Device Connection
        main_layout.addWidget(self._section_heading("Device Connection"))
        dev_inner_layout = QHBoxLayout()
        self.target_dev_label = QLabel("Target Device: Default / Any")
        self.target_dev_label.setAccessibleName("Current Target Device: Default or Any")
        
        self.choose_dev_btn = QPushButton("Device Manager")
        self.choose_dev_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ComputerIcon))
        self.choose_dev_btn.setAccessibleName("Device Manager")
        self.choose_dev_btn.clicked.connect(self.open_device_picker)
        
        dev_inner_layout.addWidget(self.target_dev_label)
        dev_inner_layout.addWidget(self.choose_dev_btn)
        dev_inner_layout.addStretch()
        main_layout.addLayout(dev_inner_layout)

        # File Management
        main_layout.addWidget(self._section_heading("File Management"))
        transfer_label = QLabel("File Transfers (Or Drag and Drop file here):")
        self.wizard_btn = QPushButton("Open File Manager")
        self.wizard_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_DirHomeIcon))
        self.wizard_btn.setAccessibleName("Open File Manager")
        self.wizard_btn.setAccessibleDescription("Click to open the file manager for pushing, pulling, moving, or deleting files.")
        self.wizard_btn.clicked.connect(self.start_transfer_wizard)
        
        main_layout.addWidget(transfer_label)
        main_layout.addWidget(self.wizard_btn)

        # Command Terminal
        main_layout.addWidget(self._section_heading("Command Terminal"))
        cmd_layout = QHBoxLayout()
        self.adb_radio = QRadioButton("ADB")
        self.adb_radio.setChecked(True)
        self.adb_radio.setAccessibleName("Use ADB Tool")
        
        self.fastboot_radio = QRadioButton("Fastboot")
        self.fastboot_radio.setAccessibleName("Use Fastboot Tool")
        self.cmd_input = TerminalLineEdit()
        self.cmd_input.setAccessibleName("Command Input")
        self.cmd_input.setAccessibleDescription("Type raw arguments here. Do not include 'adb' or 'fastboot'. Press Enter to run.")
        self.cmd_input.returnPressed.connect(self.run_command)
        self.insert_path_btn = QPushButton("Insert File Path")
        self.insert_path_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileDialogStart))
        self.insert_path_btn.setAccessibleName("Insert File Path Into Command")
        self.insert_path_btn.setAccessibleDescription("Opens a file picker and inserts the chosen path into the command field, as an alternative to dragging and dropping.")
        self.insert_path_btn.clicked.connect(self.insert_file_path_into_terminal)
        self.stop_btn = QPushButton("Stop Command")
        self.stop_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_BrowserStop))
        self.stop_btn.setAccessibleName("Stop Running Command")
        self.stop_btn.setEnabled(False)
        self.stop_btn.clicked.connect(self.stop_command)
        cmd_layout.addWidget(self.adb_radio)
        cmd_layout.addWidget(self.fastboot_radio)
        cmd_layout.addWidget(self.cmd_input)
        cmd_layout.addWidget(self.insert_path_btn)
        cmd_layout.addWidget(self.stop_btn)
        main_layout.addLayout(cmd_layout)

        # Terminal Output & Status
        main_layout.addWidget(self._section_heading("Terminal Output & Status"))
        header_layout = QHBoxLayout()
        
        self.status_label = QLabel("Status: Idle")
        self.status_label.setAccessibleName("Status: Idle")
        self.status_label.setStyleSheet("font-weight: bold; color: #0078D7; font-size: 14px;")
        
        self.clear_btn = QPushButton("Clear Terminal")
        self.clear_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_TrashIcon))
        self.clear_btn.setAccessibleName("Clear Terminal Output")
        self.clear_btn.clicked.connect(self.clear_log)
        
        header_layout.addWidget(self.status_label)
        header_layout.addStretch()
        header_layout.addWidget(self.clear_btn)
        main_layout.addLayout(header_layout)
        
        self.pct_label = QLabel("Overall Progress: 0%")
        self.pct_label.setAccessibleName("Overall Progress: 0 percent")
        self.pct_label.setStyleSheet("font-weight: bold; font-size: 14px;")
        
        self.speed_label = QLabel("Speed: 0.00 MB/s (0.00 MB transferred)")
        self.speed_label.setAccessibleName("Speed: 0 Megabytes per second")
        
        self.file_label = QLabel("Current File: None")
        self.file_label.setAccessibleName("Current File: None")
        
        main_layout.addWidget(self.pct_label)
        main_layout.addWidget(self.speed_label)
        main_layout.addWidget(self.file_label)
        
        # Same show()/hide() behavior as the old stats container widget, but
        # without an extra container (group) in the accessibility tree.
        self.stats_container = _VisibilityGroup([self.pct_label, self.speed_label, self.file_label])
        self.stats_container.hide()
        
        self.log_output = QTextEdit()
        self.log_output.setReadOnly(True)
        self.log_output.setAccessibleName("Terminal Output Log")
        
        self.log_output.setStyleSheet("""
            QTextEdit {
                background-color: #121212;
                color: #00FF00;
                font-family: 'Courier New', Courier, monospace;
                font-size: 13px;
                border: 1px solid #333333;
            }
        """)
        
        main_layout.addWidget(self.log_output)
        
        self.update_live_region_settings()
    def insert_file_path_into_terminal(self):
        paths, _ = QFileDialog.getOpenFileNames(self, "Select File(s) to Insert")
        if paths:
            current = self.cmd_input.text()
            paths_str = " ".join(shlex.quote(p) for p in paths)
            self.cmd_input.setText(f"{current} {paths_str}".strip())
            self.cmd_input.setFocus()
    def update_live_region_settings(self):
        if self.announce_terminal:
            self.log_output.setProperty("container-live", "polite")
            self.log_output.setProperty("live", "polite")
        else:
            self.log_output.setProperty("container-live", "none")
            self.log_output.setProperty("live", "none")
    def check_configuration(self):
        if not self.adb_path or not os.path.exists(self.adb_path):
            QMessageBox.information(self, "Setup Required", "Please locate your ADB executable.")
            path, _ = QFileDialog.getOpenFileName(self, "Select ADB Executable")
            if path:
                self.adb_path = path
                self.settings.setValue("adb_path", self.adb_path)
                self.log(f"ADB path configured to: {self.adb_path}")
        
        if not self.fastboot_path or not os.path.exists(self.fastboot_path):
            QMessageBox.information(self, "Setup Required", "Please locate your Fastboot executable. You can cancel if you don't use Fastboot.")
            path, _ = QFileDialog.getOpenFileName(self, "Select Fastboot Executable")
            if path:
                self.fastboot_path = path
                self.settings.setValue("fastboot_path", self.fastboot_path)
                self.log(f"Fastboot path configured to: {self.fastboot_path}")
        if not self.save_dir or not os.path.exists(self.save_dir):
            QMessageBox.information(self, "Setup Required", "Where would you like to save files generated by the terminal (like saved logs)?")
            path = QFileDialog.getExistingDirectory(self, "Select Terminal Save Directory")
            if path:
                self.save_dir = path
                self.settings.setValue("save_dir", self.save_dir)
                self.log(f"Save directory configured to: {self.save_dir}")
            else:
                self.save_dir = os.path.expanduser("~")
                self.settings.setValue("save_dir", self.save_dir)
                self.log(f"Defaulting save directory to Home folder: {self.save_dir}")
        if not self.default_android_dir:
            QMessageBox.information(self, "Setup Required", "Please make sure your Android phone is plugged in and authorized.\n\nWe will now browse your Android device to set your default start directory.")
            serial = self.get_current_serial()
            dialog = AccessibleAndroidBrowser(self.adb_path, serial=serial, mode="select_dir", start_path="/sdcard/", parent=self)
            if dialog.exec() == QDialog.DialogCode.Accepted and dialog.selected_path:
                self.default_android_dir = dialog.selected_path
                self.settings.setValue("default_android_dir", self.default_android_dir)
                self.log(f"Default Android directory configured to: {self.default_android_dir}")
            else:
                self.default_android_dir = "/sdcard/"
                self.settings.setValue("default_android_dir", self.default_android_dir)
                self.log(f"Defaulting Android directory to: {self.default_android_dir}")
        last_version = self.settings.value("last_version", "")
        if last_version != APP_VERSION:
            self.show_welcome_dialog()
            self.settings.setValue("last_version", APP_VERSION)
    def show_welcome_dialog(self):
        msg = QMessageBox(self)
        msg.setWindowTitle("New Updates")
        msg.setIcon(QMessageBox.Icon.Information)
        msg.setText(f"Welcome to version {APP_VERSION}!\n\n"
                    "What's New:\n"
                    "- Multi-select in the File Manager: Control/Command-click items or use Select All, then Copy, Move, Delete, or drag them together.\n"
                    "- macOS File Promise drag-and-drop fixes for both dragging files out to Finder and dropping promised files into the app.\n"
                    "- Main window accessibility: removed the section boxes and hidden container that VoiceOver treated as groups. Section titles are now plain headings and every control sits directly on the page.\n"
                    "- Fixed multi-file drops of native macOS File Promises, and failed promise drops now report an error in the Terminal Output log.\n"
                    "- The window now registers for native file promise drag types, which Qt does not do on its own.\n"
                    "- Fixed the cause of large drag-out failures: the fallback drag path was buffering progress text in a never-trimmed string for the whole transfer, which crawled to a halt on big files.\n"
                    "- Outgoing macOS File Promises now show a real progress percentage in Finder on large/slow transfers.\n"
                    "- File-promise and drag errors now show up in the Terminal Output log so they're actually visible, instead of vanishing into an invisible console print.\n"
                    "- Startup now reports whether native macOS drag-out support loaded correctly.\n"
                    "- Fixed drag-and-drop being rejected mid-drag (a missing dragMoveEvent handler was the cause of Finder drags not registering).\n"
                    "- Fixed a thread-safety bug in outgoing macOS File Promises that could hang or crash the app.\n"
                    "- Outgoing File Promises now correctly support dragging whole folders out to Finder.\n"
                    "- Added support for receiving native File Promises dropped in from apps like Photos, Mail, or Safari.\n"
                    "- Added an 'Insert File Path' button as a non-drag alternative for keyboard and screen-reader users.\n"
                    "- Progress indicators now automatically hide when idle for privacy.\n"
                    "- Redesigned Android Browser: Removed intrusive pop-ups. Replaced with dedicated Menu button and active item selection.\n"
                    "- Recalibrated file tracker using absolute byte cursors to strictly prevent >100% bugs.\n"
                    "- Refactored Global UI actions directly into the master Action Menu.")
        msg.exec()
    def open_preferences(self):
        dialog = PreferencesDialog(self)
        dialog.exec()
    def start_transfer_wizard(self):
        serial = self.get_current_serial()
        dialog = AccessibleAndroidBrowser(self.adb_path, serial=serial, mode="browse", start_path=self.default_android_dir, parent=self)
        dialog.exec()
    def run_command(self):
        cmd_text = self.cmd_input.text().strip()
        if not cmd_text:
            return
            
        selected_tool = "ADB" if self.adb_radio.isChecked() else "Fastboot"
        
        try:
            args = shlex.split(cmd_text)
        except ValueError as e:
            self.log(f"Error parsing command syntax: {e}")
            return
            
        self.execute_tool(selected_tool, args)
        self.cmd_input.clear()
    def execute_internal_transfer(self, action, src, dest, on_progress=None, on_finished=None):
        """Start an internal transfer. `src` may be a single path or a list of
        paths (multi-selection in the file manager). The optional callbacks are
        connected before the thread starts so fast transfers cannot finish
        before a caller (e.g. a macOS file promise) is listening."""
        if self.process.state() != QProcess.ProcessState.NotRunning or (self.transfer_thread and self.transfer_thread.isRunning()):
            self.log("A process is already running. Please wait or stop it first.")
            return None
        src_list = list(src) if isinstance(src, (list, tuple)) else [src]
        if not src_list:
            return None
        self.is_file_transfer = True
        self.current_percent = 0
        self.last_announced_percent = 0
        self.status_label.setText("Status: Transfer Started")
        self.status_label.setAccessibleName("Status: Transfer Started")
        self.pct_label.setText("Overall Progress: 0%")
        self.speed_label.setText("Speed: Calculating...")
        self.file_label.setText("Current File: Initiating...")
        
        self.stats_container.show()
        
        if self.announce_transfers:
            self.announce(f"{action.replace('_', ' ').capitalize()} started.")
        self.log(f"\nInitiating {action} for: {', '.join(src_list)}", skip_announce=True)
        
        self.stop_btn.setEnabled(True)
        self.wizard_btn.setEnabled(False)
        self.transfer_thread = AdbTransferThread(self.adb_path, self.get_current_serial(), action, src_list, dest)
        self.transfer_thread.progress_update.connect(self.handle_thread_progress)
        self.transfer_thread.finished_transfer.connect(self.handle_thread_finished)
        if on_progress is not None:
            self.transfer_thread.progress_update.connect(on_progress)
        if on_finished is not None:
            self.transfer_thread.finished_transfer.connect(on_finished)
        self.transfer_thread.start()
        return self.transfer_thread
    def execute_tool(self, tool_name, args):
        if self.process.state() != QProcess.ProcessState.NotRunning or (self.transfer_thread and self.transfer_thread.isRunning()):
            self.log("A process is already running. Please wait or stop it first.")
            return
        exe_path = self.adb_path if tool_name == "ADB" else self.fastboot_path
        
        if not exe_path or not os.path.exists(exe_path):
            self.log(f"Error: {tool_name} executable path is missing or invalid.")
            return
        modified_args = list(args)
        
        if tool_name == "ADB":
            serial = self.get_current_serial()
            if serial:
                modified_args = ["-s", serial] + modified_args
        
        self.command_output_buffer = "" 
        
        if tool_name == "ADB" and any(action in args for action in ["push", "pull"]):
            self.is_file_transfer = True
            
            action_type = "push" if "push" in args else "pull"
            idx = args.index(action_type)
            if idx + 2 > len(args):
                self.log("Error: Invalid push/pull arguments. Source and destination required.")
                return
            src_list = args[idx + 1:-1]
            dest = args[-1]
            
            self.current_percent = 0
            self.last_announced_percent = 0
            
            self.status_label.setText("Status: File Transfer Started")
            self.status_label.setAccessibleName("Status: File Transfer Started")
            self.pct_label.setText("Overall Progress: 0%")
            self.speed_label.setText("Speed: Calculating...")
            self.file_label.setText("Current File: Initiating...")
            
            self.stats_container.show()
            
            if self.announce_transfers:
                self.announce("File transfer started.")
            self.log(f"\nInitiating direct daemon {action_type}...", skip_announce=True)
            
            self.stop_btn.setEnabled(True)
            self.wizard_btn.setEnabled(False)
            self.transfer_thread = AdbTransferThread(exe_path, self.get_current_serial(), action_type, src_list, dest)
            self.transfer_thread.progress_update.connect(self.handle_thread_progress)
            self.transfer_thread.finished_transfer.connect(self.handle_thread_finished)
            self.transfer_thread.start()
        else:
            self.is_file_transfer = False
            status_text = f"Status: Executing {tool_name} command..."
            self.status_label.setText(status_text)
            self.status_label.setAccessibleName(status_text)
            self.pct_label.setText("Overall Progress: 0%")
            self.speed_label.setText("Speed: 0.00 MB/s (0.00 MB transferred)")
            self.file_label.setText("Current File: None")
            
            self.stats_container.show()
            
            full_cmd_str = f"{exe_path} {' '.join(modified_args)}"
            
            self.log(f"\nExecuting: {full_cmd_str}", skip_announce=True)
            
            if self.save_dir and os.path.exists(self.save_dir):
                self.process.setWorkingDirectory(self.save_dir)
            self.stop_btn.setEnabled(True)
            self.wizard_btn.setEnabled(False)
            
            self.process.setProgram(exe_path)
            self.process.setArguments(modified_args)
            self.process.start()
    def handle_thread_progress(self, percent, mb_sec, mb_trans, filename):
        if percent > self.current_percent or percent == 100:
            self.current_percent = percent
            
            self.pct_label.setText(f"Overall Progress: {percent}%")
            self.pct_label.setAccessibleName(f"Overall Progress: {percent} percent")
            
            self.file_label.setText(f"Current File: {filename}")
            self.file_label.setAccessibleName(f"Current File: {filename}")
            speed_text = f"Speed: {mb_sec:.2f} MB/s ({mb_trans:.2f} MB transferred)"
            self.speed_label.setText(speed_text)
            self.speed_label.setAccessibleName(f"Speed: {mb_sec:.2f} Megabytes per second")
            
            if QT_ACCESSIBILITY_AVAILABLE:
                QAccessible.updateAccessibility(QAccessibleEvent(self.pct_label, QAccessible.Event.NameChanged))
            
            if self.announce_transfers:
                if percent >= self.last_announced_percent + 10 and percent < 100:
                    self.announce(f"{percent} percent")
                    self.last_announced_percent = percent
    def hide_stats_if_idle(self):
        if self.process.state() == QProcess.ProcessState.NotRunning and not (self.transfer_thread and self.transfer_thread.isRunning()):
            self.stats_container.hide()
            self.pct_label.setText("Overall Progress: 0%")
            self.speed_label.setText("Speed: 0.00 MB/s (0.00 MB transferred)")
            self.file_label.setText("Current File: None")
            self.status_label.setText("Status: Idle")
            self.status_label.setAccessibleName("Status: Idle")
    def handle_thread_finished(self, success, message):
        self.stop_btn.setEnabled(False)
        self.wizard_btn.setEnabled(True)
        if success:
            self.pct_label.setText("Overall Progress: 100%")
            self.pct_label.setAccessibleName("Overall Progress: 100 percent")
            self.file_label.setText("Current File: Complete")
            
            self.status_label.setText("Status: File Transfer Completed Successfully")
            self.status_label.setAccessibleName("Status: File Transfer Completed Successfully")
            
            if self.announce_transfers:
                self.announce("File transfer completed successfully.")
            self.log("--- File Transfer Completed Successfully ---")
        else:
            self.status_label.setText("Status: File Transfer Failed/Cancelled")
            self.status_label.setAccessibleName("Status: File Transfer Failed or Cancelled")
            
            if self.announce_transfers:
                self.announce("File transfer failed or was cancelled.")
            self.log(f"--- Transfer Error:\n{message}\n---")
            
        QTimer.singleShot(5000, self.hide_stats_if_idle)
    def stop_command(self):
        if self.process.state() != QProcess.ProcessState.NotRunning:
            self.log("Stopping process...")
            self.status_label.setText("Status: Stopping Process...")
            self.status_label.setAccessibleName("Status: Stopping Process")
            self.process.kill()
            
        if self.transfer_thread and self.transfer_thread.isRunning():
            self.log("Cancelling file transfer...")
            self.status_label.setText("Status: Cancelling Transfer...")
            self.status_label.setAccessibleName("Status: Cancelling Transfer")
            self.transfer_thread.cancel()
    def handle_stdout(self):
        raw_bytes = self.process.readAllStandardOutput().data()
        text_chunk = raw_bytes.decode('utf-8', errors='ignore')
        if not text_chunk:
            return
        self.command_output_buffer += text_chunk
        self.log(text_chunk)
    def handle_stderr(self):
        raw_bytes = self.process.readAllStandardError().data()
        text_chunk = raw_bytes.decode('utf-8', errors='ignore')
        if not text_chunk:
            return
        self.command_output_buffer += text_chunk
        self.log(text_chunk)
    def handle_finished(self):
        self.pct_label.setText("Overall Progress: 100%")
        self.status_label.setText("Status: Command Finished")
        self.status_label.setAccessibleName("Status: Command Finished")
        self.log("--- Process Finished ---")
        
        if getattr(self, 'read_final_only', False) and self.command_output_buffer.strip():
            self.announce("Command Finished. Output: " + self.command_output_buffer.strip())
            
        self.stop_btn.setEnabled(False)
        self.wizard_btn.setEnabled(True)
        
        QTimer.singleShot(5000, self.hide_stats_if_idle)
    def clear_log(self):
        self.log_output.clear()
    def log(self, message, skip_announce=False):
        self.log_output.append(message.strip())
        
        if not self.announce_terminal or not message.strip():
            return
            
        if skip_announce and self.skip_command_announce:
            return
            
        if getattr(self, 'read_final_only', False) and getattr(self, 'process', None) and self.process.state() != QProcess.ProcessState.NotRunning:
            return
            
        self.announce(message.strip())
if __name__ == "__main__":
    os.environ["QT_ACCESSIBILITY"] = "1"
    
    app = QApplication(sys.argv)
    window = ADBClient()
    window.show()
    
    window.raise_()
    window.activateWindow()
    

    sys.exit(app.exec())
