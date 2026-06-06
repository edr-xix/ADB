import sys
import os
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
                             QCheckBox) 
from PyQt6.QtCore import QSettings, QTimer, QProcess, Qt, QMimeData, QUrl, QThread, pyqtSignal
from PyQt6.QtGui import QDrag

try:
    from PyQt6.QtGui import QAccessible, QAccessibleEvent
    QT_ACCESSIBILITY_AVAILABLE = True
except ImportError:
    QT_ACCESSIBILITY_AVAILABLE = False

try:
    import objc
    from AppKit import NSObject, NSFilePromiseProvider, NSDraggingItem, NSImage, NSSize, NSApp, NSDragOperationCopy
    from Foundation import NSURL
    PYOBJC_AVAILABLE = True
except ImportError:
    PYOBJC_AVAILABLE = False

if sys.platform == "darwin" and PYOBJC_AVAILABLE:
    class AdbPromiseDelegate(NSObject):
        adb_cmd = objc.ivar()
        remote_path = objc.ivar()
        file_name = objc.ivar()
        main_window = objc.ivar()
        
        def filePromiseProvider_fileTypeForURL_(self, provider, url):
            return "public.data"
            
        def filePromiseProvider_fileNameForType_(self, provider, fileType):
            return self.file_name
            
        def filePromiseProvider_writePromiseToURL_completionHandler_(self, provider, url, handler):
            try:
                dest_path = url.path()
                if self.main_window:
                    # Bridge the PyObjC drop completion back to the PyQt main event loop for active tracking
                    QTimer.singleShot(0, lambda: self.main_window.execute_internal_transfer("pull", self.remote_path, dest_path))
            except Exception as e:
                print(f"File Promise Error: {e}")
            finally:
                if handler:
                    handler(None)
                
        def draggingSession_sourceOperationMaskForDraggingContext_(self, session, context):
            return NSDragOperationCopy

APP_VERSION = "0.0.12-beta-V2"

class TrackedFile:
    """Wraps a local file object and calculates exact delta cursor movements."""
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
                src = self.src_list[0].replace('//', '/') if self.src_list[0].startswith('//') else self.src_list[0]
                dest = self.dest
                
                fi = device.sync.stat(src)
                if fi.mode == 0:
                    raise Exception(f"Source not found: {src}")
                
                if self.action == "android_copy":
                    if stat.S_ISDIR(fi.mode):
                        res = device.shell(["du", "-sk", src])
                        match = re.search(r'^(\d+)', res.strip())
                        if match:
                            total_bytes = int(match.group(1)) * 1024
                    else:
                        total_bytes = fi.size
                        
                start_time = time.time()
                fname = os.path.basename(src)
                
                if self.action == "android_move":
                    device.shell(["mv", src, dest])
                    self.progress_update.emit(100, 0, 0, fname)
                else:
                    cmd_list = [self.adb_path]
                    if self.serial:
                        cmd_list.extend(["-s", self.serial])
                    cmd_list.extend(["shell", "cp", "-a", src, dest])
                    
                    proc = subprocess.Popen(cmd_list)
                    dest_path = f"{dest.rstrip('/')}/{fname}" if device.sync.stat(dest).mode & stat.S_IFDIR else dest
                    
                    while proc.poll() is None:
                        if self.is_cancelled:
                            proc.kill()
                            raise InterruptedError("Cancelled")
                        
                        try:
                            fi_dest = device.sync.stat(dest_path)
                            if stat.S_ISDIR(fi_dest.mode):
                                res = device.shell(["du", "-sk", dest_path])
                                match = re.search(r'^(\d+)', res.strip())
                                if match:
                                    current_bytes = int(match.group(1)) * 1024
                                else:
                                    current_bytes = 0
                            else:
                                current_bytes = fi_dest.size
                            
                            percent = int((current_bytes / total_bytes) * 100) if total_bytes > 0 else 0
                            percent = min(100, percent)
                            elapsed = time.time() - start_time
                            mb_trans = current_bytes / (1024 * 1024)
                            mb_sec = mb_trans / elapsed if elapsed > 0 else 0
                            
                            self.progress_update.emit(percent, mb_sec, mb_trans, fname)
                        except Exception:
                            pass
                        time.sleep(1)
                        
                    if proc.returncode != 0:
                        raise Exception("Internal copy failed.")
                
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
        self.announce_transfers_checkbox.setAccessibleDescription("When enabled, VoiceOver will dynamically read percentage updates during file transfers.")
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
                        "- Added toggle to disable file size calculation for faster File Manager loading.\n"
                        "- Added dynamic 'Stop Speech' button for VoiceOver interruptions.\n"
                        "- Progress indicators now auto-hide when idle to improve privacy.\n"
                        "- Relabeled Device Manager and Preferences for cleaner screen reader navigation.\n"
                        "- Redesigned Android Browser: Removed intrusive pop-ups. Replaced with dedicated Menu button and active item selection.\n"
                        "- Repaired PyObjC memory pointer bugs to natively fulfill File Promises without temp files.\n"
                        "- Recalibrated file tracker using absolute byte cursors to prevent >100% bugs.\n"
                        "- Rebuilt bidirectional dragging; you can drag native Mac files directly onto the browser window to push them to the active directory.\n"
                        "- Testing beta accessibility features.")
        rn_text.setMaximumHeight(100)
        rn_text.setStyleSheet("background-color: #1e1e1e; color: #d4d4d4;")
        layout.addWidget(rn_text)

        version_label = QLabel(f"Developers: Elwin Rivera and Gemini")
        version_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        version_label.setAccessibleName(f"Developers: Elwin Rivera and Gemini.")
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
            
        if sys.platform == "darwin" and PYOBJC_AVAILABLE:
            try:
                self._mac_delegate = AdbPromiseDelegate.alloc().init()
                self._mac_delegate.adb_cmd = self.adb_cmd
                self._mac_delegate.remote_path = self.remote_path
                self._mac_delegate.file_name = os.path.basename(self.remote_path.rstrip('/'))
                self._mac_delegate.main_window = self.window()
                
                self._mac_provider = NSFilePromiseProvider.alloc().initWithFileType_delegate_("public.data", self._mac_delegate)
                self._mac_drag_item = NSDraggingItem.alloc().initWithPasteboardWriter_(self._mac_provider)
                
                img = NSImage.alloc().initWithSize_(NSSize(32, 32))
                self._mac_drag_item.setDraggingFrame_contents_( ((0,0),(32,32)), img )
                
                ns_view = NSApp.mainWindow().contentView() if NSApp.mainWindow() else None
                mac_event = getattr(self, '_mac_press_event', None) or NSApp.currentEvent()
                
                if ns_view and mac_event:
                    ns_view.beginDraggingSessionWithItems_event_source_([self._mac_drag_item], mac_event, self._mac_delegate)
                    return 
            except Exception as e:
                print(f"File Promise Event Error: {e}")
            return 

        original_text = self.text()
        self.setText("Preparing...")
        self.setEnabled(False)

        temp_dir = tempfile.gettempdir()
        base_name = os.path.basename(self.remote_path.rstrip('/'))
        local_dest = os.path.join(temp_dir, base_name)
        
        cmd = self.adb_cmd + ["pull", "-p", self.remote_path, local_dest]
        
        process = QProcess()
        process.setProgram(cmd[0])
        process.setArguments(cmd[1:])
        process.start()
        
        output_buffer = ""
        
        while process.state() != QProcess.ProcessState.NotRunning:
            process.waitForReadyRead(50) 
            
            data = process.readAllStandardOutput().data().decode('utf-8', errors='replace')
            data += process.readAllStandardError().data().decode('utf-8', errors='replace')
            
            if data:
                output_buffer += data
                matches = re.findall(r'(\d+)\s*%', output_buffer[-2000:])
                if matches:
                    self.setText(f"Preparing for drop... {matches[-1]}%")
            
            QApplication.processEvents()

        self.setText(original_text)
        self.setEnabled(True)
        
        if os.path.exists(local_dest):
            drag = QDrag(self)
            mime = QMimeData()
            mime.setUrls([QUrl.fromLocalFile(local_dest)])
            drag.setMimeData(mime)
            drag.exec(Qt.DropAction.CopyAction)

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
        self.selected_item_name = None
        self.selected_item_is_dir = False
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

        self.selected_label = QLabel("Selected: None")
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
        self.menu_btn.setAccessibleName("Open Menu for selected item or current folder")
        self.menu_btn.clicked.connect(self.open_menu)
        action_layout.addWidget(self.menu_btn)
        
        if self.mode == "select_dir":
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

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            
    def dropEvent(self, event):
        urls = event.mimeData().urls()
        local_paths = [u.toLocalFile() for u in urls if os.path.exists(u.toLocalFile())]
        if local_paths:
            args = ["push"] + local_paths + [self.current_path]
            if self.parent():
                self.parent().execute_tool("ADB", args)
            self.accept()

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
        layout = QVBoxLayout(dialog)

        if self.selected_item_name:
            target_name = self.selected_item_name
            target_path = f"{self.current_path}{self.selected_item_name}"
        else:
            target_name = "Current Folder"
            target_path = self.current_path

        item_lbl = QLabel(f"Target: {target_name}")
        item_lbl.setStyleSheet("font-weight: bold;")
        layout.addWidget(item_lbl)

        btn_copy_mac = QPushButton("Copy to Mac")
        btn_copy_mac.clicked.connect(lambda: [dialog.accept(), self.action_pull(target_path, move=False)])
        layout.addWidget(btn_copy_mac)

        btn_move_mac = QPushButton("Move to Mac")
        btn_move_mac.clicked.connect(lambda: [dialog.accept(), self.action_pull(target_path, move=True)])
        layout.addWidget(btn_move_mac)

        btn_copy_and = QPushButton("Copy file or folder within Android")
        btn_copy_and.clicked.connect(lambda: [dialog.accept(), self.action_copy(target_path)])
        layout.addWidget(btn_copy_and)

        btn_move_and = QPushButton("Move file or folder within Android")
        btn_move_and.clicked.connect(lambda: [dialog.accept(), self.action_move(target_path)])
        layout.addWidget(btn_move_and)

        del_text = "Delete selected folder" if self.selected_item_is_dir else "Delete selected file"
        btn_delete = QPushButton(del_text)
        btn_delete.setStyleSheet("color: red;")
        btn_delete.clicked.connect(lambda: [dialog.accept(), self.action_delete(target_path)])
        layout.addWidget(btn_delete)

        layout.addWidget(QLabel("Global Actions:"))

        btn_push_mac = QPushButton("Push File/Folder from Mac")
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
        msg.setWindowTitle("Push from Mac")
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

    def action_delete(self, target_path):
        reply = QMessageBox.warning(self, "Confirm Delete", 
                                    f"Are you sure you want to PERMANENTLY delete:\n\n{target_path}\n\nThis cannot be undone.", 
                                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
                                    
        if reply == QMessageBox.StandardButton.Yes:
            subprocess.run(self.adb_cmd + ["shell", "rm", "-rf", shlex.quote(target_path)])
            if target_path == self.current_path:
                self.go_up()
            else:
                self.load_directory(self.current_path)
        
    def action_pull(self, target_path, move=False):
        local_dest = QFileDialog.getExistingDirectory(self, "Select Save Destination on Mac")
        if local_dest:
            if self.parent():
                action = "move_to_mac" if move else "pull"
                self.parent().execute_internal_transfer(action, target_path, local_dest)
            self.accept()

    def action_move(self, target_path):
        target_name = os.path.basename(target_path.rstrip('/')) or "Current Folder"
        dest, ok = QInputDialog.getText(self, "Destination", f"Enter destination path for {target_name}:", text=self.current_path)
        if ok and dest.strip():
            if self.parent():
                self.parent().execute_internal_transfer("android_move", target_path, dest.strip())
            self.accept()

    def action_copy(self, target_path):
        target_name = os.path.basename(target_path.rstrip('/')) or "Current Folder"
        dest, ok = QInputDialog.getText(self, "Destination", f"Enter destination path for {target_name}:", text=self.current_path)
        if ok and dest.strip():
            if self.parent():
                self.parent().execute_internal_transfer("android_copy", target_path, dest.strip())
            self.accept()

    def select_current_directory(self):
        self.selected_path = self.current_path
        self.accept()

    def load_directory(self, path):
        self.current_path = path
        self.path_label.setText(f"Current Directory: {self.current_path}")
        self.selected_item_name = None
        self.selected_item_is_dir = False
        self.selected_label.setText("Selected: None")
        self.selected_label.setAccessibleName("Selected item: None")
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
                
                type_str = "Folder" if is_dir else "File"
                acc_name = f"{type_str}: {name}, Size: {size_str}" if size_str else f"{type_str}: {name}"
                btn.setAccessibleName(acc_name)
                
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

        self.selected_item_name = name
        self.selected_item_is_dir = is_dir
        self.selected_label.setText(f"Selected: {name}")
        self.selected_label.setAccessibleName(f"Selected item: {name}")
        
        for b in self.item_buttons:
            b.setStyleSheet("")
        btn.setStyleSheet("background-color: #005599; color: white;")

        if is_dir:
            self.load_directory(f"{self.current_path}{name}/")

    def on_item_context_menu(self, name, is_dir, btn):
        self.selected_item_name = name
        self.selected_item_is_dir = is_dir
        self.selected_label.setText(f"Selected: {name}")
        self.selected_label.setAccessibleName(f"Selected item: {name}")
        
        for b in self.item_buttons:
            b.setStyleSheet("")
        btn.setStyleSheet("background-color: #005599; color: white;")
        
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
        self.speech_processes = []
        
        self.setWindowTitle("ADB and Fastboot Tool")
        self.setAccessibleName("ADB and Fastboot Main Window")
        
        self.process = QProcess(self)
        self.process.readyReadStandardOutput.connect(self.handle_stdout)
        self.process.readyReadStandardError.connect(self.handle_stderr)
        self.process.finished.connect(self.handle_finished)

        self.transfer_thread = None
        
        self.setup_ui()
        QTimer.singleShot(500, self.check_configuration)

    def get_current_serial(self):
        return self.current_target_serial

    def open_device_picker(self):
        dialog = DeviceSelectionDialog(self.adb_path, self.current_target_serial, self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.current_target_serial = dialog.selected_serial
            display_name = self.current_target_serial if self.current_target_serial else "Default / Any"
            self.target_dev_label.setText(f"Target Device: {display_name}")
            self.target_dev_label.setAccessibleName(f"Current Target Device: {display_name}")

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            
    def dropEvent(self, event):
        urls = event.mimeData().urls()
        local_paths = [u.toLocalFile() for u in urls if os.path.exists(u.toLocalFile())]
        if local_paths:
            serial = self.get_current_serial()
            dialog = AccessibleAndroidBrowser(self.adb_path, serial=serial, mode="push", start_path=self.default_android_dir, parent=self)
            if dialog.exec() == QDialog.DialogCode.Accepted and dialog.selected_path:
                args = ["push"] + local_paths + [dialog.selected_path]
                self.execute_tool("ADB", args)

    def announce(self, message):
        if not message.strip():
            return
            
        if QT_ACCESSIBILITY_AVAILABLE:
            self.log_output.setAccessibleDescription(message.strip())
            QAccessible.updateAccessibility(QAccessibleEvent(self.log_output, QAccessible.Event.Alert))
            if sys.platform != "darwin":
                return

        if sys.platform == "darwin":
            proc = subprocess.Popen(["say", message.strip()], stderr=subprocess.DEVNULL)
            self.speech_processes.append(proc)
        elif sys.platform == "win32":
            safe_msg = message.replace('"', '""').replace("'", "''")
            script = f"Add-Type -AssemblyName System.Speech; (New-Object System.Speech.Synthesis.SpeechSynthesizer).Speak('{safe_msg}')"
            try:
                proc = subprocess.Popen(["powershell", "-WindowStyle", "Hidden", "-Command", script], creationflags=subprocess.CREATE_NO_WINDOW)
                self.speech_processes.append(proc)
            except AttributeError:
                proc = subprocess.Popen(["powershell", "-WindowStyle", "Hidden", "-Command", script])
                self.speech_processes.append(proc)
        elif sys.platform.startswith("linux"):
            proc = subprocess.Popen(["spd-say", message], stderr=subprocess.DEVNULL)
            self.speech_processes.append(proc)
            
        self.speech_processes = [p for p in self.speech_processes if p.poll() is None]

    def stop_speech(self):
        for p in self.speech_processes:
            try:
                p.terminate()
            except Exception:
                pass
        self.speech_processes.clear()
        
        if sys.platform == "darwin":
            subprocess.Popen(["killall", "say"], stderr=subprocess.DEVNULL)
        elif sys.platform.startswith("linux"):
            subprocess.Popen(["spd-say", "-S"], stderr=subprocess.DEVNULL)

    def setup_ui(self):
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        layout = QVBoxLayout()
        central_widget.setLayout(layout)

        prefs_layout = QHBoxLayout()
        self.prefs_btn = QPushButton("Preferences")
        self.prefs_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_FileDialogListView))
        self.prefs_btn.setAccessibleName("Preferences")
        self.prefs_btn.setAccessibleDescription("")
        self.prefs_btn.clicked.connect(self.open_preferences)
        prefs_layout.addStretch()
        prefs_layout.addWidget(self.prefs_btn)
        layout.addLayout(prefs_layout)

        transfer_label = QLabel("File Transfers (Or Drag and Drop file here):")
        self.wizard_btn = QPushButton("File Manager")
        self.wizard_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ComputerIcon))
        self.wizard_btn.setAccessibleName("File Manager")
        self.wizard_btn.setAccessibleDescription("Click to open the file manager for pushing, pulling, moving, or deleting files.")
        self.wizard_btn.clicked.connect(self.start_transfer_wizard)
        
        layout.addWidget(transfer_label)
        layout.addWidget(self.wizard_btn)
        
        dev_layout = QHBoxLayout()
        self.target_dev_label = QLabel("Target Device: Default / Any")
        self.target_dev_label.setAccessibleName("Current Target Device: Default or Any")
        
        self.choose_dev_btn = QPushButton("Device Manager")
        self.choose_dev_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_ComputerIcon))
        self.choose_dev_btn.setAccessibleName("Device Manager")
        self.choose_dev_btn.clicked.connect(self.open_device_picker)
        
        dev_layout.addWidget(self.target_dev_label)
        dev_layout.addWidget(self.choose_dev_btn)
        dev_layout.addStretch()
        layout.addLayout(dev_layout)

        term_label = QLabel("Command Terminal:")
        
        self.adb_radio = QRadioButton("ADB")
        self.adb_radio.setChecked(True)
        self.adb_radio.setAccessibleName("Use ADB Tool")
        
        self.fastboot_radio = QRadioButton("Fastboot")
        self.fastboot_radio.setAccessibleName("Use Fastboot Tool")

        self.cmd_input = QLineEdit()
        self.cmd_input.setAccessibleName("Command Input")
        self.cmd_input.setAccessibleDescription("Type raw arguments here. Do not include 'adb' or 'fastboot'. Press Enter to run.")
        self.cmd_input.returnPressed.connect(self.run_command)

        self.stop_btn = QPushButton("Stop Command")
        self.stop_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_BrowserStop))
        self.stop_btn.setAccessibleName("Stop Running Command")
        self.stop_btn.setEnabled(False)
        self.stop_btn.clicked.connect(self.stop_command)

        cmd_layout = QHBoxLayout()
        cmd_layout.addWidget(self.adb_radio)
        cmd_layout.addWidget(self.fastboot_radio)
        cmd_layout.addWidget(self.cmd_input)
        cmd_layout.addWidget(self.stop_btn)
        
        layout.addWidget(term_label)
        layout.addLayout(cmd_layout)

        out_layout = QHBoxLayout()
        out_label = QLabel("Terminal Output:")
        
        self.status_label = QLabel("Status: Idle")
        self.status_label.setAccessibleName("Status: Idle")
        self.status_label.setStyleSheet("font-weight: bold; color: #0078D7; font-size: 14px; margin-left: 15px;")
        
        self.stats_container = QWidget()
        self.stats_layout = QVBoxLayout(self.stats_container)
        self.stats_layout.setContentsMargins(15, 0, 15, 0)
        
        self.pct_label = QLabel("Overall Progress: 0%")
        self.pct_label.setAccessibleName("Overall Progress: 0 percent")
        self.pct_label.setStyleSheet("font-weight: bold; font-size: 14px;")
        
        self.speed_label = QLabel("Speed: 0.00 MB/s (0.00 MB transferred)")
        self.speed_label.setAccessibleName("Speed: 0 Megabytes per second")
        
        self.file_label = QLabel("Current File: None")
        self.file_label.setAccessibleName("Current File: None")
        
        self.stats_layout.addWidget(self.pct_label)
        self.stats_layout.addWidget(self.speed_label)
        self.stats_layout.addWidget(self.file_label)
        
        self.stats_container.hide()

        self.stop_speech_btn = QPushButton("Stop Speech")
        self.stop_speech_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MediaStop))
        self.stop_speech_btn.setAccessibleName("Stop Speech")
        self.stop_speech_btn.clicked.connect(self.stop_speech)
        self.stop_speech_btn.setVisible(self.announce_terminal)

        self.clear_btn = QPushButton("Clear Terminal")
        self.clear_btn.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_TrashIcon))
        self.clear_btn.setAccessibleName("Clear Terminal Output")
        self.clear_btn.clicked.connect(self.clear_log)
        
        out_layout.addWidget(out_label)
        out_layout.addWidget(self.status_label)
        out_layout.addWidget(self.stats_container)
        out_layout.addStretch()
        out_layout.addWidget(self.stop_speech_btn)
        out_layout.addWidget(self.clear_btn)
        
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
        
        self.update_live_region_settings()
        
        layout.addLayout(out_layout)
        layout.addWidget(self.log_output)

    def update_live_region_settings(self):
        if self.announce_terminal:
            self.log_output.setProperty("container-live", "polite")
            self.log_output.setProperty("live", "polite")
            self.stop_speech_btn.setVisible(True)
        else:
            self.log_output.setProperty("container-live", "none")
            self.log_output.setProperty("live", "none")
            self.stop_speech_btn.setVisible(False)

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
                    "- Added toggle to disable file size calculation for faster File Manager loading.\n"
                    "- Added dynamic 'Stop Speech' button for VoiceOver interruptions.\n"
                    "- Progress indicators now automatically hide when idle for privacy.\n"
                    "- Relabeled Device Manager and Preferences for cleaner screen reader navigation.\n"
                    "- Redesigned Android Browser: Removed intrusive pop-ups. Replaced with dedicated Menu button and active item selection.\n"
                    "- Repaired PyObjC memory pointer bugs to natively fulfill File Promises without temp files.\n"
                    "- Recalibrated file tracker using absolute byte cursors to strictly prevent >100% bugs.\n"
                    "- Refactored Global UI actions directly into the master Action Menu.\n"
                    "- Testing beta accessibility features.")
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

    def execute_internal_transfer(self, action, src, dest):
        if self.process.state() != QProcess.ProcessState.NotRunning or (self.transfer_thread and self.transfer_thread.isRunning()):
            self.log("A process is already running. Please wait or stop it first.")
            return

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
        self.log(f"\nInitiating {action} for: {src}", skip_announce=True)
        
        self.stop_btn.setEnabled(True)
        self.wizard_btn.setEnabled(False)

        self.transfer_thread = AdbTransferThread(self.adb_path, self.get_current_serial(), action, [src], dest)
        self.transfer_thread.progress_update.connect(self.handle_thread_progress)
        self.transfer_thread.finished_transfer.connect(self.handle_thread_finished)
        self.transfer_thread.start()

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
