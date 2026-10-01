#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tip Editor - Forge Neo Edition v9.5 (Modern Desktop App)
========================================================
Финальная версия с корректной многоязычной обработкой метаданных,
быстрым drag & drop и точным позиционированием '×'.

ИСПРАВЛЕНО В 9.5:
- EXIF UserComment теперь читается из ExifIFD-поддиректории (0x8769) —
  большинство JPEG/WEBP хранят промпт именно там. Раньше искали только
  в корне EXIF → «метаданные не найдены».
- Бинарный fallback ищет "steps:" в UTF-8, UTF-16LE и UTF-16BE —
  покрывает Neo/A1111/ComfyUI/WEBP.
- '×' рисуется вручную через QPainter — точный центр, не зависит от
  QSS text-align и выбранного шрифта.
- Drag & Drop начинается мгновенно (порог 6 px вместо системного),
  клик эмитится на mouseRelease — UI не блокируется парсингом.
- Перетаскивание во внешние приложения (Проводник, рабочий стол,
  Photoshop, Telegram, браузер) через text/uri-list.

ИСПРАВЛЕНО В 9.3:
- Правильное декодирование UTF-16, бинарного EXIF, откат latin-1 → UTF-8.
- Кириллица, CJK, японский, корейский, арабский, иврит — как отдельно,
  так и смешанно с латиницей.
- Кэш MetadataParser (mtime) + QPixmap (LRU).

ТРЕБОВАНИЯ:
    pip install PySide6 Pillow
    (или pip install PyQt6 Pillow)
"""

import sys
import os
import re
import json
import csv
import shutil
from pathlib import Path
from collections import OrderedDict

# --- КРОСС-ПЛАТФОРМЕННЫЙ ИМПОРТ QT ---
QT_LIB = None
try:
    from PySide6.QtWidgets import (
        QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
        QTextEdit, QLabel, QPushButton, QFileDialog, QMessageBox, QFrame,
        QComboBox, QSpinBox, QSplitter, QGridLayout, QScrollArea, QSlider,
        QStatusBar, QTableWidget, QTableWidgetItem,
        QHeaderView, QDialog, QProgressBar, QCheckBox, QGroupBox, QMenu
    )
    from PySide6.QtCore import (
        Qt, QSettings, QPoint, QRect, QTimer, Signal, QMimeData, QUrl
    )
    from PySide6.QtGui import (
        QDragEnterEvent, QDropEvent, QPixmap, QFont, QIcon, QFontDatabase,
        QPainter, QPen, QColor, QResizeEvent, QKeySequence, QShortcut,
        QDrag, QCursor
    )
    QT_LIB = "PySide6"
except ImportError:
    try:
        from PyQt6.QtWidgets import (
            QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
            QTextEdit, QLabel, QPushButton, QFileDialog, QMessageBox, QFrame,
            QComboBox, QSpinBox, QSplitter, QGridLayout, QScrollArea, QSlider,
            QStatusBar, QTableWidget, QTableWidgetItem,
            QHeaderView, QDialog, QProgressBar, QCheckBox, QGroupBox, QMenu
        )
        from PyQt6.QtCore import (
            Qt, QSettings, QPoint, QRect, QTimer, pyqtSignal as Signal,
            QMimeData, QUrl
        )
        from PyQt6.QtGui import (
            QDragEnterEvent, QDropEvent, QPixmap, QFont, QIcon, QFontDatabase,
            QPainter, QPen, QColor, QResizeEvent, QKeySequence, QShortcut,
            QDrag, QCursor
        )
        QT_LIB = "PyQt6"
    except ImportError:
        print("Ошибка: Не найдена библиотека PySide6 или PyQt6.")
        print("Установите: pip install PySide6 Pillow")
        sys.exit(1)

# --- Pillow ---
HAS_PIL = False
try:
    from PIL import Image, ExifTags
    from PIL.PngImagePlugin import PngInfo
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

# --- ФИКС ИКОНКИ В ПАНЕЛИ ЗАДАЧ WINDOWS ---
if sys.platform == "win32":
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
            "tip.editor.forge.neo.edition.v9.5"
        )
    except Exception:
        pass


# =============================================================================
# === LRU-КЭШ ПИКСМАПОВ ===
# =============================================================================

_PIXMAP_CACHE = OrderedDict()
_PIXMAP_CACHE_MAX = 400


def get_cached_pixmap(path: str) -> QPixmap:
    if path in _PIXMAP_CACHE:
        _PIXMAP_CACHE.move_to_end(path)
        return _PIXMAP_CACHE[path]
    pixmap = QPixmap(path)
    if len(_PIXMAP_CACHE) >= _PIXMAP_CACHE_MAX:
        try:
            _PIXMAP_CACHE.popitem(last=False)
        except Exception:
            _PIXMAP_CACHE.clear()
    _PIXMAP_CACHE[path] = pixmap
    return pixmap


def invalidate_pixmap_cache(path: str = None):
    if path is None:
        _PIXMAP_CACHE.clear()
    else:
        _PIXMAP_CACHE.pop(path, None)


# =============================================================================
# === МОДУЛЬ АНАЛИЗА МЕТАДАННЫХ ===
# =============================================================================

class MetadataParser:
    """Глубокий анализ и корректное многоязычное декодирование метаданных."""

    _cache = OrderedDict()
    _cache_max = 400

    STRICT_ENCODINGS = (
        'utf-8',
        'gb18030', 'big5', 'euc-kr', 'shift_jis',
        'cp1251', 'cp1252', 'koi8-r', 'iso-8859-5',
        'iso-8859-1', 'latin-1',
    )

    @classmethod
    def invalidate_cache(cls, file_path: str = None):
        if file_path is None:
            cls._cache.clear()
        else:
            cls._cache = OrderedDict(
                (k, v) for k, v in cls._cache.items()
                if not (isinstance(k, tuple) and k[0] == file_path)
            )

    # ----------------------------------------------------- ДЕКОДИРОВАНИЕ

    @staticmethod
    def _looks_like_mojibake(s: str) -> bool:
        return any('\u00c0' <= c <= '\u00ff' for c in s)

    @staticmethod
    def _is_reasonable_text(s: str) -> bool:
        if not s or len(s) < 2:
            return False
        printable = sum(1 for c in s if c.isprintable() or c in '\n\r\t')
        if printable / len(s) < 0.80:
            return False
        weird = sum(1 for c in s if 0x2E80 <= ord(c) <= 0x4DFF)
        if weird > 3:
            return False
        return True

    @staticmethod
    def _truncate_at_binary(s: str) -> str:
        for i, c in enumerate(s):
            if 0x2E80 <= ord(c) <= 0x4DFF:
                j = i
                while j < len(s) and (0x2E80 <= ord(s[j]) <= 0x4DFF
                                      or not s[j].isprintable()):
                    j += 1
                if j - i >= 6:
                    return s[:i].rstrip()
        return s.rstrip()

    @staticmethod
    def _extract_text_from_exif_blob(val: bytes) -> str:
        try:
            text = val.decode('latin-1')
        except Exception:
            return ""
        runs = re.findall(r'[\x20-\xff]{30,}', text)
        if not runs:
            return ""
        for run in sorted(runs, key=len, reverse=True):
            try:
                raw = run.encode('latin-1')
            except UnicodeEncodeError:
                continue
            for enc in ('utf-8', 'gb18030', 'cp1251', 'latin-1'):
                try:
                    decoded = raw.decode(enc)
                except UnicodeDecodeError:
                    continue
                if MetadataParser._is_reasonable_text(decoded) and 'Exif' not in decoded[:8]:
                    return decoded.rstrip()
        return ""

    @staticmethod
    def _decode_bytes(val: bytes) -> str:
        if not val:
            return ""

        unicode_idx = val.find(b'UNICODE\x00')
        if unicode_idx != -1:
            body = val[unicode_idx + 8:]
            for enc in ('utf-16le', 'utf-16be', 'utf-8'):
                try:
                    res = body.decode(enc).rstrip('\x00').rstrip()
                except UnicodeDecodeError:
                    continue
                if res.strip():
                    return MetadataParser._truncate_at_binary(res)

        ascii_idx = val.find(b'ASCII\x00\x00\x00')
        if ascii_idx != -1:
            body = val[ascii_idx + 8:]
            for enc in ('utf-8', 'ascii', 'latin-1', 'gb18030', 'cp1251'):
                try:
                    res = body.decode(enc).rstrip('\x00').rstrip()
                except UnicodeDecodeError:
                    continue
                if res.strip():
                    return MetadataParser._truncate_at_binary(res)

        if (val[:6] == b'Exif\x00\x00' or
                val[:4] in (b'MM\x00*', b'II\x2a\x00') or
                b'Exif\x00\x00' in val[:64]):
            extracted = MetadataParser._extract_text_from_exif_blob(val)
            return extracted if extracted else ""

        if len(val) > 8:
            null_ratio = val.count(0) / len(val)
            if null_ratio > 0.20:
                even_nulls = sum(1 for i in range(0, len(val), 2) if val[i] == 0)
                odd_nulls = sum(1 for i in range(1, len(val), 2) if val[i] == 0)
                order = ('utf-16le', 'utf-16be') if odd_nulls >= even_nulls else ('utf-16be', 'utf-16le')
                for enc in order:
                    try:
                        res = val.decode(enc).rstrip('\x00')
                    except UnicodeDecodeError:
                        continue
                    if MetadataParser._is_reasonable_text(res):
                        return res

        for enc in MetadataParser.STRICT_ENCODINGS:
            try:
                res = val.decode(enc).rstrip('\x00')
            except UnicodeDecodeError:
                continue
            if MetadataParser._is_reasonable_text(res):
                return res

        return val.decode('latin-1').rstrip('\x00')

    @staticmethod
    def _safe_decode(val) -> str:
        if isinstance(val, bytes):
            return MetadataParser._decode_bytes(val)

        if isinstance(val, str):
            try:
                raw = val.encode('latin-1')
            except UnicodeEncodeError:
                return val

            if not MetadataParser._looks_like_mojibake(val):
                return val

            try:
                return raw.decode('utf-8')
            except UnicodeDecodeError:
                pass

            for enc in ('gb18030', 'big5', 'euc-kr', 'shift_jis'):
                try:
                    return raw.decode(enc)
                except UnicodeDecodeError:
                    continue

            for enc in ('cp1251', 'koi8-r', 'iso-8859-5'):
                try:
                    return raw.decode(enc)
                except UnicodeDecodeError:
                    continue

            return val

        return str(val)

    @staticmethod
    def decode_user_comment(val) -> str:
        if isinstance(val, bytes):
            return MetadataParser.clean_prompt_junk(MetadataParser._decode_bytes(val))
        if isinstance(val, str):
            return MetadataParser.clean_prompt_junk(MetadataParser._safe_decode(val))
        return MetadataParser.clean_prompt_junk(str(val))

    # --------------------------------------------------------- ОЧИСТКА

    @staticmethod
    def clean_prompt_junk(text: str) -> str:
        if not text:
            return ""

        text = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]', '', text)

        text = re.sub(
            r'(?i)(?:ExifMM\*i|MM\*i[\s\$\(\)\*\,\:\-\\\/]*|II\*|2\(UNICODE|'
            r'^(?:UNICODE|ASCII|UserComment|ImageDescription|Comment|IHDR)[\s\$\(\)\*\,\:\-\\\/]*|'
            r'(?<![\w])tEXtparameters(?![\w])|'
            r'(?<![\w])iTXtparameters(?![\w])|'
            r'(?<![\w])giTXtparameters(?![\w])|'
            r'(?<![\w])parameters(?![\w]))',
            '', text
        )

        text = re.sub(r'^[^\w\s\(\)\[\]<>{}\.,\-+!="\'`]+', '', text)
        return text.lstrip(' ,:\n\r\t$()/*').strip()

    # ----------------------------------------------------------- EXIF

    @staticmethod
    def _extract_exif_text(img, info) -> str:
        """
        Извлекает текст промпта из EXIF (JPEG/WEBP/TIFF).
        Ключевое: UserComment лежит в ExifIFD-поддиректории (0x8769),
        а не в корне EXIF.
        """
        # --- 1. info["exif"] как сырые байты ---
        if isinstance(info.get("exif"), bytes):
            decoded = MetadataParser._decode_bytes(info["exif"])
            if decoded and len(decoded.strip()) > 10:
                low = decoded.lower()
                if "steps:" in low or "negative prompt:" in low or "prompt" in low:
                    return decoded

        # --- 2. img.getexif() + ExifIFD-поддиректория ---
        exif_obj = None
        try:
            exif_obj = img.getexif()
        except Exception:
            pass
        if not exif_obj:
            try:
                exif_obj = img._getexif()
            except Exception:
                pass
        if not exif_obj:
            return ""

        ifds = [exif_obj]
        for ptr in (0x8769, 0x8825):
            try:
                sub = exif_obj.get_ifd(ptr)
                if sub:
                    ifds.append(sub)
            except Exception:
                pass

        priority_tags = ("UserComment", 0x9286, 37510)
        secondary_tags = ("ImageDescription", 0x010e, 270, "MakerNote", 0x927c, 37500)

        def _try_ifd(ifd, tags):
            try:
                items = list(ifd.items())
            except Exception:
                return ""
            for tag, val in items:
                tag_name = ExifTags.TAGS.get(tag, tag)
                if tag_name in tags or tag in tags:
                    if isinstance(val, bytes):
                        decoded = MetadataParser._decode_bytes(val)
                    else:
                        decoded = MetadataParser._safe_decode(val)
                    if decoded and len(decoded.strip()) > 10:
                        return decoded
            return ""

        for ifd in ifds:
            res = _try_ifd(ifd, priority_tags)
            if res:
                return res
        for ifd in ifds:
            res = _try_ifd(ifd, secondary_tags)
            if res:
                return res
        return ""

    # ----------------------------------------------------------- ПАРСИНГ

    @staticmethod
    def parse_image(file_path: str, use_cache: bool = True) -> dict:
        key = None
        if use_cache:
            try:
                st = os.stat(file_path)
                key = (file_path, st.st_mtime, st.st_size)
                if key in MetadataParser._cache:
                    MetadataParser._cache.move_to_end(key)
                    return MetadataParser._cache[key]
            except Exception:
                key = None

        result = MetadataParser._do_parse(file_path)

        if use_cache and key is not None:
            if len(MetadataParser._cache) >= MetadataParser._cache_max:
                try:
                    MetadataParser._cache.popitem(last=False)
                except Exception:
                    MetadataParser._cache.clear()
            MetadataParser._cache[key] = result
        return result

    @staticmethod
    def _do_parse(file_path: str) -> dict:
        result = {
            "file_path": file_path,
            "filename": os.path.basename(file_path),
            "prompt": "",
            "negative_prompt": "",
            "settings_raw": "",
            "parsed_params": {},
            "raw_metadata": "",
            "format": "",
            "size": (0, 0),
            "file_size_bytes": 0,
            "has_metadata": False
        }

        path_obj = Path(file_path)
        if not path_obj.exists():
            return result

        try:
            result["file_size_bytes"] = path_obj.stat().st_size
        except Exception:
            pass

        raw_text = ""
        if HAS_PIL:
            try:
                with Image.open(file_path) as img:
                    result["format"] = img.format or path_obj.suffix.upper().replace(".", "")
                    result["size"] = img.size

                    info = img.info or {}

                    if "parameters" in info:
                        raw_text = MetadataParser._safe_decode(info["parameters"])
                    elif "prompt" in info:
                        raw_text = MetadataParser._parse_comfy_json(
                            info.get("prompt"), info.get("workflow")
                        )
                    elif "Comment" in info:
                        raw_text = MetadataParser._safe_decode(info["Comment"])
                    elif "comment" in info:
                        raw_text = MetadataParser._safe_decode(info["comment"])
                    elif "Description" in info:
                        raw_text = MetadataParser._safe_decode(info["Description"])

                    # EXIF fallback — читает UserComment из ExifIFD
                    if not raw_text:
                        raw_text = MetadataParser._extract_exif_text(img, info)

            except Exception:
                pass

        # Бинарный fallback
        if not raw_text or ("steps:" not in raw_text.lower()
                            and "negative prompt:" not in raw_text.lower()):
            fallback = MetadataParser._binary_fallback_read(file_path)
            if fallback:
                raw_text = fallback

        raw_text = MetadataParser.clean_prompt_junk(raw_text)

        if raw_text and ("steps:" in raw_text.lower()
                         or "negative prompt:" in raw_text.lower()
                         or len(raw_text.strip()) > 10):
            result["has_metadata"] = True
            result["raw_metadata"] = raw_text
            parsed = MetadataParser._split_prompt_components(raw_text)
            result["prompt"] = MetadataParser.clean_prompt_junk(parsed["prompt"])
            result["negative_prompt"] = MetadataParser.clean_prompt_junk(parsed["negative_prompt"])
            result["settings_raw"] = parsed["settings_raw"]
            result["parsed_params"] = MetadataParser._parse_settings_kv(parsed["settings_raw"])

        return result

    @staticmethod
    def _parse_comfy_json(prompt_json, workflow_json) -> str:
        prompts = []
        try:
            data = json.loads(prompt_json) if isinstance(prompt_json, str) else prompt_json
            if isinstance(data, dict):
                for node_id, node in data.items():
                    class_type = node.get("class_type", "")
                    inputs = node.get("inputs", {})
                    if "CLIPTextEncode" in class_type or "Prompt" in class_type:
                        text = inputs.get("text", "")
                        if text and isinstance(text, str):
                            prompts.append(text)
        except Exception:
            pass
        return "\n".join(prompts) if prompts else str(prompt_json or "")

    @staticmethod
    def _binary_fallback_read(file_path: str) -> str:
        """
        Читает сырые байты файла. Ищет 'steps:' в UTF-8, UTF-16LE, UTF-16BE —
        покрывает Neo/A1111/ComfyUI/WEBP/JPEG/PNG.
        """
        try:
            with open(file_path, "rb") as f:
                data = f.read()
        except Exception:
            return ""

        # ---- 1. PNG tEXt/iTXt чанки ----
        for marker in (b'tEXtparameters\x00', b'iTXtparameters\x00',
                       b'tEXtparameters', b'parameters\x00'):
            idx = data.find(marker)
            if idx == -1:
                continue
            start = idx + len(marker)
            chunk = data[start:start + 20000]
            for enc in ('utf-8', 'utf-16le', 'gb18030', 'big5',
                        'euc-kr', 'shift_jis', 'cp1251', 'latin-1'):
                try:
                    text = chunk.decode(enc)
                except UnicodeDecodeError:
                    continue
                low = text.lower()
                if "steps:" in low or "negative prompt:" in low:
                    raw = "".join(c for c in text if c.isprintable() or c in '\n\r\t')
                    cleaned = MetadataParser.clean_prompt_junk(raw)
                    if cleaned:
                        return cleaned

        # ---- 2. EXIF UserComment с маркером UNICODE ----
        for unicode_marker in (b'UNICODE\x00',
                               b'U\x00N\x00I\x00C\x00O\x00D\x00E\x00\x00\x00'):
            unicode_idx = data.find(unicode_marker)
            if unicode_idx != -1:
                body = data[unicode_idx + len(unicode_marker):][:65536]
                for enc in ('utf-16le', 'utf-16be', 'utf-8'):
                    try:
                        text = body.decode(enc, errors='ignore')
                    except Exception:
                        continue
                    low = text.lower()
                    if "steps:" in low or "negative prompt:" in low:
                        ver_idx = low.find("version:")
                        if ver_idx != -1:
                            nl = text.find("\n", ver_idx)
                            if nl == -1 or nl - ver_idx > 300:
                                nl = min(len(text), ver_idx + 200)
                            text = text[:nl]
                        raw = "".join(c for c in text if c.isprintable() or c in '\n\r\t')
                        cleaned = MetadataParser.clean_prompt_junk(raw)
                        if cleaned:
                            return cleaned

        # ---- 3. Поиск 'steps:' во всех кодировках ----
        step_markers = [
            (b"steps:", 'utf-8', 8000, 4000),
            (b"s\x00t\x00e\x00p\x00s\x00:\x00", 'utf-16le', 16000, 8000),
            (b"\x00s\x00t\x00e\x00p\x00s\x00:", 'utf-16be', 16000, 8000),
        ]
        for marker, enc, before, after in step_markers:
            idx = data.find(marker)
            if idx == -1:
                continue
            start = max(0, idx - before)
            chunk = data[start: idx + after]
            try:
                text = chunk.decode(enc, errors='ignore')
            except Exception:
                continue
            raw = "".join(c for c in text if c.isprintable() or c in '\n\r\t')
            cleaned = MetadataParser.clean_prompt_junk(raw)
            if cleaned:
                return cleaned

        # ---- 4. Строгое декодирование всего файла ----
        for enc in ('utf-8', 'gb18030', 'big5', 'euc-kr', 'shift_jis',
                    'utf-16le', 'cp1251', 'cp1252', 'latin-1'):
            try:
                text = data.decode(enc)
            except UnicodeDecodeError:
                continue
            low = text.lower()
            if "steps:" in low or "negative prompt:" in low:
                i = low.find("steps:")
                if i == -1:
                    i = low.find("negative prompt:")
                chunk = text[max(0, i - 5000): min(len(text), i + 2000)]
                raw = "".join(c for c in chunk if c.isprintable() or c in '\n\r\t')
                return MetadataParser.clean_prompt_junk(raw)

        return ""

    @staticmethod
    def _split_prompt_components(raw_text: str) -> dict:
        low = raw_text.lower()
        neg_marker = "negative prompt:"
        set_marker = "steps:"

        prompt, neg_prompt, settings = raw_text, "", ""

        if neg_marker in low and set_marker in low:
            idx_neg = low.find(neg_marker)
            idx_set = low.find(set_marker)
            prompt = raw_text[:idx_neg].strip()
            neg_prompt = raw_text[idx_neg + len(neg_marker):idx_set].strip()
            settings = raw_text[idx_set:].strip()
        elif set_marker in low:
            idx_set = low.find(set_marker)
            prompt = raw_text[:idx_set].strip()
            settings = raw_text[idx_set:].strip()
        else:
            prompt = raw_text.strip()

        if prompt.endswith(','):
            prompt = prompt[:-1].strip()

        for junk in ("iTXtparameters", "giTXtparameters", "tEXtparameters",
                     "ExifMM*i", "MM*i"):
            prompt = prompt.replace(junk, "").strip()

        return {"prompt": prompt, "negative_prompt": neg_prompt, "settings_raw": settings}

    @staticmethod
    def _parse_settings_kv(settings_raw: str) -> dict:
        kv = {}
        if not settings_raw:
            return kv
        pattern = r'([A-Za-z0-9\s_\-\.]+):\s*("[^"]*"|[^,]+)'
        for key, val in re.findall(pattern, settings_raw):
            k = key.strip()
            v = val.strip().strip('"')
            if k:
                kv[k] = v
        return kv


# =============================================================================
# === КНОПКА УДАЛЕНИЯ '×' (рисуется вручную QPainter) ===
# =============================================================================

class HoverRemoveButton(QPushButton):
    """
    Кнопка удаления '×' — символ рисуется вручную через QPainter,
    чтобы всегда быть точно по центру, независимо от QSS/шрифта.
    """
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedSize(18, 18)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip("Убрать миниатюру из истории")
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setFlat(True)
        self._card_hovered = False
        self._btn_hovered = False
        self._apply_state()

    def _apply_state(self):
        visible = self._card_hovered or self._btn_hovered
        if visible:
            self.setStyleSheet("""
                QPushButton {
                    background-color: #0f172a;
                    border: 1px solid #2bbdf8;
                    border-radius: 4px;
                    padding: 0px;
                    margin: 0px;
                }
            """)
        else:
            self.setStyleSheet("""
                QPushButton {
                    background-color: transparent;
                    border: 1px solid transparent;
                    border-radius: 4px;
                    padding: 0px;
                    margin: 0px;
                }
            """)
        self.update()

    def set_card_hovered(self, hovered: bool):
        if self._card_hovered != hovered:
            self._card_hovered = hovered
            self._apply_state()

    def enterEvent(self, event):
        self._btn_hovered = True
        self._apply_state()
        super().enterEvent(event)

    def leaveEvent(self, event):
        self._btn_hovered = False
        self._apply_state()
        super().leaveEvent(event)

    def paintEvent(self, event):
        super().paintEvent(event)
        if not (self._card_hovered or self._btn_hovered):
            return
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        color = QColor("#ffffff") if self._btn_hovered else QColor("#2bbdf8")
        painter.setPen(QPen(color, 1.6, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
        rect = self.rect()
        cx = rect.width() / 2.0
        cy = rect.height() / 2.0
        r = 3.5
        painter.drawLine(QPoint(int(cx - r), int(cy - r)),
                         QPoint(int(cx + r), int(cy + r)))
        painter.drawLine(QPoint(int(cx - r), int(cy + r)),
                         QPoint(int(cx + r), int(cy - r)))


class SaveIconButton(QPushButton):
    def __init__(self, tooltip="Сохранить отредактированные метаданные в файл", parent=None):
        super().__init__(parent)
        self.setFixedSize(36, 36)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip(tooltip)
        self.default_style = """
            QPushButton {
                background-color: #1e293b;
                border: 1px solid #334155;
                border-radius: 6px;
            }
            QPushButton:hover { background-color: #334155; border-color: #2bbdf8; }
            QPushButton:pressed { background-color: #0284c7; }
        """
        self.setStyleSheet(self.default_style)
        self.is_saved = False

    def animate_saved(self):
        self.is_saved = True
        self.setStyleSheet("""
            QPushButton {
                background-color: #10b981;
                border: 1px solid #059669;
                border-radius: 6px;
            }
        """)
        self.update()
        QTimer.singleShot(1200, self.reset_icon)

    def reset_icon(self):
        self.is_saved = False
        self.setStyleSheet(self.default_style)
        self.update()

    def paintEvent(self, event):
        super().paintEvent(event)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.is_saved:
            painter.setPen(QPen(QColor("#ffffff"), 2.5))
            painter.drawPolyline([QPoint(11, 18), QPoint(16, 23), QPoint(25, 13)])
        else:
            painter.setPen(QPen(QColor("#2bbdf8"), 1.8))
            painter.drawRect(QRect(10, 9, 16, 18))
            painter.drawRect(QRect(13, 9, 10, 6))
            painter.drawRect(QRect(13, 18, 10, 9))


class CopyIconButton(QPushButton):
    def __init__(self, tooltip="Копировать", parent=None):
        super().__init__(parent)
        self.setFixedSize(36, 36)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip(tooltip)
        self.default_style = """
            QPushButton {
                background-color: #1e293b;
                border: 1px solid #334155;
                border-radius: 6px;
            }
            QPushButton:hover { background-color: #334155; border-color: #2bbdf8; }
            QPushButton:pressed { background-color: #0284c7; }
        """
        self.setStyleSheet(self.default_style)
        self.is_copied = False

    def animate_copied(self):
        self.is_copied = True
        self.setStyleSheet("""
            QPushButton {
                background-color: #10b981;
                border: 1px solid #059669;
                border-radius: 6px;
            }
        """)
        self.update()
        QTimer.singleShot(1200, self.reset_icon)

    def reset_icon(self):
        self.is_copied = False
        self.setStyleSheet(self.default_style)
        self.update()

    def paintEvent(self, event):
        super().paintEvent(event)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.is_copied:
            painter.setPen(QPen(QColor("#ffffff"), 2.5))
            painter.drawPolyline([QPoint(11, 18), QPoint(16, 23), QPoint(25, 13)])
        else:
            painter.setPen(QPen(QColor("#2bbdf8"), 1.8))
            painter.drawPolyline([QPoint(11, 15), QPoint(11, 25), QPoint(21, 25)])
            painter.drawRect(QRect(14, 9, 12, 14))


# =============================================================================
# === КАРТОЧКА ИСТОРИИ ===
# =============================================================================

class HistoryCardWidget(QFrame):
    clicked = Signal(int, object)
    remove_requested = Signal(int)
    reorder_requested = Signal(int, int)

    def __init__(self, index: int, parent=None):
        super().__init__(parent)
        self.index = index
        self.file_path = ""
        self.is_selected = False
        self.drag_start_pos = None
        self._drag_started = False

        self.setObjectName("HistoryCard")
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAcceptDrops(True)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.customContextMenuRequested.connect(self.show_context_menu)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(0)

        self.lbl_image = QLabel()
        self.lbl_image.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.lbl_image.setScaledContents(False)
        layout.addWidget(self.lbl_image)

        self.lbl_badge = QLabel(self)
        self.lbl_badge.setStyleSheet("""
            QLabel {
                background-color: #0f172a;
                color: #2bbdf8;
                font-size: 10px;
                font-weight: bold;
                border: 1px solid #1e293b;
                border-radius: 4px;
                padding: 1px 4px;
            }
        """)

        self.lbl_select_badge = QLabel("✓", self)
        self.lbl_select_badge.setStyleSheet("""
            QLabel {
                background-color: #2bbdf8;
                color: #0f172a;
                font-size: 10px;
                font-weight: bold;
                border-radius: 9px;
                padding: 1px;
            }
        """)
        self.lbl_select_badge.setFixedSize(18, 18)
        self.lbl_select_badge.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.lbl_select_badge.hide()

        self.btn_delete = HoverRemoveButton(self)
        self.btn_delete.clicked.connect(self.on_delete_clicked)

        self.update_card_style()

    def update_card_style(self):
        if self.is_selected:
            self.setStyleSheet("""
                QFrame#HistoryCard {
                    background-color: #1e3a5f;
                    border: 2px solid #2bbdf8;
                    border-radius: 8px;
                }
            """)
            self.lbl_select_badge.show()
        else:
            self.setStyleSheet("""
                QFrame#HistoryCard {
                    background-color: #121826;
                    border: 2px solid #1e293b;
                    border-radius: 8px;
                }
                QFrame#HistoryCard:hover {
                    border: 2px solid #2bbdf8;
                    background-color: #1a2234;
                }
            """)
            self.lbl_select_badge.hide()

    def set_selected(self, selected: bool):
        self.is_selected = selected
        self.update_card_style()

    def set_data(self, path: str, size: int, slot_number: int):
        self.file_path = path
        self.setFixedSize(size, size)

        self.lbl_badge.setText(f"#{slot_number}")
        self.lbl_badge.adjustSize()
        self.lbl_badge.move(5, 5)

        self.btn_delete.move(size - 23, 5)
        self.btn_delete.raise_()

        self.lbl_select_badge.move(size - 23, size - 23)
        self.lbl_select_badge.raise_()

        filename = os.path.basename(path)
        self.setToolTip(
            f"Слот #{slot_number}: {filename}\nПуть: {path}\n"
            f"(Ctrl/Shift — мульти-выделение; перетащите в приложение; "
            f"внутри — смена позиции)"
        )

        pixmap = get_cached_pixmap(path)
        if not pixmap.isNull():
            inner_size = max(10, size - 10)
            scaled = pixmap.scaled(
                inner_size, inner_size,
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
            self.lbl_image.setPixmap(scaled)
        else:
            self.lbl_image.setText("Файл не найден")
            self.lbl_image.setStyleSheet("color: #ef4444; font-size: 10px;")

        self.btn_delete.raise_()
        self.lbl_select_badge.raise_()

    def on_delete_clicked(self):
        self.remove_requested.emit(self.index)

    def mousePressEvent(self, event):
        """Только фиксируем стартовую позицию. Клик эмитится на release."""
        if event.button() == Qt.MouseButton.LeftButton:
            if not self.btn_delete.geometry().contains(event.pos()):
                self.drag_start_pos = event.pos()
                self._drag_started = False

    def mouseReleaseEvent(self, event):
        """Клик срабатывает только если НЕ было drag."""
        if event.button() == Qt.MouseButton.LeftButton:
            if (self.drag_start_pos is not None
                    and not self._drag_started
                    and not self.btn_delete.geometry().contains(event.pos())):
                self.clicked.emit(self.index, event.modifiers())
            self.drag_start_pos = None
            self._drag_started = False

    def mouseMoveEvent(self, event):
        if not (event.buttons() & Qt.MouseButton.LeftButton):
            return
        if not self.drag_start_pos:
            return
        if self._drag_started:
            return
        # Порог 6 px — драг начинается мгновенно
        if (event.pos() - self.drag_start_pos).manhattanLength() < 6:
            return
        if not self.file_path or not os.path.exists(self.file_path):
            return

        self._drag_started = True

        drag = QDrag(self)
        mime_data = QMimeData()

        mime_data.setUrls([QUrl.fromLocalFile(self.file_path)])
        mime_data.setData("application/x-history-card-index",
                          str(self.index).encode("utf-8"))
        mime_data.setText(self.file_path)

        drag.setMimeData(mime_data)

        pixmap = self.lbl_image.pixmap()
        if pixmap and not pixmap.isNull():
            drag.setPixmap(pixmap.scaled(
                64, 64,
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            ))
            drag.setHotSpot(QPoint(32, 32))

        drag.exec(
            Qt.DropAction.CopyAction | Qt.DropAction.MoveAction,
            Qt.DropAction.CopyAction
        )

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasFormat("application/x-history-card-index"):
            event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent):
        if event.mimeData().hasFormat("application/x-history-card-index"):
            try:
                raw = event.mimeData().data("application/x-history-card-index")
                if not isinstance(raw, (bytes, bytearray)):
                    raw = bytes(raw)
                src_idx = int(bytes(raw).decode("utf-8"))
                self.reorder_requested.emit(src_idx, self.index)
                event.acceptProposedAction()
            except Exception:
                pass

    def enterEvent(self, event):
        self.btn_delete.set_card_hovered(True)
        super().enterEvent(event)

    def leaveEvent(self, event):
        QTimer.singleShot(0, self._recheck_hover)
        super().leaveEvent(event)

    def _recheck_hover(self):
        cursor_local = self.mapFromGlobal(QCursor.pos())
        still_inside = self.rect().contains(cursor_local)
        self.btn_delete.set_card_hovered(still_inside)

    def show_context_menu(self, pos):
        menu = QMenu(self)
        menu.setStyleSheet("""
            QMenu { background-color: #1e293b; color: #f8fafc; border: 1px solid #334155; }
            QMenu::item:selected { background-color: #0284c7; }
        """)
        act_open = menu.addAction("🔍 Открыть в редакторе")
        act_select = menu.addAction(
            "⏹️ Снять выделение" if self.is_selected else "☑️ Выделить / Снять выделение"
        )
        act_delete = menu.addAction("🗑️ Убрать из истории")
        act_copy_path = menu.addAction("📋 Скопировать путь")

        action = menu.exec(self.mapToGlobal(pos))
        if action == act_open:
            self.clicked.emit(self.index, Qt.KeyboardModifier.NoModifier)
        elif action == act_select:
            self.set_selected(not self.is_selected)
        elif action == act_delete:
            self.remove_requested.emit(self.index)
        elif action == act_copy_path:
            QApplication.clipboard().setText(self.file_path)


class DynamicHistoryContainer(QWidget):
    resized = Signal()

    def resizeEvent(self, event: QResizeEvent):
        super().resizeEvent(event)
        self.resized.emit()


# =============================================================================
# === ОКНО ПАКЕТНОЙ ОБРАБОТКИ ===
# =============================================================================

class BatchProcessingDialog(QDialog):
    open_in_editor_requested = Signal(str)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("📦 Пакетная обработка изображений (Batch Processing)")
        self.setGeometry(150, 150, 1150, 720)
        self.setMinimumSize(900, 550)

        self.batch_files = []
        self.parsed_data_list = []

        self.init_ui()
        QShortcut(QKeySequence("Escape"), self, self.reject)

    def init_ui(self):
        layout = QVBoxLayout(self)
        layout.setSpacing(12)
        layout.setContentsMargins(16, 16, 16, 16)

        top_group = QGroupBox("Загрузка файлов для пакетной обработки")
        top_layout = QHBoxLayout(top_group)
        top_layout.setSpacing(10)

        self.btn_select_files = QPushButton("📄 Выбрать файлы...")
        self.btn_select_files.clicked.connect(self.select_files)
        top_layout.addWidget(self.btn_select_files)

        self.btn_select_folder = QPushButton("📁 Выбрать папку...")
        self.btn_select_folder.clicked.connect(self.select_folder)
        top_layout.addWidget(self.btn_select_folder)

        self.chk_subfolders = QCheckBox("Включая подпапки")
        self.chk_subfolders.setChecked(True)
        top_layout.addWidget(self.chk_subfolders)

        top_layout.addStretch()

        self.lbl_count = QLabel("Загружено файлов: 0")
        self.lbl_count.setStyleSheet("color: #2bbdf8; font-weight: bold;")
        top_layout.addWidget(self.lbl_count)

        layout.addWidget(top_group)

        self.table = QTableWidget()
        self.table.setColumnCount(7)
        self.table.setHorizontalHeaderLabels([
            "№", "Имя файла", "Метаданные", "Разрешение", "Seed", "Model", "Промпт (фрагмент)"
        ])
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Interactive)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(5, QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(6, QHeaderView.ResizeMode.Stretch)

        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.doubleClicked.connect(self.on_table_double_click)

        layout.addWidget(self.table, stretch=1)

        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.hide()
        layout.addWidget(self.progress_bar)

        actions_group = QGroupBox("Пакетные операции")
        actions_layout = QHBoxLayout(actions_group)
        actions_layout.setSpacing(10)

        self.btn_export_csv = QPushButton("📊 Экспорт в CSV / JSON")
        self.btn_export_csv.setToolTip("Сохранить сводную таблицу всех промптов и настроек")
        self.btn_export_csv.clicked.connect(self.export_batch_catalog)
        actions_layout.addWidget(self.btn_export_csv)

        self.btn_export_txt = QPushButton("📝 Экспорт TXT для всех")
        self.btn_export_txt.setToolTip("Создать отдельный .txt файл с промптом для каждого изображения")
        self.btn_export_txt.clicked.connect(self.export_individual_txts)
        actions_layout.addWidget(self.btn_export_txt)

        self.btn_strip_meta = QPushButton("🛡️ Очистить метаданные")
        self.btn_strip_meta.setToolTip("Сохранить чистые копии файлов без скрытых промптов")
        self.btn_strip_meta.clicked.connect(self.strip_metadata_batch)
        actions_layout.addWidget(self.btn_strip_meta)

        self.btn_load_selected = QPushButton("🔍 Открыть в редакторе")
        self.btn_load_selected.setToolTip("Загрузить выделенный файл в главное окно редактора")
        self.btn_load_selected.clicked.connect(self.load_selected_to_editor)
        actions_layout.addWidget(self.btn_load_selected)

        layout.addWidget(actions_group)

    def select_files(self):
        files, _ = QFileDialog.getOpenFileNames(
            self, "Выберите файлы изображений", "", "Images (*.png *.webp *.jpg *.jpeg)"
        )
        if files:
            self.batch_files = files
            self.run_batch_scan()

    def select_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Выберите папку с изображениями")
        if not folder:
            return
        valid_exts = {".png", ".webp", ".jpg", ".jpeg"}
        found = []
        try:
            if self.chk_subfolders.isChecked():
                for p in Path(folder).rglob("*"):
                    if p.suffix.lower() in valid_exts:
                        found.append(str(p))
            else:
                for p in Path(folder).glob("*"):
                    if p.suffix.lower() in valid_exts:
                        found.append(str(p))
        except Exception:
            pass
        self.batch_files = sorted(found)
        self.run_batch_scan()

    def run_batch_scan(self):
        if not self.batch_files:
            return

        self.parsed_data_list.clear()
        self.table.setRowCount(0)
        total = len(self.batch_files)
        self.progress_bar.setRange(0, total)
        self.progress_bar.setValue(0)
        self.progress_bar.show()

        for idx, file_path in enumerate(self.batch_files):
            data = MetadataParser.parse_image(file_path)
            self.parsed_data_list.append(data)

            row = self.table.rowCount()
            self.table.insertRow(row)

            item_num = QTableWidgetItem(str(idx + 1))
            item_num.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, 0, item_num)

            item_name = QTableWidgetItem(data["filename"])
            item_name.setToolTip(file_path)
            self.table.setItem(row, 1, item_name)

            status_str = "✅ Найдено" if data["has_metadata"] else "❌ Нет"
            item_status = QTableWidgetItem(status_str)
            item_status.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            item_status.setForeground(QColor("#10b981") if data["has_metadata"] else QColor("#ef4444"))
            self.table.setItem(row, 2, item_status)

            w, h = data["size"]
            item_res = QTableWidgetItem(f"{w}x{h}" if w > 0 else "-")
            item_res.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, 3, item_res)

            seed = data["parsed_params"].get("Seed", "-")
            item_seed = QTableWidgetItem(seed)
            item_seed.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, 4, item_seed)

            model = data["parsed_params"].get("Model", data["parsed_params"].get("Model hash", "-"))
            item_model = QTableWidgetItem(model)
            item_model.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, 5, item_model)

            prompt_snip = data["prompt"][:120].replace("\n", " ")
            if len(data["prompt"]) > 120:
                prompt_snip += "..."
            self.table.setItem(row, 6, QTableWidgetItem(prompt_snip))

            self.progress_bar.setValue(idx + 1)
            self.lbl_count.setText(f"Загружено файлов: {idx + 1}/{total}")
            QApplication.processEvents()

        self.progress_bar.hide()

    def export_batch_catalog(self):
        if not self.parsed_data_list:
            return

        file_path, selected_filter = QFileDialog.getSaveFileName(
            self, "Сохранить пакетный каталог", "batch_metadata_catalog",
            "CSV File (*.csv);;JSON File (*.json)"
        )
        if not file_path:
            return

        try:
            if file_path.endswith(".json") or "JSON" in selected_filter:
                if not file_path.endswith(".json"):
                    file_path += ".json"
                with open(file_path, "w", encoding="utf-8") as f:
                    json.dump(self.parsed_data_list, f, ensure_ascii=False, indent=2)
            else:
                if not file_path.endswith(".csv"):
                    file_path += ".csv"
                with open(file_path, "w", encoding="utf-8-sig", newline="") as f:
                    writer = csv.writer(f)
                    writer.writerow([
                        "Filename", "File Path", "Has Metadata", "Prompt",
                        "Negative Prompt", "Steps", "Sampler", "CFG scale",
                        "Seed", "Model", "Width", "Height"
                    ])
                    for item in self.parsed_data_list:
                        kv = item["parsed_params"]
                        w, h = item["size"]
                        writer.writerow([
                            item["filename"], item["file_path"], item["has_metadata"],
                            item["prompt"], item["negative_prompt"],
                            kv.get("Steps", ""), kv.get("Sampler", ""),
                            kv.get("CFG scale", ""), kv.get("Seed", ""),
                            kv.get("Model", ""), w, h
                        ])
        except Exception:
            pass

    def export_individual_txts(self):
        if not self.parsed_data_list:
            return

        output_dir = QFileDialog.getExistingDirectory(self, "Выберите папку для сохранения .txt файлов")
        if not output_dir:
            return

        name_counter = {}
        for item in self.parsed_data_list:
            if not item["prompt"]:
                continue
            stem = Path(item["filename"]).stem or "image"
            if stem in name_counter:
                name_counter[stem] += 1
                unique_stem = f"{stem}_{name_counter[stem]}"
            else:
                name_counter[stem] = 0
                unique_stem = stem

            txt_path = os.path.join(output_dir, f"{unique_stem}.txt")
            try:
                with open(txt_path, "w", encoding="utf-8") as f:
                    f.write(item["prompt"])
            except Exception:
                pass

    def strip_metadata_batch(self):
        if not self.parsed_data_list:
            return

        output_dir = QFileDialog.getExistingDirectory(self, "Выберите папку для очищенных изображений")
        if not output_dir:
            return

        for item in self.parsed_data_list:
            try:
                src = item["file_path"]
                dst = os.path.join(output_dir, f"clean_{item['filename']}")
                if HAS_PIL:
                    with Image.open(src) as img:
                        data = list(img.getdata())
                        clean_img = Image.new(img.mode, img.size)
                        clean_img.putdata(data)
                        clean_img.save(dst)
                else:
                    shutil.copy2(src, dst)
            except Exception:
                pass

    def load_selected_to_editor(self):
        selected_rows = self.table.selectionModel().selectedRows()
        if not selected_rows:
            return
        row = selected_rows[0].row()
        if row < len(self.parsed_data_list):
            self.open_in_editor_requested.emit(self.parsed_data_list[row]["file_path"])
            self.accept()

    def on_table_double_click(self, index):
        row = index.row()
        if row < len(self.parsed_data_list):
            self.open_in_editor_requested.emit(self.parsed_data_list[row]["file_path"])
            self.accept()


# =============================================================================
# === ГЛАВНОЕ ОКНО ===
# =============================================================================

class TipEditorForgeNeoApp(QMainWindow):
    """Главное окно Tip Editor - Forge Neo Edition v9.5."""

    def __init__(self):
        super().__init__()
        self.setWindowTitle("Tip Editor - Forge Neo Edition v9.5")
        self.setGeometry(100, 100, 1680, 980)

        self.settings = QSettings("ForgeNeoTools", "TipEditorNeoEditionV9")
        self.history_paths = []
        self.thumb_cards = []
        self.current_thumb_size = 132
        self.current_file_path = None
        self.current_metadata = {}
        self.last_selected_index = -1
        self._last_columns = -1

        self.init_theme_styles()
        self.init_ui()
        self.setAcceptDrops(True)
        self.load_saved_settings()

    def init_theme_styles(self):
        self.setStyleSheet("""
            QMainWindow { background-color: #0b0f19; }
            QWidget { font-family: 'Segoe UI', 'Inter', 'Microsoft YaHei', 'SimSun',
                                  'Malgun Gothic', 'Meiryo', 'Arial Unicode MS',
                                  -apple-system, sans-serif; }

            QLabel { color: #94a3b8; font-size: 13px; font-weight: 600; }
            .SectionHeader { color: #2bbdf8; font-size: 12px; font-weight: 700; letter-spacing: 0.5px; }

            QTextEdit {
                background-color: #121826;
                color: #f1f5f9;
                border: 1px solid #1e293b;
                border-radius: 8px;
                padding: 8px;
                selection-background-color: #0284c7;
            }
            QTextEdit:focus { border: 1px solid #2bbdf8; }

            QPushButton {
                background-color: #1e293b;
                color: #f8fafc;
                border: 1px solid #334155;
                border-radius: 6px;
                padding: 6px 14px;
                font-size: 13px;
                font-weight: 500;
            }
            QPushButton:hover { background-color: #334155; border-color: #2bbdf8; }
            QPushButton:pressed { background-color: #0284c7; }

            QComboBox, QSpinBox, QLineEdit {
                background-color: #121826;
                color: #f8fafc;
                border: 1px solid #334155;
                border-radius: 6px;
                padding: 5px 8px;
                font-size: 13px;
            }
            QComboBox:hover, QSpinBox:hover, QLineEdit:hover { border-color: #2bbdf8; }
            QComboBox QAbstractItemView {
                background-color: #1e293b;
                color: #f8fafc;
                selection-background-color: #0284c7;
                border: 1px solid #334155;
            }

            #dropZone {
                border: 2px dashed #2bbdf8;
                border-radius: 10px;
                background-color: #121826;
            }
            #dropZone:hover { background-color: #1e293b; border-color: #38bdf8; }
            #dropZoneLabel { color: #2bbdf8; font-size: 13px; font-weight: 600; }

            #imagePreview {
                background-color: #070a12;
                border: 1px solid #1e293b;
                border-radius: 10px;
            }

            QSplitter::handle:horizontal {
                background-color: #0f172a;
                border-left: 1px solid #1e293b;
                border-right: 1px solid #1e293b;
                width: 6px;
            }
            QSplitter::handle:horizontal:hover {
                background-color: #2bbdf8;
                border-left: 1px solid #2bbdf8;
                border-right: 1px solid #2bbdf8;
            }
            QSplitter::handle:horizontal:pressed { background-color: #0284c7; }

            QScrollArea { border: none; background-color: transparent; }

            QSlider::groove:horizontal {
                border: 1px solid #334155;
                height: 6px;
                background: #121826;
                border-radius: 3px;
            }
            QSlider::handle:horizontal {
                background: #2bbdf8;
                border: 1px solid #2bbdf8;
                width: 14px;
                margin: -4px 0;
                border-radius: 7px;
            }
            QSlider::handle:horizontal:hover { background: #38bdf8; }

            QStatusBar {
                background-color: #070a12;
                color: #64748b;
                border-top: 1px solid #1e293b;
            }

            QTableWidget {
                background-color: #121826;
                color: #f8fafc;
                gridline-color: #1e293b;
                border: 1px solid #1e293b;
                border-radius: 6px;
            }
            QHeaderView::section {
                background-color: #1e293b;
                color: #94a3b8;
                font-weight: bold;
                border: none;
                padding: 6px;
            }

            QGroupBox {
                border: 1px solid #1e293b;
                border-radius: 8px;
                margin-top: 10px;
                font-weight: bold;
                color: #2bbdf8;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px;
            }
        """)

    def init_ui(self):
        main_widget = QWidget()
        self.setCentralWidget(main_widget)

        window_layout = QVBoxLayout(main_widget)
        window_layout.setSpacing(12)
        window_layout.setContentsMargins(16, 16, 16, 16)

        top_bar = QHBoxLayout()
        top_bar.setSpacing(12)

        tools_layout = QHBoxLayout()
        tools_layout.setSpacing(8)

        self.btn_open = QPushButton("📁 Открыть")
        self.btn_open.clicked.connect(self.open_file_dialog)
        tools_layout.addWidget(self.btn_open)

        self.btn_batch = QPushButton("📦 Пакетная обработка")
        self.btn_batch.setStyleSheet(
            "background-color: #0284c7; border-color: #2bbdf8; font-weight: bold;"
        )
        self.btn_batch.setToolTip("Запустить модуль пакетной обработки (Ctrl+B)")
        self.btn_batch.clicked.connect(self.open_batch_dialog)
        tools_layout.addWidget(self.btn_batch)

        self.btn_export = QPushButton("💾 Экспорт")
        self.btn_export.setToolTip("Сохранить метаданные текущего файла в TXT или JSON")
        self.btn_export.clicked.connect(self.export_metadata_dialog)
        tools_layout.addWidget(self.btn_export)

        tools_layout.addSpacing(8)
        tools_layout.addWidget(QLabel("Шрифт:"))
        self.combo_font = QComboBox()
        self.combo_font.setMaxVisibleItems(16)
        self.combo_font.currentIndexChanged.connect(self.on_font_selected)
        tools_layout.addWidget(self.combo_font)

        tools_layout.addWidget(QLabel("Размер:"))
        self.spin_size = QSpinBox()
        self.spin_size.setRange(8, 48)
        self.spin_size.setValue(13)
        self.spin_size.valueChanged.connect(self.update_text_font)
        tools_layout.addWidget(self.spin_size)

        tools_layout.addSpacing(8)
        tools_layout.addWidget(QLabel("Плитки:"))
        self.slider_thumb_size = QSlider(Qt.Orientation.Horizontal)
        self.slider_thumb_size.setRange(80, 320)
        self.slider_thumb_size.setValue(self.current_thumb_size)
        self.slider_thumb_size.setFixedWidth(100)
        self.slider_thumb_size.valueChanged.connect(self.on_thumb_size_slider_changed)
        tools_layout.addWidget(self.slider_thumb_size)

        top_bar.addLayout(tools_layout)

        self.drop_zone = QFrame()
        self.drop_zone.setObjectName("dropZone")
        drop_layout = QVBoxLayout(self.drop_zone)
        drop_layout.setContentsMargins(16, 6, 16, 6)
        self.drop_label = QLabel("Перетащите сюда изображение или папку (PNG, WEBP, JPEG)")
        self.drop_label.setObjectName("dropZoneLabel")
        self.drop_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        drop_layout.addWidget(self.drop_label)
        top_bar.addWidget(self.drop_zone, stretch=1)

        window_layout.addLayout(top_bar)

        self.global_splitter = QSplitter(Qt.Orientation.Horizontal)

        left_container = QWidget()
        left_layout = QVBoxLayout(left_container)
        left_layout.setContentsMargins(0, 0, 0, 0)

        self.main_splitter = QSplitter(Qt.Orientation.Horizontal)

        # --- Превью ---
        self.preview_container = QWidget()
        preview_layout = QVBoxLayout(self.preview_container)
        preview_layout.setContentsMargins(0, 0, 0, 0)
        preview_layout.setSpacing(6)

        self.image_preview = QLabel()
        self.image_preview.setObjectName("imagePreview")
        self.image_preview.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.image_preview.setMinimumSize(280, 420)
        self.image_preview.setScaledContents(False)
        self.image_preview.setText("Превью изображения")
        preview_layout.addWidget(self.image_preview, stretch=1)

        self.lbl_img_info = QLabel("Разрешение: - | Формат: - | Размер: -")
        self.lbl_img_info.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.lbl_img_info.setStyleSheet("color: #64748b; font-size: 11px;")
        preview_layout.addWidget(self.lbl_img_info)

        # --- Поля ---
        self.fields_container = QWidget()
        fields_layout = QVBoxLayout(self.fields_container)
        fields_layout.setContentsMargins(0, 0, 0, 0)
        fields_layout.setSpacing(6)

        lbl_p_header = QLabel("ПОЛОЖИТЕЛЬНЫЙ ПРОМПТ (PROMPT)")
        lbl_p_header.setProperty("class", "SectionHeader")
        fields_layout.addWidget(lbl_p_header)

        self.txt_prompt = QTextEdit()
        fields_layout.addWidget(self.txt_prompt, stretch=2)

        p_tools = QHBoxLayout()
        self.lbl_p_stats = QLabel("Слов: 0 | Символов: 0")
        self.lbl_p_stats.setStyleSheet("color: #64748b; font-size: 11px;")
        p_tools.addWidget(self.lbl_p_stats)

        btn_clean_prompt = QPushButton("📄 Одним абзацем")
        btn_clean_prompt.setToolTip("Скомпоновать промпт в один абзац без переносов строк")
        btn_clean_prompt.setStyleSheet("padding: 2px 10px; font-size: 11px;")
        btn_clean_prompt.clicked.connect(self.clean_current_prompt)
        p_tools.addWidget(btn_clean_prompt)

        p_tools.addStretch()

        self.btn_save_p = SaveIconButton("Сохранить отредактированный положительный промпт в файл")
        self.btn_save_p.clicked.connect(self.save_edited_metadata_to_file)
        p_tools.addWidget(self.btn_save_p)

        self.btn_copy_p = CopyIconButton("Копировать положительный промпт")
        self.btn_copy_p.clicked.connect(
            lambda: self.copy_to_clipboard(self.txt_prompt.toPlainText(), self.btn_copy_p)
        )
        p_tools.addWidget(self.btn_copy_p)
        fields_layout.addLayout(p_tools)

        lbl_n_header = QLabel("НЕГАТИВНЫЙ ПРОМПТ (NEGATIVE PROMPT)")
        lbl_n_header.setProperty("class", "SectionHeader")
        fields_layout.addWidget(lbl_n_header)

        self.txt_neg_prompt = QTextEdit()
        self.txt_neg_prompt.setMaximumHeight(110)
        fields_layout.addWidget(self.txt_neg_prompt, stretch=1)

        n_tools = QHBoxLayout()
        self.lbl_n_stats = QLabel("Слов: 0 | Символов: 0")
        self.lbl_n_stats.setStyleSheet("color: #64748b; font-size: 11px;")
        n_tools.addWidget(self.lbl_n_stats)
        n_tools.addStretch()

        self.btn_save_n = SaveIconButton("Сохранить отредактированный негативный промпт в файл")
        self.btn_save_n.clicked.connect(self.save_edited_metadata_to_file)
        n_tools.addWidget(self.btn_save_n)

        self.btn_copy_n = CopyIconButton("Копировать негативный промпт")
        self.btn_copy_n.clicked.connect(
            lambda: self.copy_to_clipboard(self.txt_neg_prompt.toPlainText(), self.btn_copy_n)
        )
        n_tools.addWidget(self.btn_copy_n)
        fields_layout.addLayout(n_tools)

        lbl_s_header = QLabel("ПАРАМЕТРЫ ГЕНЕРАЦИИ (STEPS, SAMPLER, SEED...)")
        lbl_s_header.setProperty("class", "SectionHeader")
        fields_layout.addWidget(lbl_s_header)

        self.txt_settings = QTextEdit()
        self.txt_settings.setMaximumHeight(120)
        fields_layout.addWidget(self.txt_settings, stretch=1)

        s_tools = QHBoxLayout()
        s_tools.addStretch()

        self.btn_save_s = SaveIconButton("Сохранить отредактированные параметры генерации в файл")
        self.btn_save_s.clicked.connect(self.save_edited_metadata_to_file)
        s_tools.addWidget(self.btn_save_s)

        self.btn_copy_s = CopyIconButton("Копировать параметры генерации")
        self.btn_copy_s.clicked.connect(
            lambda: self.copy_to_clipboard(self.txt_settings.toPlainText(), self.btn_copy_s)
        )
        s_tools.addWidget(self.btn_copy_s)
        fields_layout.addLayout(s_tools)

        self.txt_prompt.textChanged.connect(self.update_prompt_stats)
        self.txt_neg_prompt.textChanged.connect(self.update_prompt_stats)

        self.main_splitter.addWidget(self.preview_container)
        self.main_splitter.addWidget(self.fields_container)
        self.main_splitter.setSizes([480, 640])
        self.main_splitter.splitterMoved.connect(self.on_splitter_moved)

        left_layout.addWidget(self.main_splitter)

        # --- История ---
        self.history_container = DynamicHistoryContainer(self)
        self.history_container.setMinimumWidth(180)
        self.history_container.resized.connect(self.rearrange_history_grid)

        history_layout = QVBoxLayout(self.history_container)
        history_layout.setContentsMargins(0, 0, 0, 0)
        history_layout.setSpacing(6)

        hist_header = QHBoxLayout()
        self.lbl_hist_count = QLabel("ИСТОРИЯ (0/500)")
        self.lbl_hist_count.setProperty("class", "SectionHeader")
        hist_header.addWidget(self.lbl_hist_count)
        hist_header.addStretch()

        btn_save_selected = QPushButton("💾 Сохранить выделенные")
        btn_save_selected.setToolTip(
            "Экспортировать положительные подсказки выделенных миниатюр в один .txt "
            "файл (по 1 абзацу, через пустую строку)"
        )
        btn_save_selected.setStyleSheet(
            "padding: 2px 8px; font-size: 11px; background-color: #0284c7; border-color: #2bbdf8;"
        )
        btn_save_selected.clicked.connect(self.save_selected_prompts_to_file)
        hist_header.addWidget(btn_save_selected)

        btn_clear_hist = QPushButton("Очистить все")
        btn_clear_hist.setToolTip("Очистить полностью всю историю (до 500 слотов)")
        btn_clear_hist.setStyleSheet("padding: 2px 8px; font-size: 11px;")
        btn_clear_hist.clicked.connect(self.clear_history)
        hist_header.addWidget(btn_clear_hist)

        history_layout.addLayout(hist_header)

        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_widget = QWidget()
        self.scroll_widget.setStyleSheet("background-color: transparent;")

        self.grid_history_layout = QGridLayout(self.scroll_widget)
        self.grid_history_layout.setSpacing(6)
        self.grid_history_layout.setContentsMargins(4, 0, 4, 4)
        self.grid_history_layout.setAlignment(Qt.AlignmentFlag.AlignTop)

        for i in range(500):
            card = HistoryCardWidget(i, self)
            card.clicked.connect(self.handle_card_click)
            card.remove_requested.connect(self.remove_from_history)
            card.reorder_requested.connect(self.reorder_history_item)
            card.hide()
            self.thumb_cards.append(card)

        self.scroll_area.setWidget(self.scroll_widget)
        history_layout.addWidget(self.scroll_area)

        self.global_splitter.addWidget(left_container)
        self.global_splitter.addWidget(self.history_container)
        self.global_splitter.setSizes([1100, 500])

        window_layout.addWidget(self.global_splitter, stretch=1)

        self.status_bar = QStatusBar()
        self.setStatusBar(self.status_bar)
        self.status_bar.showMessage(
            f"Готово. Qt: {QT_LIB} | Pillow: {'Подключен' if HAS_PIL else 'Отсутствует'}"
        )

        QShortcut(QKeySequence("Ctrl+O"), self, self.open_file_dialog)
        QShortcut(QKeySequence("Ctrl+B"), self, self.open_batch_dialog)
        QShortcut(QKeySequence("Ctrl+S"), self, self.export_metadata_dialog)

    # --------------------------------------------- СОХРАНЕНИЕ МЕТАДАННЫХ

    def save_edited_metadata_to_file(self):
        if not self.current_file_path or not os.path.exists(self.current_file_path):
            self.status_bar.showMessage("Ошибка: файл изображения не выбран или не существует", 4000)
            return

        p_text = self.txt_prompt.toPlainText().strip()
        n_text = self.txt_neg_prompt.toPlainText().strip()
        s_text = self.txt_settings.toPlainText().strip()

        if p_text == "В данном изображении метаданные генерации затерты или не распознаны.":
            p_text = ""

        combined = p_text
        if n_text:
            combined += f"\nNegative prompt: {n_text}"
        if s_text:
            combined += f"\n{s_text}"

        try:
            if HAS_PIL:
                ext = Path(self.current_file_path).suffix.lower()
                if ext == ".png":
                    with Image.open(self.current_file_path) as img:
                        png_info = PngInfo()
                        png_info.add_text("parameters", combined)
                        img.save(self.current_file_path, pnginfo=png_info)
                elif ext in (".jpg", ".jpeg", ".webp"):
                    with Image.open(self.current_file_path) as img:
                        exif_data = img.getexif()
                        exif_data[37510] = b'UNICODE\x00' + combined.encode('utf-16le')
                        img.save(self.current_file_path, exif=exif_data)

            MetadataParser.invalidate_cache(self.current_file_path)
            invalidate_pixmap_cache(self.current_file_path)

            self.btn_save_p.animate_saved()
            self.btn_save_n.animate_saved()
            self.btn_save_s.animate_saved()

            self.status_bar.showMessage(
                f"Отредактированные метаданные сохранены: {os.path.basename(self.current_file_path)}",
                4000
            )
        except Exception as e:
            self.status_bar.showMessage(f"Ошибка при сохранении метаданных: {e}", 4000)

    # ------------------------------------- ПАКЕТНЫЙ ЭКСПОРТ ПОДСКАЗОК

    def save_selected_prompts_to_file(self):
        selected_cards = [c for c in self.thumb_cards
                          if c.isVisible() and c.is_selected and c.file_path]

        if not selected_cards:
            selected_cards = [c for c in self.thumb_cards
                              if c.isVisible() and c.file_path]

        if not selected_cards:
            self.status_bar.showMessage("Инфо: в истории нет файлов для сохранения подсказок.", 4000)
            return

        file_path, _ = QFileDialog.getSaveFileName(
            self, "Сохранить выделенные подсказки", "selected_prompts.txt", "Text Files (*.txt)"
        )
        if not file_path:
            return

        try:
            formatted = []
            for card in selected_cards:
                meta = MetadataParser.parse_image(card.file_path)
                p_text = meta.get("prompt", "").strip()
                if not p_text or p_text == "В данном изображении метаданные генерации затерты или не распознаны.":
                    continue
                one_line = p_text.replace("\n", " ").replace("\r", " ")
                one_line = re.sub(r'\s*,\s*', ', ', one_line)
                one_line = re.sub(r',(\s*,)+', ',', one_line)
                one_line = re.sub(r'\s+', ' ', one_line).strip(', ')
                if one_line:
                    formatted.append(one_line)

            if not formatted:
                self.status_bar.showMessage(
                    "Внимание: ни одна из выделенных миниатюр не содержит положительного промпта.", 4000
                )
                return

            combined = "\n\n".join(formatted)

            with open(file_path, "w", encoding="utf-8") as f:
                f.write(combined)

            self.status_bar.showMessage(
                f"Успешно сохранено подсказок: {len(formatted)} → {os.path.basename(file_path)}",
                4000
            )
        except Exception as e:
            self.status_bar.showMessage(f"Ошибка экспорта выделенных подсказок: {e}", 4000)

    # ----------------------------------------------- ВЫДЕЛЕНИЕ / КЛИК

    def handle_card_click(self, index: int, modifiers):
        if index < 0 or index >= len(self.history_paths):
            return

        card = self.thumb_cards[index]

        if modifiers & Qt.KeyboardModifier.ControlModifier:
            card.set_selected(not card.is_selected)
            self.last_selected_index = index
        elif modifiers & Qt.KeyboardModifier.ShiftModifier and self.last_selected_index != -1:
            start = min(self.last_selected_index, index)
            end = max(self.last_selected_index, index)
            for i in range(start, end + 1):
                if i < len(self.history_paths):
                    self.thumb_cards[i].set_selected(True)
        else:
            for i, c in enumerate(self.thumb_cards):
                c.set_selected(i == index)
            self.last_selected_index = index

        path = self.history_paths[index]
        if os.path.exists(path):
            self.process_image(path)

    # ------------------------------------------------------ ИСТОРИЯ

    def add_to_history(self, file_path: str):
        if not file_path or not os.path.exists(file_path):
            return
        if file_path not in self.history_paths:
            if len(self.history_paths) >= 500:
                self.history_paths.pop(0)
            self.history_paths.append(file_path)
        self.save_app_settings()
        self.update_history_ui()
        self.rearrange_history_grid()

    def remove_from_history(self, index: int):
        if 0 <= index < len(self.history_paths):
            deleted = self.history_paths.pop(index)
            self.save_app_settings()
            self.update_history_ui()
            self.rearrange_history_grid()
            self.status_bar.showMessage(
                f"Миниатюра #{index + 1} убрана из истории: {os.path.basename(deleted)}", 3000
            )

    def reorder_history_item(self, src_idx: int, dst_idx: int):
        if (src_idx != dst_idx
                and 0 <= src_idx < len(self.history_paths)
                and 0 <= dst_idx < len(self.history_paths)):
            moved = self.history_paths.pop(src_idx)
            self.history_paths.insert(dst_idx, moved)
            self.save_app_settings()
            self.update_history_ui()
            self.rearrange_history_grid()
            self.status_bar.showMessage(
                f"Слот #{src_idx + 1} перемещен на позицию #{dst_idx + 1}", 3000
            )

    def update_history_ui(self):
        count = len(self.history_paths)
        self.lbl_hist_count.setText(f"ИСТОРИЯ ({count}/500)")

        for i in range(500):
            if i < count:
                self.thumb_cards[i].set_data(self.history_paths[i], self.current_thumb_size, i + 1)
                self.thumb_cards[i].show()
            else:
                self.thumb_cards[i].hide()

    def clear_history(self):
        self.history_paths.clear()
        self.save_app_settings()
        self.update_history_ui()
        self.rearrange_history_grid()
        self.status_bar.showMessage("История очищена", 3000)

    # --------------------------------------------------- ПРОСМОТР

    def process_image(self, file_path: str):
        try:
            self.current_file_path = file_path
            self.clear_fields(clear_preview=False)
            self.resize_preview_image(file_path)

            metadata = MetadataParser.parse_image(file_path)
            self.current_metadata = metadata

            filename = os.path.basename(file_path)
            w, h = metadata["size"]
            size_kb = metadata["file_size_bytes"] / 1024
            size_str = f"{size_kb:.1f} KB" if size_kb < 1024 else f"{size_kb/1024:.2f} MB"
            fmt = metadata["format"] or Path(file_path).suffix.upper().replace(".", "")
            self.lbl_img_info.setText(f"Разрешение: {w}x{h} px | Формат: {fmt} | Размер: {size_str}")

            if metadata["has_metadata"]:
                self.txt_prompt.setPlainText(metadata["prompt"])
                self.txt_neg_prompt.setPlainText(metadata["negative_prompt"])
                self.txt_settings.setPlainText(metadata["settings_raw"])
                self.drop_label.setText(f"Успешно прочитан файл: {filename}")
                self.setWindowTitle(f"Tip Editor Neo - {filename}")
                self.status_bar.showMessage(f"Файл успешно загружен: {file_path}")
            else:
                self.txt_prompt.setPlainText(
                    "В данном изображении метаданные генерации затерты или не распознаны."
                )
                self.drop_label.setText("Метаданные генерации не найдены.")
                self.setWindowTitle("Tip Editor - Forge Neo Edition v9.5")
                self.status_bar.showMessage("Инфо: в изображении отсутствуют скрытые метаданные.")
        except Exception as e:
            self.status_bar.showMessage(f"Ошибка при обработке файла: {e}")

    def clean_current_prompt(self):
        p_text = self.txt_prompt.toPlainText()
        if p_text and p_text != "В данном изображении метаданные генерации затерты или не распознаны.":
            cleaned = p_text.replace("\n", " ").replace("\r", " ")
            cleaned = re.sub(r'\s*,\s*', ', ', cleaned)
            cleaned = re.sub(r',(\s*,)+', ',', cleaned)
            cleaned = re.sub(r'\s+', ' ', cleaned).strip(', ')
            self.txt_prompt.setPlainText(cleaned)
            self.status_bar.showMessage("Промпт скомпонован в один абзац без переносов", 3000)

    def update_prompt_stats(self):
        p_text = self.txt_prompt.toPlainText().strip()
        if p_text == "В данном изображении метаданные генерации затерты или не распознаны.":
            self.lbl_p_stats.setText("Слов: 0 | Символов: 0")
        else:
            words = len(p_text.split()) if p_text else 0
            self.lbl_p_stats.setText(f"Слов: {words} | Символов: {len(p_text)}")

        n_text = self.txt_neg_prompt.toPlainText().strip()
        n_words = len(n_text.split()) if n_text else 0
        self.lbl_n_stats.setText(f"Слов: {n_words} | Символов: {len(n_text)}")

    def on_splitter_moved(self, pos, index):
        if self.current_file_path:
            self.resize_preview_image(self.current_file_path)

    # --------------------------------------------------- СЕТКА

    def rearrange_history_grid(self):
        if not self.thumb_cards:
            return

        available_width = self.scroll_area.viewport().width()
        spacing = self.grid_history_layout.spacing()
        margins = self.grid_history_layout.contentsMargins()

        net_width = available_width - margins.left() - margins.right()
        cell_w = self.current_thumb_size + spacing

        columns = max(1, min(12, net_width // cell_w))
        if net_width % cell_w >= self.current_thumb_size:
            columns = max(1, min(12, columns + 1))

        if columns == self._last_columns:
            return
        self._last_columns = columns

        for i, card in enumerate(self.thumb_cards):
            self.grid_history_layout.removeWidget(card)
            self.grid_history_layout.addWidget(card, i // columns, i % columns)

    def on_thumb_size_slider_changed(self, value):
        self.current_thumb_size = value
        self._last_columns = -1
        self.update_history_ui()
        self.rearrange_history_grid()

    # --------------------------------------------------- ШРИФТЫ

    def rebuild_font_list(self, active_family=None):
        self.combo_font.blockSignals(True)
        self.combo_font.clear()

        all_families = QFontDatabase.families()
        rolling_history = self.settings.value("rolling_font_history_v2", [])
        if not isinstance(rolling_history, list):
            rolling_history = []

        font_stats = {}
        for family in rolling_history:
            if family and family in all_families:
                font_stats[family] = font_stats.get(family, 0) + 1

        sorted_top = sorted(font_stats.items(), key=lambda item: item[1], reverse=True)
        top_7 = [item[0] for item in sorted_top[:7]]
        inserted = set()

        for family in top_7:
            self.combo_font.addItem(f"⭐ {family}", family)
            inserted.add(family)

        if top_7:
            self.combo_font.addItem("-----------------------------------", "---")

        for family in sorted(all_families):
            if family not in inserted:
                self.combo_font.addItem(family, family)

        if active_family:
            for index in range(self.combo_font.count()):
                if self.combo_font.itemData(index) == active_family:
                    self.combo_font.setCurrentIndex(index)
                    break

        self.combo_font.blockSignals(False)

    def on_font_selected(self, index: int):
        if index < 0:
            return
        family = self.combo_font.itemData(index)
        if not family or family == "---":
            return

        rolling_history = self.settings.value("rolling_font_history_v2", [])
        if not isinstance(rolling_history, list):
            rolling_history = []

        rolling_history.append(family)
        if len(rolling_history) > 50:
            rolling_history.pop(0)

        self.settings.setValue("rolling_font_history_v2", rolling_history)
        self.update_text_font()

    def update_text_font(self):
        current_index = self.combo_font.currentIndex()
        family = self.combo_font.itemData(current_index)

        if not family or family == "---":
            family = self.combo_font.currentText().replace("⭐ ", "").strip()
        if not family or family.startswith("---"):
            family = "Segoe UI"

        font_size = self.spin_size.value()
        new_font = QFont(family, font_size)

        for txt_edit in (self.txt_prompt, self.txt_neg_prompt, self.txt_settings):
            txt_edit.setFont(new_font)
            txt_edit.document().setDefaultFont(new_font)
            txt_edit.setStyleSheet(
                f"background-color: #121826; color: #f1f5f9; border: 1px solid #1e293b; "
                f"border-radius: 8px; padding: 8px; "
                f"font-family: '{family}', 'Segoe UI', 'Microsoft YaHei', 'SimSun', "
                f"'Malgun Gothic', 'Meiryo', 'Arial Unicode MS', monospace; "
                f"font-size: {font_size}pt;"
            )

        self.settings.setValue("saved_font_family_fixed", family)
        self.settings.setValue("saved_font_size_fixed", font_size)

    # --------------------------------------------------- НАСТРОЙКИ

    def load_saved_settings(self):
        saved_family = self.settings.value("saved_font_family_fixed", "Segoe UI")
        saved_size = self.settings.value("saved_font_size_fixed", 13, type=int)

        self.spin_size.blockSignals(True)
        self.spin_size.setValue(saved_size)
        self.spin_size.blockSignals(False)

        self.rebuild_font_list(active_family=saved_family)
        self.update_text_font()

        saved_history = self.settings.value("history_file_paths", [])
        if isinstance(saved_history, list):
            self.history_paths = [p for p in saved_history if os.path.exists(p)][:500]
            self.update_history_ui()
            self.rearrange_history_grid()

    def save_app_settings(self):
        self.settings.setValue("history_file_paths", self.history_paths)

    # --------------------------------------------------- DRAG & DROP

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent):
        urls = event.mimeData().urls()
        if not urls:
            return

        valid_exts = {".png", ".webp", ".jpg", ".jpeg"}
        added_files = []

        for url in urls:
            path_str = url.toLocalFile()
            if not path_str or not os.path.exists(path_str):
                continue
            if os.path.isfile(path_str) and Path(path_str).suffix.lower() in valid_exts:
                added_files.append(path_str)
            elif os.path.isdir(path_str):
                try:
                    for p in Path(path_str).rglob("*"):
                        if p.suffix.lower() in valid_exts:
                            added_files.append(str(p))
                except Exception:
                    pass

        if not added_files:
            return

        for file_p in sorted(added_files):
            if file_p not in self.history_paths and len(self.history_paths) < 500:
                self.history_paths.append(file_p)

        self.save_app_settings()
        self.update_history_ui()
        self.rearrange_history_grid()

        self.process_image(sorted(added_files)[0])
        self.status_bar.showMessage(f"Добавлено файлов: {len(added_files)}", 4000)

    # --------------------------------------------------- ДИАЛОГИ

    def open_file_dialog(self):
        files, _ = QFileDialog.getOpenFileNames(
            self, "Выберите изображения", "", "Images (*.png *.webp *.jpg *.jpeg)"
        )
        if files:
            for f in files:
                self.add_to_history(f)
            self.process_image(files[0])

    def open_batch_dialog(self):
        dialog = BatchProcessingDialog(self)
        dialog.open_in_editor_requested.connect(self.open_file_from_path)
        dialog.exec()

    def open_file_from_path(self, file_path: str):
        if file_path and os.path.exists(file_path):
            self.add_to_history(file_path)
            self.process_image(file_path)

    def clear_fields(self, clear_preview=True):
        self.txt_prompt.clear()
        self.txt_neg_prompt.clear()
        self.txt_settings.clear()
        self.lbl_img_info.setText("Разрешение: - | Формат: - | Размер: -")
        if clear_preview:
            self.image_preview.clear()
            self.image_preview.setText("Превью изображения")

    def resize_preview_image(self, file_path: str):
        pixmap = get_cached_pixmap(file_path)
        if not pixmap.isNull():
            scaled = pixmap.scaled(
                self.image_preview.size(),
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
            self.image_preview.setPixmap(scaled)

    def copy_to_clipboard(self, text, btn: CopyIconButton = None):
        if text and text != "В данном изображении метаданные генерации затерты или не распознаны.":
            QApplication.clipboard().setText(text)
            if btn:
                btn.animate_copied()
            self.status_bar.showMessage("Скопировано в буфер обмена!", 3000)

    def export_metadata_dialog(self):
        if not self.current_file_path or not self.current_metadata:
            self.status_bar.showMessage("Инфо: сначала откройте файл с метаданными.", 3000)
            return

        file_path, selected_filter = QFileDialog.getSaveFileName(
            self, "Экспорт метаданных", f"{Path(self.current_file_path).stem}_metadata",
            "Text File (*.txt);;JSON File (*.json)"
        )
        if not file_path:
            return

        try:
            if file_path.endswith(".json") or "JSON" in selected_filter:
                if not file_path.endswith(".json"):
                    file_path += ".json"
                with open(file_path, "w", encoding="utf-8") as f:
                    json.dump(self.current_metadata, f, ensure_ascii=False, indent=2)
            else:
                if not file_path.endswith(".txt"):
                    file_path += ".txt"
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(f"=== ПРОМПТ ===\n{self.current_metadata.get('prompt', '')}\n\n")
                    f.write(f"=== НЕГАТИВНЫЙ ПРОМПТ ===\n{self.current_metadata.get('negative_prompt', '')}\n\n")
                    f.write(f"=== ПАРАМЕТРЫ ГЕНЕРАЦИИ ===\n{self.current_metadata.get('settings_raw', '')}\n")
            self.status_bar.showMessage(f"Экспортировано: {file_path}", 4000)
        except Exception as e:
            self.status_bar.showMessage(f"Ошибка сохранения: {e}", 4000)


# =============================================================================

if __name__ == "__main__":
    app = QApplication(sys.argv)
    try:
        app.setStyle("Fusion")
    except Exception:
        pass
    window = TipEditorForgeNeoApp()
    window.show()
    sys.exit(app.exec())