from __future__ import annotations

import configparser
import json
import os
import struct
import threading
import tkinter as tk
import urllib.error
import urllib.request
import zlib
from dataclasses import asdict, dataclass
from tkinter import filedialog, messagebox, ttk

try:
    import zstandard as zstd
except ImportError:  # pragma: no cover - optional dependency
    zstd = None


MAGIC = 0x414B504B
SUPPORTED_VERSIONS = {(4, 0), (4, 1), (4, 2), (2, 0)}

FEATURE_EXTRA_DATA = 0x0004
FEATURE_ENCRYPT_ENTRY_LIST = 0x0008
FEATURE_EXTRA_INTEGER = 0x0010
FEATURE_HAS_CHUNK_CONTENT_TABLE = 0x0020
KNOWN_FEATURE_FLAGS = (
    FEATURE_EXTRA_DATA
    | FEATURE_ENCRYPT_ENTRY_LIST
    | FEATURE_EXTRA_INTEGER
    | FEATURE_HAS_CHUNK_CONTENT_TABLE
)

COMPRESSION_NONE = 0
COMPRESSION_DEFLATE = 1
COMPRESSION_ZSTD = 2

OFFSET_MAIN_CONTENTS = 0
OFFSET_CHUNK_CONTENTS = 1

MANIFEST_PATH = "__MANIFEST/MANIFEST.TXT"
UNKNOWN_PREFIX = "__unknown"
INVALID_PATH_CHARS = '<>:"\\|?*'

HEADER_STRUCT = struct.Struct("<IBBhiI")
ENTRY_V4_STRUCT = struct.Struct("<IIqqqqq")
ENTRY_V2_STRUCT = struct.Struct("<qqII")
CHUNK_ENTRY_STRUCT = struct.Struct("<II")

EKEY_README_URL = "https://raw.githubusercontent.com/Ekey/REE.PAK.Tool/main/README.md"
EKEY_PROJECT_URL_TEMPLATE = (
    "https://raw.githubusercontent.com/Ekey/REE.PAK.Tool/main/Projects/{tag}.list"
)
DEFAULT_TIMEOUT = 20

KEY_MODULUS = int.from_bytes(
    bytes(
        [
            0x7D, 0x0B, 0xF8, 0xC1, 0x7C, 0x23, 0xFD, 0x3B, 0xD4, 0x75, 0x16, 0xD2, 0x33, 0x21, 0xD8, 0x10,
            0x71, 0xF9, 0x7C, 0xD1, 0x34, 0x93, 0xBA, 0x77, 0x26, 0xFC, 0xAB, 0x2C, 0xEE, 0xDA, 0xD9, 0x1C,
            0x89, 0xE7, 0x29, 0x7B, 0xDD, 0x8A, 0xAE, 0x50, 0x39, 0xB6, 0x01, 0x6D, 0x21, 0x89, 0x5D, 0xA5,
            0xA1, 0x3E, 0xA2, 0xC0, 0x8C, 0x93, 0x13, 0x36, 0x65, 0xEB, 0xE8, 0xDF, 0x06, 0x17, 0x67, 0x96,
            0x06, 0x2B, 0xAC, 0x23, 0xED, 0x8C, 0xB7, 0x8B, 0x90, 0xAD, 0xEA, 0x71, 0xC4, 0x40, 0x44, 0x9D,
            0x1C, 0x7B, 0xBA, 0xC4, 0xB6, 0x2D, 0xD6, 0xD2, 0x4B, 0x62, 0xD6, 0x26, 0xFC, 0x74, 0x20, 0x07,
            0xEC, 0xE3, 0x59, 0x9A, 0xE6, 0xAF, 0xB9, 0xA8, 0x35, 0x8B, 0xE0, 0xE8, 0xD3, 0xCD, 0x45, 0x65,
            0xB0, 0x91, 0xC4, 0x95, 0x1B, 0xF3, 0x23, 0x1E, 0xC6, 0x71, 0xCF, 0x3E, 0x35, 0x2D, 0x6B, 0xE3,
        ]
    ),
    "little",
    signed=False,
)
KEY_EXPONENT = int.from_bytes(bytes([0x01, 0x00, 0x01, 0x00]), "little", signed=False)
RESOURCE_MODULUS = int.from_bytes(
    bytes(
        [
            0x13, 0xD7, 0x9C, 0x89, 0x88, 0x91, 0x48, 0x10, 0xD7, 0xAA, 0x78, 0xAE, 0xF8, 0x59, 0xDF, 0x7D,
            0x3C, 0x43, 0xA0, 0xD0, 0xBB, 0x36, 0x77, 0xB5, 0xF0, 0x5C, 0x02, 0xAF, 0x65, 0xD8, 0x77, 0x03,
        ]
    ),
    "little",
    signed=False,
)
RESOURCE_EXPONENT = int.from_bytes(
    bytes(
        [
            0xC0, 0xC2, 0x77, 0x1F, 0x5B, 0x34, 0x6A, 0x01, 0xC7, 0xD4, 0xD7, 0x85, 0x2E, 0x42, 0x2B, 0x3B,
            0x16, 0x3A, 0x17, 0x13, 0x16, 0xEA, 0x83, 0x30, 0x30, 0xDF, 0x3F, 0xF4, 0x25, 0x93, 0x20, 0x01,
        ]
    ),
    "little",
    signed=False,
)


def _format_size(size: int) -> str:
    if size < 1024:
        return f"{size} B"
    units = ["KiB", "MiB", "GiB", "TiB"]
    value = float(size)
    for unit in units:
        value /= 1024.0
        if value < 1024.0:
            return f"{value:.2f} {unit}"
    return f"{value:.2f} PiB"


def _normalize_archive_path(path: str) -> str:
    return path.replace("\\", "/").strip("/")


def _sanitize_rel_path(path: str) -> str:
    normalized = _normalize_archive_path(path)
    safe_parts: list[str] = []
    for part in normalized.split("/"):
        if not part or part in {".", ".."}:
            continue
        safe_parts.append("".join("_" if char in INVALID_PATH_CHARS else char for char in part))
    if not safe_parts:
        return "unnamed.bin"
    return os.path.join(*safe_parts)


def _murmur3_hash(data: bytes) -> int:
    c1 = 0xCC9E2D51
    c2 = 0x1B873593
    h1 = 0xFFFFFFFF

    for index in range(0, len(data), 4):
        chunk = data[index:index + 4]
        if len(chunk) == 4:
            k1 = chunk[0] | chunk[1] << 8 | chunk[2] << 16 | chunk[3] << 24
        elif len(chunk) == 3:
            k1 = chunk[0] | chunk[1] << 8 | chunk[2] << 16
        elif len(chunk) == 2:
            k1 = chunk[0] | chunk[1] << 8
        elif len(chunk) == 1:
            k1 = chunk[0]
        else:
            k1 = 0

        k1 = (k1 * c1) & 0xFFFFFFFF
        k1 = ((k1 << 15) | (k1 >> 17)) & 0xFFFFFFFF
        k1 = (k1 * c2) & 0xFFFFFFFF
        h1 ^= k1

        if len(chunk) == 4:
            h1 = ((h1 << 13) | (h1 >> 19)) & 0xFFFFFFFF
            h1 = (h1 * 5 + 0xE6546B64) & 0xFFFFFFFF

    h1 ^= len(data)
    h1 ^= h1 >> 16
    h1 = (h1 * 0x85EBCA6B) & 0xFFFFFFFF
    h1 ^= h1 >> 13
    h1 = (h1 * 0xC2B2AE35) & 0xFFFFFFFF
    h1 ^= h1 >> 16
    return h1


def _get_filepath_hash(path: str) -> int:
    normalized = path.replace("\\", "/")
    lower = _murmur3_hash(normalized.lower().encode("utf-16le"))
    upper = _murmur3_hash(normalized.upper().encode("utf-16le"))
    return ((upper & 0xFFFFFFFF) << 32) | (lower & 0xFFFFFFFF)


def _unknown_path_from_hash(value: int) -> str:
    return f"{UNKNOWN_PREFIX}/{value:016X}.bin"


def _read_exact(handle, size: int) -> bytes:
    data = handle.read(size)
    if len(data) != size:
        raise ValueError("Unexpected end of file")
    return data


def _decompress_deflate(data: bytes) -> bytes:
    try:
        return zlib.decompress(data, -zlib.MAX_WBITS)
    except zlib.error:
        return zlib.decompress(data)


def _decompress_zstd(data: bytes) -> bytes:
    if zstd is None:
        raise RuntimeError("zstandard package is required to decode ZSTD-compressed entries")
    return zstd.ZstdDecompressor().decompress(data)


def _decrypt_key(key: bytes) -> bytes:
    encrypted_key = int.from_bytes(key, "little", signed=False)
    result = pow(encrypted_key, KEY_EXPONENT, KEY_MODULUS)
    return result.to_bytes(len(key), "little", signed=False)


def _decrypt_pak_entry_data(buffer: bytearray, key: bytes) -> None:
    decoded_key = _decrypt_key(key)
    for index in range(len(buffer)):
        buffer[index] ^= (index + decoded_key[index % 32] * decoded_key[index % 29]) & 0xFF


def _decrypt_resource(compressed_bytes: bytes) -> bytes:
    if len(compressed_bytes) < 8:
        raise ValueError("Encrypted resource payload is truncated")

    size = int.from_bytes(compressed_bytes[:8], "little", signed=True)
    block_count = (len(compressed_bytes) - 8) // 128
    output = bytearray(size + 1)
    cursor = 8

    for offset in range(0, block_count * 8, 8):
        key_block = compressed_bytes[cursor:cursor + 64]
        data_block = compressed_bytes[cursor + 64:cursor + 128]
        if len(key_block) != 64 or len(data_block) != 64:
            raise ValueError("Encrypted resource block is truncated")

        key_value = int.from_bytes(key_block, "little", signed=False)
        data_value = int.from_bytes(data_block, "little", signed=False)
        mod_value = pow(key_value, RESOURCE_EXPONENT, RESOURCE_MODULUS)
        result_value = data_value // mod_value
        output[offset:offset + 8] = result_value.to_bytes(8, "little", signed=False)
        cursor += 128

    return bytes(output[:size])


def _looks_textual(data: bytes) -> bool:
    if not data:
        return True
    sample = data[: min(len(data), 4096)]
    printable = sum(
        1
        for value in sample
        if value in (0x09, 0x0A, 0x0D) or 0x20 <= value <= 0x7E
    )
    return printable / max(1, len(sample)) >= 0.8


def _decode_text_preview(data: bytes) -> str | None:
    for encoding in ("utf-8-sig", "utf-16le", "utf-16be", "cp932", "latin-1"):
        try:
            text = data.decode(encoding)
        except UnicodeDecodeError:
            continue
        if text and ("\x00" not in text or encoding.startswith("utf-16")):
            return text
    return None


@dataclass(slots=True)
class EkeyGame:
    display_name: str
    tag: str
    platform: str
    game_name: str


@dataclass(slots=True)
class PakHeader:
    major_version: int
    minor_version: int
    feature_flags: int
    file_count: int
    fingerprint: int


@dataclass(slots=True)
class PakChunkEntry:
    offset: int
    attributes: int


@dataclass(slots=True)
class PakEntry:
    hash_lowercase: int
    hash_uppercase: int
    offset: int
    compressed_size: int
    decompressed_size: int
    checksum: int
    compression: int
    encryption: int
    offset_type: int
    path: str | None = None

    @property
    def combined_hash(self) -> int:
        return ((self.hash_uppercase & 0xFFFFFFFF) << 32) | (self.hash_lowercase & 0xFFFFFFFF)

    @property
    def display_path(self) -> str:
        return self.path or _unknown_path_from_hash(self.combined_hash)

    @property
    def extension(self) -> str:
        _, extension = os.path.splitext(self.display_path)
        return extension.lower()


@dataclass(slots=True)
class TreeNodeInfo:
    kind: str
    pak_file: "PakArchive" | None
    entry: PakEntry | None
    relative_path: str
    display_name: str


class EkeyCatalog:
    def __init__(self, cache_dir: str):
        self.cache_dir = cache_dir
        self.catalog_path = os.path.join(cache_dir, "catalog.json")
        self.projects_dir = os.path.join(cache_dir, "Projects")
        os.makedirs(self.projects_dir, exist_ok=True)

    def fetch_games(self, refresh: bool = False) -> list[EkeyGame]:
        if not refresh:
            cached = self._load_catalog()
            if cached:
                return cached

        readme_text = self._download_text(EKEY_README_URL)
        games = self._parse_readme_games(readme_text)
        self._save_catalog(games)
        return games

    def load_path_map(self, tag: str, refresh: bool = False) -> dict[int, str]:
        if not tag:
            return {}

        project_path = os.path.join(self.projects_dir, f"{tag}.list")
        if refresh or not os.path.exists(project_path):
            content = self._download_text(EKEY_PROJECT_URL_TEMPLATE.format(tag=tag))
            with open(project_path, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(content)

        path_map: dict[int, str] = {}
        with open(project_path, "r", encoding="utf-8", errors="replace") as handle:
            for raw_line in handle:
                line = raw_line.strip()
                if not line:
                    continue
                normalized = _normalize_archive_path(line)
                path_map[_get_filepath_hash(normalized)] = normalized
        return path_map

    def _download_text(self, url: str) -> str:
        request = urllib.request.Request(url, headers={"User-Agent": "ree-browser"})
        with urllib.request.urlopen(request, timeout=DEFAULT_TIMEOUT) as response:
            charset = response.headers.get_content_charset() or "utf-8"
            return response.read().decode(charset, errors="replace")

    def _load_catalog(self) -> list[EkeyGame]:
        if not os.path.exists(self.catalog_path):
            return []
        try:
            with open(self.catalog_path, "r", encoding="utf-8") as handle:
                data = json.load(handle)
            return [EkeyGame(**item) for item in data]
        except Exception:
            return []

    def _save_catalog(self, games: list[EkeyGame]) -> None:
        os.makedirs(self.cache_dir, exist_ok=True)
        with open(self.catalog_path, "w", encoding="utf-8") as handle:
            json.dump([asdict(game) for game in games], handle, ensure_ascii=False, indent=2)

    def _parse_readme_games(self, text: str) -> list[EkeyGame]:
        games: list[EkeyGame] = []
        current_platform = ""
        lines = text.splitlines()
        index = 0

        while index < len(lines):
            line = lines[index].strip()
            if line.startswith("# Platform (") and line.endswith(")"):
                current_platform = line.removeprefix("# Platform (").removesuffix(")").strip()
                index += 1
                continue

            if line.startswith("|") and "List Tag" in line:
                columns = [part.strip() for part in line.split("|") if part.strip()]
                if not columns:
                    index += 1
                    continue
                try:
                    game_index = columns.index("Game")
                    tag_index = columns.index("List Tag")
                except ValueError:
                    index += 1
                    continue
                index += 2
                while index < len(lines):
                    row = lines[index].strip()
                    if not row or not row.startswith("|"):
                        break
                    parts = [part.strip() for part in row.split("|") if part.strip()]
                    if not parts or all(set(part) <= {"-"} for part in parts):
                        index += 1
                        continue
                    if len(parts) <= max(game_index, tag_index):
                        break

                    game_name = parts[game_index]
                    tag = parts[tag_index]
                    if tag.startswith("[") and "]" in tag:
                        tag = tag[1:tag.index("]")]

                    if tag and tag.lower() != "none":
                        games.append(
                            EkeyGame(
                                display_name=f"{game_name} [{current_platform}]",
                                tag=tag,
                                platform=current_platform,
                                game_name=game_name,
                            )
                        )
                    index += 1
                continue

            index += 1

        games.sort(key=lambda item: item.display_name.lower())
        return games


class PakArchive:
    def __init__(self, path: str):
        self.path = path
        self.header: PakHeader | None = None
        self.entries: list[PakEntry] = []
        self.chunk_entries: list[PakChunkEntry] = []
        self.chunk_block_size = 0

    def load_index(self) -> None:
        file_size = os.path.getsize(self.path)
        with open(self.path, "rb") as handle:
            header_raw = _read_exact(handle, HEADER_STRUCT.size)
            magic, major_version, minor_version, feature_flags, file_count, fingerprint = HEADER_STRUCT.unpack(
                header_raw
            )

            if magic != MAGIC:
                raise ValueError(f"Invalid PAK magic: {magic:08X}")
            if (major_version, minor_version) not in SUPPORTED_VERSIONS:
                raise ValueError(f"Unsupported PAK version: {major_version}.{minor_version}")
            unknown_flags = feature_flags & ~KNOWN_FEATURE_FLAGS
            if unknown_flags:
                raise ValueError(f"Unsupported PAK feature flags: 0x{feature_flags:04X}")

            self.header = PakHeader(
                major_version=major_version,
                minor_version=minor_version,
                feature_flags=feature_flags,
                file_count=file_count,
                fingerprint=fingerprint,
            )
            self.entries = []
            self.chunk_entries = []
            self.chunk_block_size = 0

            if file_count <= 0:
                return

            entry_size = 48 if major_version == 4 else 24
            entry_table = bytearray(_read_exact(handle, file_count * entry_size))

            if feature_flags & FEATURE_EXTRA_INTEGER:
                _read_exact(handle, 4)
            if feature_flags & FEATURE_EXTRA_DATA:
                _read_exact(handle, 9)
            if feature_flags != 0:
                _decrypt_pak_entry_data(entry_table, _read_exact(handle, 128))

            if feature_flags & FEATURE_HAS_CHUNK_CONTENT_TABLE:
                self.chunk_block_size, chunk_count = struct.unpack("<ii", _read_exact(handle, 8))
                for _ in range(chunk_count):
                    offset, attributes = CHUNK_ENTRY_STRUCT.unpack(_read_exact(handle, CHUNK_ENTRY_STRUCT.size))
                    self.chunk_entries.append(PakChunkEntry(offset=offset, attributes=attributes))

            if handle.tell() > file_size:
                raise ValueError("PAK index exceeds file size")

            if major_version == 4:
                for offset in range(0, len(entry_table), ENTRY_V4_STRUCT.size):
                    hash_lowercase, hash_uppercase, entry_offset, compressed_size, decompressed_size, attributes, checksum = (
                        ENTRY_V4_STRUCT.unpack_from(entry_table, offset)
                    )
                    self.entries.append(
                        PakEntry(
                            hash_lowercase=hash_lowercase,
                            hash_uppercase=hash_uppercase,
                            offset=entry_offset,
                            compressed_size=compressed_size,
                            decompressed_size=decompressed_size,
                            checksum=checksum,
                            compression=attributes & 0xF,
                            encryption=(attributes >> 16) & 0xFF,
                            offset_type=(attributes >> 24) & 0x0F,
                        )
                    )
            else:
                for offset in range(0, len(entry_table), ENTRY_V2_STRUCT.size):
                    entry_offset, compressed_size, hash_uppercase, hash_lowercase = ENTRY_V2_STRUCT.unpack_from(
                        entry_table, offset
                    )
                    self.entries.append(
                        PakEntry(
                            hash_lowercase=hash_lowercase,
                            hash_uppercase=hash_uppercase,
                            offset=entry_offset,
                            compressed_size=compressed_size,
                            decompressed_size=compressed_size,
                            checksum=0,
                            compression=COMPRESSION_NONE,
                            encryption=0,
                            offset_type=OFFSET_MAIN_CONTENTS,
                        )
                    )

    def resolve_paths(self, external_paths: dict[int, str] | None = None) -> None:
        for entry in self.entries:
            entry.path = None

        manifest_hash = _get_filepath_hash(MANIFEST_PATH)
        manifest_entry = next((entry for entry in self.entries if entry.combined_hash == manifest_hash), None)
        if manifest_entry is not None:
            try:
                manifest_text = self.read_entry_bytes(manifest_entry).decode("utf-8-sig", errors="replace")
                self._apply_path_lines(manifest_text.splitlines())
            except Exception:
                pass

        if external_paths:
            for entry in self.entries:
                if entry.path is None:
                    entry.path = external_paths.get(entry.combined_hash)

    def _apply_path_lines(self, lines: list[str]) -> None:
        entry_map = {entry.combined_hash: entry for entry in self.entries}
        for raw_line in lines:
            line = raw_line.strip()
            if not line:
                continue
            normalized = _normalize_archive_path(line)
            entry = entry_map.get(_get_filepath_hash(normalized))
            if entry is not None:
                entry.path = normalized

    def read_entry_bytes(self, entry: PakEntry) -> bytes:
        with open(self.path, "rb") as handle:
            if entry.offset_type == OFFSET_CHUNK_CONTENTS:
                return self._read_chunked_entry(handle, entry)
            return self._read_regular_entry(handle, entry)

    def _read_chunked_entry(self, handle, entry: PakEntry) -> bytes:
        if not self.chunk_entries:
            raise ValueError("Chunk content table is missing")

        chunk_index = int(entry.offset)
        remaining_size = int(entry.decompressed_size)
        output = bytearray()

        while remaining_size > 0:
            if chunk_index < 0 or chunk_index >= len(self.chunk_entries):
                raise ValueError("Chunk index exceeds chunk table")
            chunk = self.chunk_entries[chunk_index]
            overflow = chunk.attributes & 0b1111111111
            compressed_size = chunk.attributes >> 10
            handle.seek(chunk.offset + 0x100000000 * overflow, os.SEEK_SET)
            chunk_bytes = _read_exact(handle, compressed_size)

            if compressed_size == self.chunk_block_size:
                output.extend(chunk_bytes)
                remaining_size -= compressed_size
            else:
                decoded = _decompress_zstd(chunk_bytes)
                output.extend(decoded)
                remaining_size -= len(decoded)
            chunk_index += 1

        return bytes(output[: entry.decompressed_size])

    def _read_regular_entry(self, handle, entry: PakEntry) -> bytes:
        handle.seek(entry.offset, os.SEEK_SET)
        if entry.compression == COMPRESSION_NONE:
            return _read_exact(handle, int(entry.decompressed_size or entry.compressed_size))

        raw_data = _read_exact(handle, int(entry.compressed_size))
        if entry.encryption != 0:
            raw_data = _decrypt_resource(raw_data)

        if entry.compression == COMPRESSION_DEFLATE:
            return _decompress_deflate(raw_data)
        if entry.compression == COMPRESSION_ZSTD:
            return _decompress_zstd(raw_data)
        raise ValueError(f"Unsupported compression type: {entry.compression}")


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("REE PAK Browser")
        self.minsize(1080, 700)
        self._center_window(1400, 860)

        self.script_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.dirname(self.script_dir)
        self.cache_root = os.path.join(self.repo_root, ".cache")
        self.config_path = os.path.join(self.script_dir, "config.ini")
        self.catalog = EkeyCatalog(os.path.join(self.cache_root, "ree_pak_tool"))

        self.config_data = configparser.ConfigParser()
        self.archive_files: list[PakArchive] = []
        self.tree_item_info: dict[str, TreeNodeInfo] = {}
        self.games: list[EkeyGame] = []
        self.game_display_to_tag: dict[str, str] = {}

        self.filter_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Ready.")
        self.preview_info_var = tk.StringVar(value="Select a file to inspect.")
        self.game_var = tk.StringVar()

        self.hex_preview_bytes = 0x10000
        self.preview_data_limit = 0x2000000

        self._load_config()
        self._build_menu()
        self._build_body()
        self._build_context_menu()
        self._refresh_game_catalog(async_refresh=True)

    def _build_menu(self):
        menubar = tk.Menu(self)
        self.config(menu=menubar)

        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open PAK File...", command=self.open_pak_file)
        file_menu.add_command(label="Open PAK Folder...", command=self.open_folder)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.destroy)
        menubar.add_cascade(label="File", menu=file_menu)

        tools_menu = tk.Menu(menubar, tearoff=0)
        tools_menu.add_command(label="Refresh Game List", command=lambda: self._refresh_game_catalog(async_refresh=True, force=True))
        tools_menu.add_command(label="Download Selected Tag List", command=self.download_selected_tag_list)
        menubar.add_cascade(label="Tools", menu=tools_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

    def _build_body(self):
        self._build_toolbar()
        self._build_main_panes()
        self._build_statusbar()

    def _build_context_menu(self):
        self.tree_context_menu = tk.Menu(self, tearoff=0)
        self.tree_context_menu.add_command(label="Extract Selected...", command=self.extract_selected)

    def _build_toolbar(self):
        toolbar = ttk.Frame(self, padding=(8, 6))
        toolbar.pack(side=tk.TOP, fill=tk.X)

        ttk.Button(toolbar, text="Open PAK Folder...", command=self.open_folder).pack(side=tk.LEFT)
        ttk.Button(toolbar, text="Open PAK File...", command=self.open_pak_file).pack(side=tk.LEFT, padx=(6, 0))

        ttk.Label(toolbar, text="  Game: ").pack(side=tk.LEFT, padx=(12, 0))
        self.game_combo = ttk.Combobox(toolbar, textvariable=self.game_var, state="readonly", width=42)
        self.game_combo.pack(side=tk.LEFT)
        self.game_combo.bind("<<ComboboxSelected>>", self.on_game_selected)

        ttk.Button(toolbar, text="Refresh Tags", command=lambda: self._refresh_game_catalog(async_refresh=True, force=True)).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(toolbar, text="Cache Tag List", command=self.download_selected_tag_list).pack(side=tk.LEFT, padx=(6, 0))

        ttk.Label(toolbar, text="  Filter: ").pack(side=tk.LEFT, padx=(12, 0))
        filter_entry = ttk.Entry(toolbar, textvariable=self.filter_var, width=48)
        filter_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        filter_entry.bind("<KeyRelease>", self.apply_filter)

        ttk.Button(toolbar, text="Clear", command=self._clear_filter).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(toolbar, text="Extract Selected...", command=self.extract_selected).pack(side=tk.LEFT, padx=(12, 0))

    def _build_main_panes(self):
        paned = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        paned.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=8, pady=6)

        left = ttk.Frame(paned)
        left.grid_rowconfigure(1, weight=1)
        left.grid_columnconfigure(0, weight=1)
        paned.add(left, weight=1)

        ttk.Label(left, text="PAK Tree").grid(row=0, column=0, sticky="w")
        self.tree_archive = ttk.Treeview(left, show="tree")
        self.tree_archive.column("#0", width=520, anchor="w")
        self.tree_archive.grid(row=1, column=0, sticky="nsew")

        archive_scroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.tree_archive.yview)
        archive_scroll.grid(row=1, column=1, sticky="ns")
        self.tree_archive.configure(yscrollcommand=archive_scroll.set)
        self.tree_archive.bind("<<TreeviewSelect>>", self.on_select_tree_node)
        self.tree_archive.bind("<Button-3>", self.on_tree_context_menu)

        right = ttk.Frame(paned)
        right.grid_rowconfigure(1, weight=1)
        right.grid_columnconfigure(0, weight=1)
        paned.add(right, weight=3)

        ttk.Label(right, text="Preview").grid(row=0, column=0, sticky="w")
        ttk.Label(right, textvariable=self.preview_info_var, anchor="w").grid(row=0, column=1, sticky="ew", padx=(12, 0))

        self.preview_notebook = ttk.Notebook(right)
        self.preview_notebook.grid(row=1, column=0, columnspan=2, sticky="nsew")

        preview_tab = ttk.Frame(self.preview_notebook)
        preview_tab.grid_rowconfigure(0, weight=1)
        preview_tab.grid_columnconfigure(0, weight=1)
        self.preview_notebook.add(preview_tab, text="Preview")

        self.preview_text = tk.Text(
            preview_tab,
            wrap="none",
            font=("Consolas", 10),
            bg="#101010",
            fg="#E8E8E8",
            insertbackground="#E8E8E8",
        )
        self.preview_text.grid(row=0, column=0, sticky="nsew")

        preview_scroll_y = ttk.Scrollbar(preview_tab, orient=tk.VERTICAL, command=self.preview_text.yview)
        preview_scroll_x = ttk.Scrollbar(preview_tab, orient=tk.HORIZONTAL, command=self.preview_text.xview)
        preview_scroll_y.grid(row=0, column=1, sticky="ns")
        preview_scroll_x.grid(row=1, column=0, sticky="ew")
        self.preview_text.configure(yscrollcommand=preview_scroll_y.set, xscrollcommand=preview_scroll_x.set)

        hex_tab = ttk.Frame(self.preview_notebook)
        hex_tab.grid_rowconfigure(0, weight=1)
        hex_tab.grid_columnconfigure(0, weight=1)
        self.preview_notebook.add(hex_tab, text="Hex")

        self.hex_text = tk.Text(
            hex_tab,
            wrap="none",
            font=("Consolas", 10),
            bg="#101010",
            fg="#E8E8E8",
            insertbackground="#E8E8E8",
        )
        self.hex_text.grid(row=0, column=0, sticky="nsew")

        hex_scroll_y = ttk.Scrollbar(hex_tab, orient=tk.VERTICAL, command=self.hex_text.yview)
        hex_scroll_x = ttk.Scrollbar(hex_tab, orient=tk.HORIZONTAL, command=self.hex_text.xview)
        hex_scroll_y.grid(row=0, column=1, sticky="ns")
        hex_scroll_x.grid(row=1, column=0, sticky="ew")
        self.hex_text.configure(yscrollcommand=hex_scroll_y.set, xscrollcommand=hex_scroll_x.set)

        self._show_preview_text("")
        self._set_hex_text("")

    def _build_statusbar(self):
        status = ttk.Label(self, textvariable=self.status_var, relief=tk.SUNKEN, anchor="w")
        status.pack(side=tk.BOTTOM, fill=tk.X)

    def _center_window(self, width: int, height: int):
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        x_pos = int((screen_w - width) / 2)
        y_pos = int((screen_h - height) / 2)
        self.geometry(f"{width}x{height}+{x_pos}+{y_pos}")

    def show_about(self):
        messagebox.showinfo(
            "About",
            "REE PAK Browser\n"
            "Tree view, decoded preview, hex view, and optional filename resolution via Ekey tag lists.",
        )

    def _load_config(self):
        self.config_data.read(self.config_path, encoding="utf-8")
        if not self.config_data.has_section("browser"):
            self.config_data.add_section("browser")
        self.game_var.set(self.config_data.get("browser", "selected_game", fallback="(None)"))

    def _save_config(self):
        browser = self.config_data["browser"]
        browser["selected_game"] = self.game_var.get().strip() or "(None)"
        with open(self.config_path, "w", encoding="utf-8") as handle:
            self.config_data.write(handle)

    def _set_status(self, text: str):
        self.status_var.set(text)
        self.update_idletasks()

    def _clear_filter(self):
        self.filter_var.set("")
        self.apply_filter()

    def _clear_all(self):
        self.archive_files = []
        self.tree_item_info = {}
        self.tree_archive.delete(*self.tree_archive.get_children())
        self._show_preview_text("")
        self._set_hex_text("")
        self.preview_info_var.set("Select a file to inspect.")

    def _selected_tag(self) -> str:
        display = self.game_var.get().strip()
        if not display or display == "(None)":
            return ""
        return self.game_display_to_tag.get(display, "")

    def on_game_selected(self, _event=None):
        self._save_config()

    def _refresh_game_catalog(self, async_refresh: bool, force: bool = False):
        def worker():
            try:
                games = self.catalog.fetch_games(refresh=force)
            except Exception as ex:
                self.after(0, lambda ex=ex: self._set_status(f"Failed to refresh game list: {ex}"))
                return
            self.after(0, lambda games=games: self._apply_game_catalog(games))

        if async_refresh:
            self._set_status("Refreshing game list from Ekey/REE.PAK.Tool...")
            threading.Thread(target=worker, daemon=True).start()
        else:
            worker()

    def _apply_game_catalog(self, games: list[EkeyGame]):
        self.games = games
        values = ["(None)"] + [game.display_name for game in games]
        self.game_display_to_tag = {game.display_name: game.tag for game in games}
        self.game_combo.configure(values=values)

        if self.game_var.get() not in values:
            self.game_var.set("(None)")
            self._save_config()

        self._set_status(f"Loaded {len(games):,} game tags.")

    def download_selected_tag_list(self):
        tag = self._selected_tag()
        if not tag:
            messagebox.showinfo("Cache Tag List", "Select a game tag first.")
            return

        def worker():
            try:
                self.catalog.load_path_map(tag, refresh=True)
            except Exception as ex:
                self.after(0, lambda ex=ex: messagebox.showerror("Cache Tag List", f"Failed:\n{ex}"))
                self.after(0, lambda: self._set_status("Tag list download failed."))
                return

            self.after(0, lambda: self._set_status(f"Cached tag list: {tag}"))
            self.after(0, lambda: messagebox.showinfo("Cache Tag List", f"Cached:\n{tag}"))

        self._set_status(f"Downloading tag list: {tag}")
        threading.Thread(target=worker, daemon=True).start()

    def open_pak_file(self):
        initial_dir = self.config_data.get("browser", "last_open_dir", fallback=self.repo_root)
        pak_path = filedialog.askopenfilename(
            title="Select a .pak file",
            initialdir=initial_dir,
            filetypes=[("PAK files", "*.pak"), ("All files", "*.*")],
        )
        if not pak_path:
            return

        self.config_data["browser"]["last_open_dir"] = os.path.dirname(pak_path)
        self._save_config()
        self._clear_all()
        self._load_pak_paths([pak_path])

    def open_folder(self):
        initial_dir = self.config_data.get("browser", "last_open_dir", fallback=self.repo_root)
        folder = filedialog.askdirectory(title="Select folder containing .pak files", initialdir=initial_dir)
        if not folder:
            return

        self.config_data["browser"]["last_open_dir"] = folder
        self._save_config()
        self._clear_all()

        try:
            pak_paths = sorted(
                os.path.join(folder, file_name)
                for file_name in os.listdir(folder)
                if file_name.lower().endswith(".pak") and os.path.isfile(os.path.join(folder, file_name))
            )
        except Exception as ex:
            messagebox.showerror("REE PAK Browser", f"Failed to scan folder:\n{ex}")
            self._set_status("Folder scan failed.")
            return

        if not pak_paths:
            messagebox.showinfo("REE PAK Browser", "No .pak files found in that folder.")
            self._set_status("No .pak files found.")
            return

        self._load_pak_paths(pak_paths)

    def _load_pak_paths(self, pak_paths: list[str]):
        def worker():
            try:
                path_map: dict[int, str] | None = None
                tag = self._selected_tag()
                if tag:
                    self.after(0, lambda tag=tag: self._set_status(f"Loading cached filename list: {tag}"))
                    path_map = self.catalog.load_path_map(tag, refresh=False)

                loaded_files: list[PakArchive] = []
                total = len(pak_paths)
                for index, path in enumerate(pak_paths, start=1):
                    pak_file = PakArchive(path)
                    pak_file.load_index()
                    pak_file.resolve_paths(path_map)
                    loaded_files.append(pak_file)
                    self.after(
                        0,
                        lambda index=index, total=total, path=path: self._set_status(
                            f"Loaded {index}/{total}: {os.path.basename(path)}"
                        ),
                    )

                self.after(0, lambda loaded_files=loaded_files: self._apply_loaded_paks(loaded_files))
            except urllib.error.URLError as ex:
                self.after(0, lambda ex=ex: messagebox.showerror("REE PAK Browser", f"Network error:\n{ex}"))
                self.after(0, lambda: self._set_status("PAK load failed."))
            except Exception as ex:
                self.after(0, lambda ex=ex: messagebox.showerror("REE PAK Browser", f"Failed to load PAK files:\n{ex}"))
                self.after(0, lambda: self._set_status("PAK load failed."))

        self._set_status(f"Loading {len(pak_paths):,} PAK file(s)...")
        threading.Thread(target=worker, daemon=True).start()

    def _apply_loaded_paks(self, pak_files: list[PakArchive]):
        self.archive_files = pak_files
        self._populate_archive_tree()
        roots = self.tree_archive.get_children()
        if roots:
            self.tree_archive.selection_set(roots[0])
            self.tree_archive.focus(roots[0])
            self.tree_archive.see(roots[0])
            self.on_select_tree_node()
        self._set_status(f"Loaded {len(pak_files):,} PAK file(s).")

    def _populate_archive_tree(self):
        self.tree_archive.delete(*self.tree_archive.get_children())
        self.tree_item_info.clear()

        filter_term = self.filter_var.get().strip().lower()
        for pak_file in self.archive_files:
            header = pak_file.header
            version = f"{header.major_version}.{header.minor_version}" if header else "?"
            root_text = f"{os.path.basename(pak_file.path)} [v{version}]"
            root_id = self.tree_archive.insert("", "end", text=root_text, open=True)
            self.tree_item_info[root_id] = TreeNodeInfo(
                kind="pak",
                pak_file=pak_file,
                entry=None,
                relative_path="",
                display_name=root_text,
            )

            nodes: dict[str, str] = {"": root_id}
            sorted_entries = sorted(pak_file.entries, key=lambda item: item.display_path.lower())

            for entry in sorted_entries:
                normalized = _normalize_archive_path(entry.display_path)
                if filter_term and filter_term not in normalized.lower():
                    continue

                parts = [part for part in normalized.split("/") if part]
                parent = root_id
                path_acc: list[str] = []

                for index, part in enumerate(parts):
                    path_acc.append(part)
                    key = "/".join(path_acc)
                    is_file = index == len(parts) - 1

                    node_id = nodes.get(key)
                    if node_id is None:
                        node_id = self.tree_archive.insert(parent, "end", text=part, open=False)
                        nodes[key] = node_id
                        self.tree_item_info[node_id] = TreeNodeInfo(
                            kind="file" if is_file else "folder",
                            pak_file=pak_file,
                            entry=entry if is_file else None,
                            relative_path=key,
                            display_name=part,
                        )
                    parent = node_id

    def apply_filter(self, _event=None):
        self._populate_archive_tree()
        roots = self.tree_archive.get_children()
        if roots:
            self.tree_archive.selection_set(roots[0])
            self.on_select_tree_node()

    def on_select_tree_node(self, _event=None):
        selection = self.tree_archive.selection()
        if not selection:
            self._show_preview_text("")
            self._set_hex_text("")
            self.preview_info_var.set("Select a file to inspect.")
            return
        self._refresh_preview(selection[0])

    def _refresh_preview(self, item_id: str):
        info = self.tree_item_info.get(item_id)
        if info is None or info.pak_file is None:
            self._show_preview_text("")
            self._set_hex_text("")
            self.preview_info_var.set("Select a file to inspect.")
            return

        if info.entry is None:
            self._preview_folder(item_id, info)
        else:
            self._preview_entry(info.pak_file, info.entry)

    def _preview_entry(self, pak_file: PakArchive, entry: PakEntry):
        estimated_size = max(int(entry.decompressed_size), int(entry.compressed_size))
        if estimated_size > self.preview_data_limit:
            self.preview_info_var.set(f"{entry.display_path} | {_format_size(estimated_size)} | preview skipped")
            self._show_preview_text(
                "\n".join(
                    [
                        f"Path: {entry.display_path}",
                        f"Hash: 0x{entry.combined_hash:016X}",
                        f"Stored size: {_format_size(int(entry.compressed_size))}",
                        f"Decoded size: {_format_size(int(entry.decompressed_size))}",
                        f"Compression: {entry.compression}",
                        f"Encryption: {entry.encryption}",
                        "",
                        f"Preview skipped because the entry is larger than {_format_size(self.preview_data_limit)}.",
                    ]
                )
            )
            self._set_hex_text("")
            return

        try:
            data = pak_file.read_entry_bytes(entry)
        except Exception as ex:
            self.preview_info_var.set("Read failed")
            self._show_preview_text(f"Failed to decode entry:\n{ex}")
            self._set_hex_text("")
            return

        preview_slice = data[: self.hex_preview_bytes]
        self.preview_info_var.set(
            " | ".join(
                [
                    entry.display_path,
                    f"hash=0x{entry.combined_hash:016X}",
                    f"stored={_format_size(int(entry.compressed_size))}",
                    f"decoded={_format_size(len(data))}",
                    f"cmp={entry.compression}",
                    f"enc={entry.encryption}",
                    f"shown={_format_size(len(preview_slice))}",
                ]
            )
        )
        self._set_hex_text(self._format_hex_dump(preview_slice))

        preview_text = None
        if entry.extension in {".txt", ".json", ".xml", ".user", ".ini", ".log"} or _looks_textual(preview_slice):
            preview_text = _decode_text_preview(data[: min(len(data), 0x20000)])

        if preview_text is None:
            preview_text = "\n".join(
                [
                    f"Path: {entry.display_path}",
                    f"Hash: 0x{entry.combined_hash:016X}",
                    f"Stored size: {_format_size(int(entry.compressed_size))}",
                    f"Decoded size: {_format_size(len(data))}",
                    f"Compression: {entry.compression}",
                    f"Encryption: {entry.encryption}",
                    f"Offset type: {entry.offset_type}",
                    f"Checksum: 0x{entry.checksum:016X}",
                    "",
                    "Use the Hex tab for byte-level inspection.",
                ]
            )

        self._show_preview_text(preview_text)

    def _preview_folder(self, item_id: str, info: TreeNodeInfo):
        descendants = self._collect_descendant_nodes(item_id)
        entries = [self.tree_item_info[node_id] for node_id in descendants if self.tree_item_info.get(node_id)]
        file_entries = [node for node in entries if node.entry is not None]
        folder_entries = [node for node in entries if node.entry is None]

        lines = [
            f"Node: {self._tree_item_path(item_id)}",
            f"Type: {info.kind}",
            f"Folders: {len(folder_entries):,}",
            f"Files: {len(file_entries):,}",
            "",
        ]

        for node in file_entries[:500]:
            lines.append(node.relative_path)
        if len(file_entries) > 500:
            lines.append("")
            lines.append(f"... {len(file_entries) - 500:,} more files omitted")

        self.preview_info_var.set(
            f"{self._tree_item_path(item_id)} | files={len(file_entries):,} | folders={len(folder_entries):,}"
        )
        self._show_preview_text("\n".join(lines))
        self._set_hex_text("")

    def _collect_descendant_nodes(self, item_id: str) -> list[str]:
        nodes: list[str] = []
        stack = list(reversed(self.tree_archive.get_children(item_id)))
        while stack:
            node_id = stack.pop()
            nodes.append(node_id)
            children = self.tree_archive.get_children(node_id)
            if children:
                stack.extend(reversed(children))
        return nodes

    def _tree_item_path(self, item_id: str) -> str:
        parts: list[str] = []
        current = item_id
        while current:
            parts.append(self.tree_archive.item(current, "text"))
            current = self.tree_archive.parent(current)
            if current == "":
                break
        return "/".join(reversed(parts))

    def _set_text_widget(self, widget: tk.Text, text: str):
        widget.configure(state="normal")
        widget.delete("1.0", tk.END)
        widget.insert("1.0", text)
        widget.configure(state="disabled")
        widget.yview_moveto(0.0)
        widget.xview_moveto(0.0)

    def _show_preview_text(self, text: str):
        self._set_text_widget(self.preview_text, text)
        self.preview_notebook.select(0)

    def _set_hex_text(self, text: str):
        self._set_text_widget(self.hex_text, text)

    def _format_hex_dump(self, data: bytes, bytes_per_line: int = 16) -> str:
        lines: list[str] = []
        for offset in range(0, len(data), bytes_per_line):
            chunk = data[offset:offset + bytes_per_line]
            hex_part = " ".join(f"{value:02X}" for value in chunk)
            if len(chunk) < bytes_per_line:
                hex_part += "   " * (bytes_per_line - len(chunk))
            ascii_part = "".join(chr(value) if 32 <= value <= 126 else "." for value in chunk)
            lines.append(f"{offset:08X}  {hex_part}  {ascii_part}")
        return "\n".join(lines)

    def extract_selected(self):
        selection = self.tree_archive.selection()
        if not selection:
            messagebox.showinfo("Extract", "Select a file entry first.")
            return

        node_info = self.tree_item_info.get(selection[0])
        if node_info is None or node_info.entry is None or node_info.pak_file is None:
            messagebox.showinfo("Extract", "Select a file entry first.")
            return

        out_dir = filedialog.askdirectory(title="Select output folder", initialdir=self.repo_root)
        if not out_dir:
            return

        entry = node_info.entry
        out_path = os.path.join(out_dir, _sanitize_rel_path(entry.display_path))
        os.makedirs(os.path.dirname(out_path), exist_ok=True)

        try:
            with open(out_path, "wb") as handle:
                handle.write(node_info.pak_file.read_entry_bytes(entry))
            self._set_status(f"Extracted: {out_path}")
            messagebox.showinfo("Extract", f"Done:\n{out_path}")
        except Exception as ex:
            messagebox.showerror("Extract", f"Failed:\n{ex}")

    def on_tree_context_menu(self, event):
        item_id = self.tree_archive.identify_row(event.y)
        if not item_id:
            return

        self.tree_archive.selection_set(item_id)
        self.tree_archive.focus(item_id)
        self.on_select_tree_node()

        node_info = self.tree_item_info.get(item_id)
        state = tk.NORMAL if node_info is not None and node_info.entry is not None else tk.DISABLED
        self.tree_context_menu.entryconfigure("Extract Selected...", state=state)

        try:
            self.tree_context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.tree_context_menu.grab_release()


def main():
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
