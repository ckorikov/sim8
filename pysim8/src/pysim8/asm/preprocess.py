"""Phase 0 preprocessor: resolves @include directives (spec §5.8).

Produces a flat annotated source for the two-pass assembler:
  - source: flat concatenated text (all @include lines replaced by file contents)
  - line_map: flat_line_no → (filename, original_line_no)
    filename=None means the root file.
"""

from __future__ import annotations

import re
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path
from urllib.error import URLError

from pysim8.asm.parser import AsmError

__all__ = ["preprocess", "PreprocessResult", "PreprocessError"]

_RE_INCLUDE_FULL = re.compile(r'^\s*@include\s+"([^"]*)"\s*$', re.IGNORECASE)
_RE_INCLUDE_START = re.compile(r"^\s*@include\b", re.IGNORECASE)

MAX_INCLUDE_DEPTH = 16

# SourceLoc: (filename, line_no) — filename=None means root file
SourceLoc = tuple[str | None, int]


def _is_url(path: str) -> bool:
    return path.startswith(("http://", "https://"))


class PreprocessError(AsmError):
    """Raised during Phase 0 preprocessing."""


@dataclass(slots=True)
class PreprocessResult:
    """Output of Phase 0 preprocessing."""

    source: str
    line_map: dict[int, SourceLoc] = field(default_factory=dict)


def preprocess(
    source: str,
    base_path: Path | None,
    include_paths: list[Path] | None = None,
) -> PreprocessResult:
    """Resolve all @include directives and return a flat annotated source.

    base_path: directory used to resolve relative paths in @include directives.
      Pass None when assembling from an in-memory string — @include is then an error.
    include_paths: additional directories to search for @include files (like -I in C).
      Tried in order after the including file's own directory.
    """
    out_lines: list[str] = []
    line_map: dict[int, SourceLoc] = {}
    _collect(
        source=source,
        current_dir=base_path,
        root_dir=base_path,
        filename=None,
        chain=frozenset(),
        depth=0,
        out_lines=out_lines,
        line_map=line_map,
        include_paths=include_paths or [],
    )
    return PreprocessResult(source="\n".join(out_lines), line_map=line_map)


def _collect(
    source: str,
    current_dir: Path | None,
    root_dir: Path | None,
    filename: str | None,
    chain: frozenset[Path | str],
    depth: int,
    out_lines: list[str],
    line_map: dict[int, SourceLoc],
    include_paths: list[Path] | None = None,
) -> None:
    for lineno, text in enumerate(source.splitlines(), start=1):
        if _RE_INCLUDE_START.match(text):
            _handle_include(
                text=text,
                lineno=lineno,
                filename=filename,
                current_dir=current_dir,
                root_dir=root_dir,
                chain=chain,
                depth=depth,
                out_lines=out_lines,
                line_map=line_map,
                include_paths=include_paths,
            )
        else:
            flat_lineno = len(out_lines) + 1
            out_lines.append(text)
            line_map[flat_lineno] = (filename, lineno)


def _embed_binary(
    data: bytes,
    out_lines: list[str],
    line_map: dict[int, SourceLoc],
    filename: str | None,
    lineno: int,
) -> None:
    """Emit raw bytes as a DB directive into the flat output (binary include)."""
    if data:
        flat_lineno = len(out_lines) + 1
        out_lines.append("DB " + ", ".join(str(b) for b in data))
        line_map[flat_lineno] = (filename, lineno)


def _decode_source(data: bytes) -> str | None:
    """Return UTF-8 text if data is text (no null bytes, valid UTF-8), else None."""
    if b"\x00" in data:
        return None
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return None


def _handle_url_include(
    url: str,
    lineno: int,
    filename: str | None,
    root_dir: Path | None,
    chain: frozenset[Path | str],
    depth: int,
    out_lines: list[str],
    line_map: dict[int, SourceLoc],
) -> None:
    if url in chain:
        raise PreprocessError(f"@include: circular include: {url}", lineno, filename=filename)

    try:
        with urllib.request.urlopen(url, timeout=10) as resp:  # noqa: S310
            data: bytes = resp.read()
    except (URLError, OSError) as exc:
        raise PreprocessError(f"@include: fetch failed: {url}: {exc}", lineno, filename=filename) from exc

    inc_source = _decode_source(data)
    if inc_source is None:
        _embed_binary(data, out_lines, line_map, filename, lineno)
        return

    _collect(
        source=inc_source,
        current_dir=None,  # URL context: no local filesystem base
        root_dir=root_dir,
        filename=url,
        chain=chain | {url},
        depth=depth + 1,
        out_lines=out_lines,
        line_map=line_map,
    )


def _resolve_include(
    path_str: str,
    current_dir: Path | None,
    include_paths: list[Path] | None,
) -> Path | None:
    """Try current_dir first, then each include_path. Return resolved Path or None."""
    candidates: list[Path] = []
    if current_dir is not None:
        candidates.append(current_dir)
    if include_paths:
        candidates.extend(include_paths)
    for base in candidates:
        candidate = (base / path_str).resolve()
        if candidate.is_file():
            return candidate
    return None


def _handle_include(
    text: str,
    lineno: int,
    filename: str | None,
    current_dir: Path | None,
    root_dir: Path | None,
    chain: frozenset[Path | str],
    depth: int,
    out_lines: list[str],
    line_map: dict[int, SourceLoc],
    include_paths: list[Path] | None = None,
) -> None:
    m = _RE_INCLUDE_FULL.match(text)
    if not m or not m.group(1):
        raise PreprocessError("@include: invalid syntax", lineno, filename=filename)

    if depth >= MAX_INCLUDE_DEPTH:
        raise PreprocessError("@include: max include depth exceeded", lineno, filename=filename)

    path_str = m.group(1)

    if _is_url(path_str):
        _handle_url_include(
            url=path_str,
            lineno=lineno,
            filename=filename,
            root_dir=root_dir,
            chain=chain,
            depth=depth,
            out_lines=out_lines,
            line_map=line_map,
        )
        return

    if current_dir is None and not include_paths:
        raise PreprocessError("@include: no filesystem context", lineno, filename=filename)

    inc_path = _resolve_include(path_str, current_dir, include_paths)

    if inc_path is None:
        raise PreprocessError(f"@include: file not found: {path_str}", lineno, filename=filename)

    if inc_path in chain:
        raise PreprocessError(f"@include: circular include: {path_str}", lineno, filename=filename)

    inc_filename = _normalize(inc_path, root_dir)

    data = inc_path.read_bytes()
    inc_source = _decode_source(data)
    if inc_source is None:
        _embed_binary(data, out_lines, line_map, filename, lineno)
        return

    _collect(
        source=inc_source,
        current_dir=inc_path.parent,
        root_dir=root_dir,
        filename=inc_filename,
        chain=chain | {inc_path},
        depth=depth + 1,
        out_lines=out_lines,
        line_map=line_map,
        include_paths=include_paths,
    )


def _normalize(path: Path, root_dir: Path | None) -> str:
    """Normalize path relative to root_dir; use str(path) if outside."""
    if root_dir is None:
        return str(path)
    try:
        return str(path.relative_to(root_dir))
    except ValueError:
        return str(path)
