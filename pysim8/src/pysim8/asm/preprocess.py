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


@dataclass
class _IncludeCtx:
    """Shared mutable state + immutable config threaded through recursive include resolution."""

    root_dir: Path | None
    out_lines: list[str]
    line_map: dict[int, SourceLoc]
    include_paths: list[Path]
    chain: frozenset[Path | str] = field(default_factory=frozenset)
    depth: int = 0

    def child(self, added: Path | str) -> _IncludeCtx:
        """Return a new ctx for one level deeper, with `added` in the chain."""
        return _IncludeCtx(
            root_dir=self.root_dir,
            out_lines=self.out_lines,
            line_map=self.line_map,
            include_paths=self.include_paths,
            chain=self.chain | {added},
            depth=self.depth + 1,
        )


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
    ctx = _IncludeCtx(
        root_dir=base_path,
        out_lines=[],
        line_map={},
        include_paths=include_paths or [],
    )
    _collect(source=source, current_dir=base_path, filename=None, ctx=ctx)
    return PreprocessResult(source="\n".join(ctx.out_lines), line_map=ctx.line_map)


def _collect(
    source: str,
    current_dir: Path | None,
    filename: str | None,
    ctx: _IncludeCtx,
) -> None:
    for lineno, text in enumerate(source.splitlines(), start=1):
        if _RE_INCLUDE_START.match(text):
            _handle_include(text=text, lineno=lineno, filename=filename, current_dir=current_dir, ctx=ctx)
        else:
            flat_lineno = len(ctx.out_lines) + 1
            ctx.out_lines.append(text)
            ctx.line_map[flat_lineno] = (filename, lineno)


_RE_PAGE_NUM = re.compile(r"^\s*@page\s+(\d+)", re.IGNORECASE)

_PAGE_SIZE = 256


def _find_current_page(out_lines: list[str]) -> int:
    """Scan backwards through emitted lines to find the most recent @page number."""
    for line in reversed(out_lines):
        m = _RE_PAGE_NUM.match(line)
        if m:
            return int(m.group(1))
    return 0


def _emit_line(
    text: str,
    out_lines: list[str],
    line_map: dict[int, SourceLoc],
    filename: str | None,
    lineno: int,
) -> None:
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
    """Emit raw bytes as DB directives, auto-splitting across pages if needed."""
    if not data:
        return
    if len(data) <= _PAGE_SIZE:
        _emit_line("DB " + ", ".join(str(b) for b in data), out_lines, line_map, filename, lineno)
        return
    page = _find_current_page(out_lines)
    for i in range(0, len(data), _PAGE_SIZE):
        if i > 0:
            page += 1
            if page > 255:
                raise PreprocessError(
                    f"@include: binary file spans beyond page 255 "
                    f"({len(data)} bytes from page {page - (i // _PAGE_SIZE)})",
                    lineno,
                    filename=filename,
                )
            _emit_line(f"@page {page}", out_lines, line_map, filename, lineno)
        chunk = data[i : i + _PAGE_SIZE]
        _emit_line("DB " + ", ".join(str(b) for b in chunk), out_lines, line_map, filename, lineno)


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
    ctx: _IncludeCtx,
) -> None:
    if url in ctx.chain:
        raise PreprocessError(f"@include: circular include: {url}", lineno, filename=filename)

    try:
        with urllib.request.urlopen(url, timeout=10) as resp:
            data: bytes = resp.read()
    except (URLError, OSError) as exc:
        raise PreprocessError(f"@include: fetch failed: {url}: {exc}", lineno, filename=filename) from exc

    inc_source = _decode_source(data)
    if inc_source is None:
        _embed_binary(data, ctx.out_lines, ctx.line_map, filename, lineno)
        return

    _collect(
        source=inc_source,
        current_dir=None,  # URL context: no local filesystem base
        filename=url,
        ctx=ctx.child(url),
    )


def _resolve_include(
    path_str: str,
    current_dir: Path | None,
    include_paths: list[Path],
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
    ctx: _IncludeCtx,
) -> None:
    m = _RE_INCLUDE_FULL.match(text)
    if not m or not m.group(1):
        raise PreprocessError("@include: invalid syntax", lineno, filename=filename)

    if ctx.depth >= MAX_INCLUDE_DEPTH:
        raise PreprocessError("@include: max include depth exceeded", lineno, filename=filename)

    path_str = m.group(1)

    if _is_url(path_str):
        _handle_url_include(url=path_str, lineno=lineno, filename=filename, ctx=ctx)
        return

    if current_dir is None and not ctx.include_paths:
        raise PreprocessError("@include: no filesystem context", lineno, filename=filename)

    inc_path = _resolve_include(path_str, current_dir, ctx.include_paths)

    if inc_path is None:
        raise PreprocessError(f"@include: file not found: {path_str}", lineno, filename=filename)

    if inc_path in ctx.chain:
        raise PreprocessError(f"@include: circular include: {path_str}", lineno, filename=filename)

    data = inc_path.read_bytes()
    inc_source = _decode_source(data)
    if inc_source is None:
        _embed_binary(data, ctx.out_lines, ctx.line_map, filename, lineno)
        return

    _collect(
        source=inc_source,
        current_dir=inc_path.parent,
        filename=_normalize(inc_path, ctx.root_dir),
        ctx=ctx.child(inc_path),
    )


def _normalize(path: Path, root_dir: Path | None) -> str:
    """Normalize path relative to root_dir; use str(path) if outside."""
    if root_dir is None:
        return str(path)
    try:
        return str(path.relative_to(root_dir))
    except ValueError:
        return str(path)
