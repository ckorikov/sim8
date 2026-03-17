"""Tests for @include directive (spec §5.8).

API contract being tested:
  assemble(source, arch=1, base_path=None)
    base_path=None  → @include raises AssemblerError("@include: no filesystem context")
    base_path=Path  → @include resolved relative to that directory

  AsmError gains: filename: str | None = None
    None = root file or no-filesystem context
    str  = normalized path relative to root file's directory

  AssembleResult.mapping: dict[int, tuple[str | None, int]]
    code_pos → (filename, line_no)
    filename=None for lines from the root file
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pysim8.asm import AssemblerError, assemble

# ── helpers ──────────────────────────────────────────────────────────


def _mock_url_resp(body: bytes) -> MagicMock:
    """Build a mock urllib response context manager returning body."""
    resp = MagicMock()
    resp.read.return_value = body
    resp.__enter__ = lambda s: s
    resp.__exit__ = MagicMock(return_value=False)
    return resp


def asm_inc(source: str, base_path: Path, arch: int = 1) -> list[int]:
    """Assemble with filesystem context; return code bytes."""
    return assemble(source, arch=arch, base_path=base_path).code


def asm_inc_labels(source: str, base_path: Path) -> dict[str, int]:
    return assemble(source, base_path=base_path).labels


def asm_inc_mapping(source: str, base_path: Path) -> dict[int, tuple[str | None, int]]:
    return assemble(source, base_path=base_path).mapping


def asm_inc_error(source: str, base_path: Path | None = None) -> AssemblerError:
    with pytest.raises(AssemblerError) as exc_info:
        assemble(source, base_path=base_path)
    return exc_info.value


# ── §5.8 Basic include ───────────────────────────────────────────────


class TestBasicInclude:
    """Single @include: code from two files assembles into one flat output."""

    def test_included_code_is_prepended(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\n")
        result = asm_inc('@include "lib.asm"\nHLT', tmp_path)
        assert result == assemble("MOV A, 1\nHLT").code

    def test_labels_from_included_file_are_visible(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("helper:\n  MOV A, 42\n  RET\n")
        labels = asm_inc_labels('@include "lib.asm"\nCALL helper\nHLT', tmp_path)
        assert "helper" in labels
        assert labels["helper"] == 0

    def test_root_label_can_call_included_label(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("add_one:\n  INC A\n  RET\n")
        code = asm_inc('@include "lib.asm"\nmain:\n  CALL add_one\n  HLT', tmp_path)
        assert len(code) > 0

    def test_include_can_appear_after_code(self, tmp_path: Path) -> None:
        (tmp_path / "data.asm").write_text("buf: DB 0\n")
        code = asm_inc('MOV A, 0\nHLT\n@include "data.asm"', tmp_path)
        assert code is not None

    def test_multiple_includes(self, tmp_path: Path) -> None:
        (tmp_path / "a.asm").write_text("MOV A, 1\n")
        (tmp_path / "b.asm").write_text("MOV B, 2\n")
        result = asm_inc('@include "a.asm"\n@include "b.asm"\nHLT', tmp_path)
        expected = assemble("MOV A, 1\nMOV B, 2\nHLT").code
        assert result == expected

    def test_empty_included_file(self, tmp_path: Path) -> None:
        (tmp_path / "empty.asm").write_text("")
        result = asm_inc('@include "empty.asm"\nHLT', tmp_path)
        assert result == [0]  # just HLT

    def test_include_only_comments(self, tmp_path: Path) -> None:
        (tmp_path / "comments.asm").write_text("; just a comment\n")
        result = asm_inc('@include "comments.asm"\nHLT', tmp_path)
        assert result == [0]


# ── §5.8 Path resolution ─────────────────────────────────────────────


class TestPathResolution:
    """Paths resolved relative to including file's directory."""

    def test_subdirectory_path(self, tmp_path: Path) -> None:
        lib = tmp_path / "lib"
        lib.mkdir()
        (lib / "print.asm").write_text("MOV A, 1\n")
        result = asm_inc('@include "lib/print.asm"\nHLT', tmp_path)
        assert result == assemble("MOV A, 1\nHLT").code

    def test_nested_include_resolves_relative_to_its_own_dir(self, tmp_path: Path) -> None:
        """lib/outer.asm includes charutil.asm (same dir), not root dir."""
        lib = tmp_path / "lib"
        lib.mkdir()
        (lib / "charutil.asm").write_text("MOV C, 3\n")
        (lib / "outer.asm").write_text('@include "charutil.asm"\nMOV D, 4\n')
        result = asm_inc('@include "lib/outer.asm"\nHLT', tmp_path)
        expected = assemble("MOV C, 3\nMOV D, 4\nHLT").code
        assert result == expected

    def test_dotslash_prefix(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 5\n")
        result = asm_inc('@include "./lib.asm"\nHLT', tmp_path)
        assert result == assemble("MOV A, 5\nHLT").code


# ── §5.8 Nesting ─────────────────────────────────────────────────────


class TestNesting:
    """Included files may themselves contain @include."""

    def test_two_levels(self, tmp_path: Path) -> None:
        (tmp_path / "inner.asm").write_text("MOV A, 1\n")
        (tmp_path / "outer.asm").write_text('@include "inner.asm"\nMOV B, 2\n')
        result = asm_inc('@include "outer.asm"\nHLT', tmp_path)
        expected = assemble("MOV A, 1\nMOV B, 2\nHLT").code
        assert result == expected

    def test_three_levels(self, tmp_path: Path) -> None:
        (tmp_path / "c.asm").write_text("MOV C, 3\n")
        (tmp_path / "b.asm").write_text('@include "c.asm"\nMOV B, 2\n')
        (tmp_path / "a.asm").write_text('@include "b.asm"\nMOV A, 1\n')
        result = asm_inc('@include "a.asm"\nHLT', tmp_path)
        expected = assemble("MOV C, 3\nMOV B, 2\nMOV A, 1\nHLT").code
        assert result == expected

    def test_max_depth_16_passes(self, tmp_path: Path) -> None:
        """Chain of exactly 16 levels must succeed."""
        _make_include_chain(tmp_path, depth=16)
        code = asm_inc('@include "level_1.asm"\nHLT', tmp_path)
        assert 0 in code  # HLT present


# ── §5.8 Trailing newline ─────────────────────────────────────────────


class TestTrailingNewline:
    """Missing trailing newline in included file must not merge lines."""

    def test_no_trailing_newline(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1")  # no \n
        result = asm_inc('@include "lib.asm"\nHLT', tmp_path)
        expected = assemble("MOV A, 1\nHLT").code
        assert result == expected

    def test_no_trailing_newline_with_label(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("fn:\n  RET")  # no trailing \n
        labels = asm_inc_labels('@include "lib.asm"\nHLT', tmp_path)
        assert "fn" in labels


# ── §5.8 Case insensitivity ───────────────────────────────────────────


class TestCaseInsensitivity:
    """@include keyword is case-insensitive (§5.8)."""

    @pytest.mark.parametrize(
        "directive",
        [
            pytest.param("@INCLUDE", id="upper"),
            pytest.param("@Include", id="mixed"),
            pytest.param("@include", id="lower"),
        ],
    )
    def test_case_variants(self, directive: str, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\n")
        result = asm_inc(f'{directive} "lib.asm"\nHLT', tmp_path)
        assert result == assemble("MOV A, 1\nHLT").code


# ── §5.8 Leading whitespace ───────────────────────────────────────────


class TestLeadingWhitespace:
    """Leading whitespace before @include is allowed."""

    @pytest.mark.parametrize(
        "indent",
        [
            pytest.param("  ", id="spaces"),
            pytest.param("\t", id="tab"),
        ],
    )
    def test_indented_include(self, indent: str, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\n")
        result = asm_inc(f'{indent}@include "lib.asm"\nHLT', tmp_path)
        assert result == assemble("MOV A, 1\nHLT").code


# ── §5.8 Source mapping ───────────────────────────────────────────────


class TestSourceMapping:
    """mapping is dict[int, tuple[str | None, int]] — (filename, line_no)."""

    def test_root_file_filename_is_none(self, tmp_path: Path) -> None:
        mapping = asm_inc_mapping("MOV A, 1\nHLT", tmp_path)
        for filename, _line in mapping.values():
            assert filename is None

    def test_included_file_has_filename(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\n")
        mapping = asm_inc_mapping('@include "lib.asm"\nHLT', tmp_path)
        filenames = {filename for filename, _ in mapping.values()}
        assert "lib.asm" in filenames

    def test_line_numbers_within_each_file(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\nMOV B, 2\n")
        mapping = asm_inc_mapping('@include "lib.asm"\nHLT', tmp_path)
        # lib.asm lines: MOV A,1 at line 1, MOV B,2 at line 2
        lib_locations = [(fn, ln) for fn, ln in mapping.values() if fn == "lib.asm"]
        lib_lines = sorted(ln for _, ln in lib_locations)
        assert lib_lines == [1, 2]

    def test_root_and_included_line_numbers_are_independent(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\n")
        mapping = asm_inc_mapping('@include "lib.asm"\nMOV B, 2\nHLT', tmp_path)
        # Root file: @include is line 1 (consumed), MOV B,2 is line 2, HLT is line 3
        root_lines = sorted(ln for fn, ln in mapping.values() if fn is None)
        assert root_lines == [2, 3]
        lib_lines = [ln for fn, ln in mapping.values() if fn == "lib.asm"]
        assert lib_lines == [1]


# ── §5.8 Namespace ────────────────────────────────────────────────────


class TestNamespace:
    """All labels share one flat namespace; duplicates across files are errors."""

    def test_duplicate_label_across_files(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("start:\n  RET\n")
        err = asm_inc_error('@include "lib.asm"\nstart:\n  HLT', tmp_path)
        assert "Duplicate label" in err.message
        assert "start" in err.message

    def test_forward_reference_to_included_label(self, tmp_path: Path) -> None:
        """Label in root file can jump to label defined in included file."""
        (tmp_path / "lib.asm").write_text("target:\n  HLT\n")
        code = asm_inc('JMP target\n@include "lib.asm"', tmp_path)
        assert len(code) > 0


# ── §5.8 Error: no filesystem context ────────────────────────────────


class TestNoFilesystemContext:
    """@include without base_path raises @include: no filesystem context."""

    def test_no_base_path(self) -> None:
        err = asm_inc_error('@include "lib.asm"', base_path=None)
        assert "@include: no filesystem context" in err.message

    def test_plain_assemble_raises(self) -> None:
        """assemble() without base_path does not support @include."""
        with pytest.raises(AssemblerError) as exc_info:
            assemble('@include "lib.asm"')
        assert "@include: no filesystem context" in exc_info.value.message


# ── §5.8 Error: file not found ────────────────────────────────────────


class TestFileNotFound:
    def test_missing_file(self, tmp_path: Path) -> None:
        err = asm_inc_error('@include "missing.asm"', tmp_path)
        assert "@include: file not found" in err.message
        assert "missing.asm" in err.message

    def test_error_line_number(self, tmp_path: Path) -> None:
        err = asm_inc_error('MOV A, 1\n@include "missing.asm"', tmp_path)
        assert err.line == 2


# ── §5.8 Error: circular include ─────────────────────────────────────


class TestCircularInclude:
    def test_direct_self_include(self, tmp_path: Path) -> None:
        (tmp_path / "self.asm").write_text('@include "self.asm"\n')
        err = asm_inc_error('@include "self.asm"', tmp_path)
        assert "@include: circular include" in err.message

    def test_indirect_cycle(self, tmp_path: Path) -> None:
        (tmp_path / "a.asm").write_text('@include "b.asm"\n')
        (tmp_path / "b.asm").write_text('@include "a.asm"\n')
        err = asm_inc_error('@include "a.asm"', tmp_path)
        assert "@include: circular include" in err.message

    def test_normalized_path_detection(self, tmp_path: Path) -> None:
        """./lib/../lib/print.asm is the same as lib/print.asm."""
        lib = tmp_path / "lib"
        lib.mkdir()
        (lib / "print.asm").write_text('@include "../lib/print.asm"\n')
        err = asm_inc_error('@include "lib/print.asm"', tmp_path)
        assert "@include: circular include" in err.message


# ── §5.8 Error: max depth ─────────────────────────────────────────────


class TestMaxDepth:
    def test_depth_17_raises(self, tmp_path: Path) -> None:
        _make_include_chain(tmp_path, depth=17)
        err = asm_inc_error('@include "level_1.asm"', tmp_path)
        assert "@include: max include depth exceeded" in err.message


# ── §5.8 Error: invalid syntax ───────────────────────────────────────


class TestInvalidSyntax:
    @pytest.mark.parametrize(
        "line",
        [
            pytest.param('@include "lib.asm" ; comment', id="trailing_comment"),
            pytest.param("@include lib.asm", id="no_quotes"),
            pytest.param("@include", id="no_path"),
            pytest.param('@include ""', id="empty_path"),
            pytest.param('@include "a.asm" "b.asm"', id="two_paths"),
        ],
    )
    def test_malformed_directive(self, line: str, tmp_path: Path) -> None:
        err = asm_inc_error(line, tmp_path)
        assert "@include: invalid syntax" in err.message


# ── §5.8 Error reporting: filename in errors ─────────────────────────


class TestErrorReporting:
    """Errors in included files report filename:line."""

    def test_error_filename_set_for_included_file(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("MOV A, 1\nINVALID_OP\n")
        err = asm_inc_error('@include "lib.asm"\nHLT', tmp_path)
        assert err.filename == "lib.asm"
        assert err.line == 2

    def test_error_filename_none_for_root(self, tmp_path: Path) -> None:
        err = asm_inc_error("INVALID_OP\n", tmp_path)
        assert err.filename is None
        assert err.line == 1

    def test_error_in_nested_include(self, tmp_path: Path) -> None:
        (tmp_path / "inner.asm").write_text("MOV A, 1\nBAD\n")
        (tmp_path / "outer.asm").write_text('@include "inner.asm"\n')
        err = asm_inc_error('@include "outer.asm"\nHLT', tmp_path)
        assert err.filename == "inner.asm"
        assert err.line == 2

    def test_undefined_label_in_included_file(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("JMP nowhere\n")
        err = asm_inc_error('@include "lib.asm"\nHLT', tmp_path)
        assert "Undefined label" in err.message
        assert err.filename == "lib.asm"
        assert err.line == 1


# ── §5.8 Binary file include ──────────────────────────────────────────


class TestBinaryInclude:
    """Binary files (null byte or non-UTF-8) are embedded as raw DB bytes (spec §5.8)."""

    def test_non_utf8_bytes_are_embedded(self, tmp_path: Path) -> None:
        data = bytes([0xFF, 0xFE, 0x00, 0x42])  # non-UTF-8 + null byte
        (tmp_path / "blob.bin").write_bytes(data)
        code = asm_inc('HLT\n@include "blob.bin"', tmp_path)
        assert code[-4:] == list(data)

    def test_null_byte_triggers_binary_mode(self, tmp_path: Path) -> None:
        # File is valid UTF-8 but contains a null byte → treated as binary
        data = bytes([0x41, 0x00, 0x42])  # "A\0B"
        (tmp_path / "null.bin").write_bytes(data)
        code = asm_inc('HLT\n@include "null.bin"', tmp_path)
        assert code[-3:] == list(data)

    def test_empty_binary_file_is_skipped(self, tmp_path: Path) -> None:
        (tmp_path / "empty.bin").write_bytes(b"")
        code_with = asm_inc('HLT\n@include "empty.bin"', tmp_path)
        code_without = asm_inc("HLT", tmp_path)
        assert code_with == code_without

    def test_binary_after_code(self, tmp_path: Path) -> None:
        # 16-byte table (null bytes + non-null), fits within page 0
        data = bytes([0x00, 0xFF] * 8)
        (tmp_path / "table.bin").write_bytes(data)
        code = asm_inc('JMP start\n@include "table.bin"\nstart: HLT', tmp_path)
        assert bytes(code[2:18]) == data  # 16 bytes after JMP (2 bytes)

    def test_binary_include_does_not_scan_for_nested_includes(self, tmp_path: Path) -> None:
        # Binary file whose bytes happen to spell @include — must not recurse.
        (tmp_path / "tricky.bin").write_bytes(b'\x00@include "other.asm"')
        code = asm_inc('HLT\n@include "tricky.bin"', tmp_path)
        assert code is not None  # no error about "other.asm" not existing

    def test_valid_utf8_without_null_bytes_is_still_text(self, tmp_path: Path) -> None:
        # UTF-8 without null bytes → treated as text assembly, not binary
        (tmp_path / "lib.asm").write_bytes("MOV A, 42\n".encode("utf-8"))
        code = asm_inc('HLT\n@include "lib.asm"', tmp_path)
        # lib.asm is parsed as assembly and MOV A,42 is assembled before HLT
        assert len(code) > 1


# ── §5.8 URL includes ────────────────────────────────────────────────


class TestUrlInclude:
    """URL @include (http/https) fetches remote text or binary at assemble time (spec §5.8)."""

    def test_text_url_include_assembles_label(self) -> None:
        with patch("urllib.request.urlopen", return_value=_mock_url_resp(b"urlsub: RET\n")):
            result = assemble('CALL urlsub\nHLT\n@include "https://example.com/lib.asm"')
        assert "urlsub" in result.labels

    def test_binary_url_include_embeds_bytes(self) -> None:
        data = bytes([0xFF, 0x00, 0x42])  # null byte → binary mode
        with patch("urllib.request.urlopen", return_value=_mock_url_resp(data)):
            result = assemble('HLT\n@include "https://example.com/blob.bin"')
        assert result.code[-3:] == list(data)

    def test_fetch_failure_raises_asm_error(self) -> None:
        from urllib.error import URLError

        with patch("urllib.request.urlopen", side_effect=URLError("timeout")):
            err = asm_inc_error('@include "https://example.com/missing.asm"')
        assert "fetch failed" in err.message

    def test_circular_url_include_raises_asm_error(self) -> None:
        from unittest.mock import patch

        # Simulate a.asm that includes itself via URL
        call_count = 0

        def urlopen_side_effect(url, timeout=None):  # noqa: ARG001
            nonlocal call_count
            call_count += 1
            if call_count > 1:
                pytest.fail("urlopen called more than once — circular include not detected")
            return _mock_url_resp(b'@include "https://example.com/self.asm"\n')

        with patch("urllib.request.urlopen", side_effect=urlopen_side_effect):
            err = asm_inc_error('@include "https://example.com/self.asm"')
        assert "circular include" in err.message

    def test_url_bypasses_no_filesystem_context_check(self) -> None:
        """URL includes work even without a base_path (in-memory assembly)."""
        with patch("urllib.request.urlopen", return_value=_mock_url_resp(b"remote: RET\n")):
            # base_path=None → normally @include raises "no filesystem context"
            result = assemble('CALL remote\nHLT\n@include "https://example.com/lib.asm"', base_path=None)
        assert "remote" in result.labels


# ── §5.8 + §5.9 @page + @include interaction ─────────────────────────


class TestPageIncludeInteraction:
    """@include after @page emits included content to that page."""

    def test_include_after_page_emits_to_page(self, tmp_path: Path) -> None:
        (tmp_path / "data.asm").write_text("DB 10, 20, 30\n")
        code = asm_inc('HLT\n@page 1\n@include "data.asm"', tmp_path)
        assert code[256] == 10
        assert code[257] == 20
        assert code[258] == 30

    def test_include_label_on_page(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("table: DB 42\n")
        result = assemble('HLT\n@page 1\n@include "lib.asm"', base_path=tmp_path)
        assert result.labels["table"] == 256  # page 1, offset 0

    def test_page_directive_inside_included_file(self, tmp_path: Path) -> None:
        (tmp_path / "pages.asm").write_text("@page 2\nDB 99\n")
        code = asm_inc('HLT\n@page 1\nDB 1\n@include "pages.asm"', tmp_path)
        assert code[256] == 1  # page 1
        assert code[512] == 99  # page 2 (switched inside include)


# ── §5.8 No include guards ───────────────────────────────────────────


class TestNoIncludeGuards:
    """Repeated inclusion duplicates content → typically causes duplicate label error."""

    def test_double_include_duplicate_label(self, tmp_path: Path) -> None:
        (tmp_path / "lib.asm").write_text("helper: RET\n")
        err = asm_inc_error('@include "lib.asm"\n@include "lib.asm"\nHLT', tmp_path)
        assert "Duplicate label" in err.message

    def test_double_include_no_label_ok(self, tmp_path: Path) -> None:
        (tmp_path / "data.asm").write_text("DB 1, 2\n")
        code = asm_inc('@include "data.asm"\n@include "data.asm"\nHLT', tmp_path)
        assert code[0:4] == [1, 2, 1, 2]


# ── helpers ───────────────────────────────────────────────────────────


def _make_include_chain(tmp_path: Path, depth: int) -> None:
    """Create depth files: level_1.asm includes level_2.asm, ..., level_N.asm has HLT."""
    for i in range(depth, 0, -1):
        if i == depth:
            (tmp_path / f"level_{i}.asm").write_text("HLT\n")
        else:
            (tmp_path / f"level_{i}.asm").write_text(f'@include "level_{i + 1}.asm"\n')
