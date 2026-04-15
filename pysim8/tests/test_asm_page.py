"""Assembler tests for @page directive and {label} expression.

Tests multi-page assembly: @page N, {label} page references,
cross-page jump validation, flat binary output.
"""

import pytest
from conftest import asm_bytes as asm
from conftest import asm_error, asm_labels

from pysim8.asm import assemble
from pysim8.asm.parser import (
    OpPageLabel,
    ParseError,
    parse_line,
)


def parse_error(source: str) -> ParseError:
    """Parse a single line expecting an error."""
    with pytest.raises(ParseError) as exc_info:
        parse_line(source, 1, arch=2)
    return exc_info.value


# ── @page directive parsing ──────────────────────────────────────────


class TestPageDirectiveParsing:
    """Parse @page N from source lines."""

    def test_page_decimal(self) -> None:
        p = parse_line("@page 1", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 1

    def test_page_hex(self) -> None:
        p = parse_line("@page 0xFF", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 255

    def test_page_case_insensitive(self) -> None:
        p = parse_line("@PAGE 2", 1, arch=2)
        assert p.mnemonic == "@PAGE"

    def test_page_with_comment(self) -> None:
        p = parse_line("@page 1 ; matrix data", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 1

    def test_page_0_valid(self) -> None:
        p = parse_line("@page 0", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 0

    def test_page_0_with_offset(self) -> None:
        p = parse_line("@page 0, 42", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 0
        assert p.operands[1].value == 42

    def test_page_1_with_offset(self) -> None:
        p = parse_line("@page 1, 10", 1, arch=2)
        assert p.mnemonic == "@PAGE"
        assert p.operands[0].value == 1
        assert p.operands[1].value == 10

    def test_page_256_error(self) -> None:
        e = parse_error("@page 256")
        assert "must be 0-255" in e.message

    def test_page_offset_invalid(self) -> None:
        e = parse_error("@page 1, abc")
        assert "invalid offset" in e.message

    def test_page_offset_out_of_range(self) -> None:
        e = parse_error("@page 1, 256")
        assert "offset must be 0-255" in e.message

    def test_page_missing_number(self) -> None:
        e = parse_error("@page")
        assert "missing page number" in e.message

    def test_page_invalid_syntax(self) -> None:
        e = parse_error("@page abc")
        assert "invalid syntax" in e.message

    def test_page_with_label_on_line(self) -> None:
        """@page must be on its own line — label prefix causes syntax error."""
        e = asm_error("label: @page 1")
        assert "syntax error" in e.message.lower()


# ── {label} expression parsing ───────────────────────────────────────


class TestPageLabelParsing:
    """Parse {label} operand."""

    def test_page_label_operand(self) -> None:
        p = parse_line("MOV DP, {matrix}", 1, arch=2)
        assert isinstance(p.operands[1], OpPageLabel)
        assert p.operands[1].name == "matrix"

    def test_page_label_case_insensitive(self) -> None:
        p = parse_line("MOV A, {Matrix}", 1, arch=2)
        assert isinstance(p.operands[1], OpPageLabel)
        assert p.operands[1].name == "matrix"

    def test_empty_braces_error(self) -> None:
        e = parse_error("MOV A, {}")
        assert "invalid operand" in e.message.lower()

    def test_number_in_braces_error(self) -> None:
        e = parse_error("MOV A, {123}")
        assert "syntax error" in e.message.lower()

    def test_bracket_brace_combo_error(self) -> None:
        """[{x}] is a syntax error."""
        e = parse_error("MOV A, [{x}]")
        assert "invalid address" in e.message.lower()


# ── Basic @page assembly ─────────────────────────────────────────────


class TestPageAssembly:
    """Assemble programs with @page directives."""

    def test_simple_data_page(self) -> None:
        """Data on page 1, code on page 0."""
        source = "HLT\n\n@page 1\nDB 65, 66, 67"
        code = asm(source)
        # Output: page 0 (256 bytes) + page 1 (256 bytes) = 512 bytes
        assert len(code) == 512
        assert code[0] == 0  # HLT opcode
        assert code[256] == 65  # page 1 offset 0
        assert code[257] == 66
        assert code[258] == 67

    def test_multiple_pages(self) -> None:
        """Multiple @page directives."""
        source = "HLT\n@page 1\nDB 10\n@page 2\nDB 20"
        code = asm(source)
        assert len(code) == 768  # 3 pages
        assert code[256] == 10  # page 1
        assert code[512] == 20  # page 2

    def test_non_sequential_pages(self) -> None:
        """Pages don't need to be sequential: @page 3 then @page 1."""
        source = "HLT\n@page 3\nDB 30\n@page 1\nDB 10"
        code = asm(source)
        assert len(code) == 1024  # pages 0-3
        assert code[768] == 30  # page 3
        assert code[256] == 10  # page 1

    def test_no_page_backward_compat(self) -> None:
        """Without @page, output is same as before (no padding)."""
        source = "MOV A, 42\nHLT"
        code = asm(source)
        assert len(code) == 4  # MOV A, 42 (3 bytes) + HLT (1 byte)

    def test_page_0_padding(self) -> None:
        """With @page, page 0 is padded to 256 bytes."""
        source = "HLT\n@page 1\nDB 1"
        code = asm(source)
        assert len(code) == 512
        assert code[0] == 0  # HLT
        assert code[1] == 0  # padding
        assert code[255] == 0  # end of page 0 padding
        assert code[256] == 1  # page 1 data

    def test_sparse_pages_zero_filled(self) -> None:
        """Gap pages are zero-filled."""
        source = "HLT\n@page 3\nDB 42"
        code = asm(source)
        assert len(code) == 1024  # pages 0-3
        # Pages 1 and 2 are all zeros
        assert all(b == 0 for b in code[256:768])
        assert code[768] == 42


# ── Labels with @page ────────────────────────────────────────────────


class TestPageLabels:
    """Label resolution across pages."""

    def test_label_on_page_1(self) -> None:
        """Label on page 1 resolves correctly."""
        source = "HLT\n@page 1\nmatrix: DB 42"
        labels = asm_labels(source)
        assert labels["matrix"] == 256  # page 1, offset 0

    def test_label_offset_on_page(self) -> None:
        """Label offset within a page."""
        source = "HLT\n@page 1\nDB 0, 0, 0\ntarget: DB 42"
        labels = asm_labels(source)
        assert labels["target"] == 259  # page 1, offset 3

    def test_page_label_expression(self) -> None:
        """{label} resolves to page number."""
        source = "MOV DP, {data}\nHLT\n@page 1\ndata: DB 42"
        code = asm(source)
        # MOV DP, {data} → MOV DP, 1 (page number)
        assert code[2] == 1  # immediate value = page 1

    def test_page_label_page_0(self) -> None:
        """{label} for page 0 label → 0."""
        source = "start: HLT\nMOV A, {start}"
        code = asm(source)
        # MOV A, {start} → MOV A, 0
        assert code[3] == 0  # page 0

    def test_offset_label_cross_page(self) -> None:
        """Regular label reference gives page-local offset."""
        source = "MOV A, [data]\nHLT\n@page 1\ndata: DB 42"
        code = asm(source)
        # [data] resolves to offset 0 (within page 1), NOT 256
        assert code[1] == 0  # direct address = offset 0 on current DP page

    def test_undefined_page_label(self) -> None:
        """{undefined} is an error."""
        e = asm_error("MOV DP, {undefined}\nHLT")
        assert "undefined label" in e.message.lower()

    def test_page_label_in_push(self) -> None:
        """{label} works with PUSH."""
        source = "PUSH {data}\nHLT\n@page 2\ndata: DB 1"
        code = asm(source)
        assert code[1] == 2  # page 2

    def test_page_label_in_cmp(self) -> None:
        """{label} works with CMP."""
        source = "CMP A, {data}\nHLT\n@page 3\ndata: DB 1"
        code = asm(source)
        # CMP A, imm → opcode, reg, imm
        assert code[2] == 3  # page 3


# ── Cross-page jump validation ───────────────────────────────────────


class TestCrossPageJumps:
    """Cross-page JMP/CALL is an error."""

    def test_jmp_page0_to_page1_error(self) -> None:
        """JMP from page 0 to label on page 1 → error."""
        source = "JMP target\n@page 1\ntarget: DB 42"
        e = asm_error(source)
        assert "jump target" in e.message.lower()
        assert "page 1" in e.message

    def test_call_page0_to_page1_error(self) -> None:
        """CALL from page 0 to label on page 1 → error."""
        source = "CALL target\n@page 1\ntarget: DB 42"
        e = asm_error(source)
        assert "jump target" in e.message.lower()

    def test_conditional_jump_cross_page_error(self) -> None:
        """Conditional jump cross-page → error."""
        source = "JE target\n@page 1\ntarget: DB 42"
        e = asm_error(source)
        assert "page 1" in e.message

    def test_jmp_same_page_ok(self) -> None:
        """JMP within same page > 0 is OK (overlay code)."""
        source = "HLT\n@page 1\nstart: MOV A, 1\nJMP start"
        code = asm(source)
        assert len(code) == 512

    def test_cross_page_jump_page2_to_page1(self) -> None:
        """JMP from page 2 to page 1 → error."""
        source = "HLT\n@page 1\ntarget: DB 42\n@page 2\nJMP target"
        e = asm_error(source)
        assert "cross-page jump" in e.message.lower()

    def test_mov_cross_page_label_ok(self) -> None:
        """MOV with cross-page label is fine (not a jump)."""
        source = "MOV A, [data]\nHLT\n@page 1\ndata: DB 42"
        # Should NOT error — only JMP/CALL check cross-page
        code = asm(source)
        assert len(code) == 512


# ── @page error conditions ───────────────────────────────────────────


class TestPageErrors:
    """@page validation errors."""

    def test_page_overflow(self) -> None:
        """Page > 256 bytes → error."""
        data = ", ".join(["0"] * 257)
        source = f"HLT\n@page 1\nDB {data}"
        e = asm_error(source)
        assert "overflow" in e.message.lower()

    def test_page_0_code_still_works(self) -> None:
        """Code on page 0 still works normally with @page."""
        source = "MOV A, 42\nMOV B, 10\nHLT\n@page 1\nDB 1"
        code = asm(source)
        assert code[0:7] == [6, 0, 42, 6, 1, 10, 0]  # MOV A,42 + MOV B,10 + HLT

    def test_backward_seek_overwrites(self) -> None:
        """@page N, M with M < current position overwrites existing bytes."""
        # HLT=0x00, MOV A,1 = [6,0,1] → 4 bytes at offsets 0-3
        # @page 0, 1 seeks back to offset 1, DB 0xFF overwrites byte 1
        source = "HLT\nMOV A, 1\n@page 0, 1\nDB 0xFF\n@page 1\nDB 0"
        code = asm(source)
        assert code[0] == 0  # HLT untouched
        assert code[1] == 0xFF  # overwritten (was MOV opcode 6)
        assert code[2] == 0  # original MOV reg A (0)
        assert code[3] == 1  # original MOV constant

    def test_backward_seek_then_forward(self) -> None:
        """Backward seek, write, then continue appending."""
        # DB 1,2,3,4 → [1,2,3,4] (4 bytes)
        # @page 0, 1 → cursor at 1
        # DB 0xAA → overwrites byte 1 → cursor at 2
        # DB 0xBB → overwrites byte 2 → cursor at 3
        # DB 0xCC → overwrites byte 3 → cursor at 4 (== len, next is append)
        # DB 0xDD → appends → byte 4
        source = "DB 1, 2, 3, 4\n@page 0, 1\nDB 0xAA, 0xBB, 0xCC, 0xDD\n@page 1\nDB 0"
        code = asm(source)
        assert code[0] == 1  # untouched
        assert code[1] == 0xAA
        assert code[2] == 0xBB
        assert code[3] == 0xCC
        assert code[4] == 0xDD  # appended

    def test_backward_seek_label(self) -> None:
        """Label placed after backward seek gets correct offset."""
        source = "DB 1, 2, 3\n@page 0, 1\nmarker: DB 42\n@page 1\nDB 0"
        code = asm(source)
        assert code[1] == 42
        # Check that label resolved to offset 1
        result = assemble(source)
        assert result.labels["marker"] == 1


class TestPageOffset:
    """@page N, M offset feature."""

    def test_page_0_offset(self) -> None:
        """@page 0, M advances offset on page 0."""
        source = "HLT\n@page 0, 10\nDB 42\n@page 1\nDB 1"
        code = asm(source)
        assert code[0] == 0  # HLT
        assert code[10] == 42  # after offset advance
        for i in range(1, 10):
            assert code[i] == 0  # zero-filled gap

    def test_page_1_offset(self) -> None:
        """@page 1, 10 starts at offset 10 on page 1."""
        source = "HLT\n@page 1, 10\nDB 42"
        code = asm(source)
        assert code[256 + 10] == 42
        for i in range(256, 256 + 10):
            assert code[i] == 0

    def test_page_0_resume(self) -> None:
        """@page 0 after @page 1 resumes page 0."""
        source = "MOV A, 1\n@page 1\nDB 42\n@page 0\nHLT"
        code = asm(source)
        assert code[0:3] == [6, 0, 1]  # MOV A, 1
        assert code[3] == 0  # HLT (resumed after MOV)
        assert code[256] == 42  # page 1

    def test_page_nonzero_resume(self) -> None:
        """@page N (N>0) twice resumes from current position."""
        source = "HLT\n@page 1\nDB 1\n@page 2\nDB 2\n@page 1\nDB 3"
        code = asm(source)
        assert code[256] == 1
        assert code[257] == 3  # resumed

    def test_page_0_resume_with_offset(self) -> None:
        """@page 0, M after @page 1 resumes page 0 at offset M."""
        source = "DB 1, 2\n@page 1\nDB 42\n@page 0, 10\nDB 99"
        code = asm(source)
        assert code[0] == 1
        assert code[1] == 2
        assert code[10] == 99
        assert code[256] == 42

    def test_page_0_noop_at_start(self) -> None:
        """@page 0 at start is a no-op (already on page 0)."""
        source = "@page 0\nHLT\n@page 1\nDB 42"
        code = asm(source)
        assert code[0] == 0  # HLT
        assert code[256] == 42

    def test_label_after_offset(self) -> None:
        """Label after @page 0, M gets correct offset."""
        source = "JMP loader\n@page 0, 20\nloader: HLT\n@page 1\nDB 1"
        code = asm(source)
        assert code[1] == 20  # JMP target = offset 20
        assert code[20] == 0  # HLT at offset 20


# ── Instructions on pages > 0 (overlay support) ─────────────────────


class TestOverlayCode:
    """Instructions on pages > 0 for overlay use case."""

    def test_instructions_on_page_1(self) -> None:
        """Instructions after @page are assembled normally."""
        source = "HLT\n@page 1\nMOV A, 42\nHLT"
        code = asm(source)
        assert code[256] == 6  # MOV opcode
        assert code[257] == 0  # reg A
        assert code[258] == 42  # immediate
        assert code[259] == 0  # HLT

    def test_overlay_labels(self) -> None:
        """Labels in overlay code use page-local offsets."""
        result = assemble("HLT\n@page 2\nstart: MOV A, 1\nloop: JMP loop")
        assert result.labels["start"] == 512  # page 2, offset 0
        assert result.labels["loop"] == 515  # page 2, offset 3
        # JMP loop → offset 3 within page 2
        assert result.code[515 + 1] == 3  # jump target = page-local offset

    def test_overlay_with_data_reference(self) -> None:
        """{label} in overlay code resolves to page number."""
        source = "HLT\n@page 1\ndata: DB 42\n@page 2\nMOV DP, {data}"
        code = asm(source)
        # MOV DP, {data} → MOV DP, 1
        assert code[514] == 1  # page number of 'data'
