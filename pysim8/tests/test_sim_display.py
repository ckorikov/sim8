"""Display cell tests from spec/tests/tests-io-display.md (D1-D12)."""

import pytest

from conftest import run

from pysim8.sim.memory import IO_START, DISPLAY_END


IO_END = DISPLAY_END  # 0xFC — first byte past display region


# ── D.1 Character Output ──────────────────────────────────────────────


class TestDisplayCharacterOutput:
    """Spec §D.1 — character output to display cells."""

    def test_d1_write_first_cell(self) -> None:
        cpu = run("MOV [0xE8], 65\nHLT")
        assert cpu.mem[0xE8] == 65
        assert cpu.display() == "A"

    def test_d2_write_last_cell(self) -> None:
        cpu = run("MOV [0xFB], 90\nHLT")
        assert cpu.mem[0xFB] == 90
        assert "Z" in cpu.display()

    def test_d3_write_two_consecutive_cells(self) -> None:
        cpu = run("MOV [0xE8], 65\nMOV [0xE9], 66\nHLT")
        assert cpu.mem[0xE8] == 65
        assert cpu.mem[0xE9] == 66
        assert cpu.display().startswith("AB")

    def test_d4_null_byte_blank_cell(self) -> None:
        cpu = run("MOV [0xE8], 65\nMOV [0xE8], 0\nHLT")
        assert cpu.mem[0xE8] == 0
        assert cpu.display() == ""

    def test_d5_space_character(self) -> None:
        cpu = run("MOV [0xE8], 32\nHLT")
        assert cpu.mem[0xE8] == 32
        assert cpu.display() == ""  # trailing space stripped per spec


# ── D.2 Read-Back ────────────────────────────────────────────────────


class TestDisplayReadBack:
    """Spec §D.2 — read-back from display cells."""

    def test_d6_read_back_written_cell(self) -> None:
        cpu = run("MOV [0xE8], 65\nMOV A, [0xE8]\nHLT")
        assert cpu.a == 65

    def test_d7_initial_value_zero(self) -> None:
        cpu = run("MOV A, [0xE8]\nHLT")
        assert cpu.a == 0


# ── D.3 Boundary ─────────────────────────────────────────────────────


class TestDisplayBoundary:
    """Spec §D.3 — boundary between display cells and adjacent regions."""

    def test_d8_address_before_display_is_data(self) -> None:
        cpu = run("MOV [0xE7], 42\nHLT")
        assert cpu.mem[0xE7] == 42
        # No display cells should have been set
        for addr in range(IO_START, IO_END):
            assert cpu.mem[addr] == 0

    def test_d9_uart_port_does_not_affect_display(self) -> None:
        # 0xFC is UART TX_DATA — write there must not affect display cells
        cpu = run("MOV [0xFC], 65\nHLT")
        for addr in range(IO_START, IO_END):
            assert cpu.mem[addr] == 0
        assert cpu.display() == ""


# ── D.4 DP Interaction ───────────────────────────────────────────────


class TestDisplayDpInteraction:
    """Spec §D.4 — display active only when DP=0."""

    def test_d10_dp_zero_activates_display(self) -> None:
        cpu = run("MOV DP, 0\nMOV [0xE8], 65\nHLT")
        assert cpu.mem[0xE8] == 65
        assert cpu.display() == "A"

    def test_d11_dp_nonzero_writes_data_not_display(self) -> None:
        cpu = run("MOV DP, 1\nMOV [0xE8], 65\nHLT")
        # Display cells on page 0 unaffected
        assert cpu.mem[0xE8] == 0
        assert cpu.display() == ""
        # Data at page 1 offset 0xE8 = address 256 + 0xE8 = 0x1E8
        assert cpu.mem[0x1E8] == 65

    def test_d12_dp_nonzero_reads_data_not_display(self) -> None:
        cpu = run("MOV DP, 1\nMOV A, [0xE8]\nHLT")
        # Reading page 1 offset 0xE8: initial value is 0
        assert cpu.a == 0
