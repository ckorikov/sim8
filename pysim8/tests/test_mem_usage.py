"""Tests for Memory.used_bytes() and CPU.peak_mem.

Covers:
- Memory.used_bytes(): counting non-zero bytes, IO exclusion, boundary cases.
- CPU.peak_mem: initialized at 0, updated after each step, tracks maximum,
  cleared by reset().
- Integration via assembled programs.
"""

import pytest
from conftest import run

from pysim8.asm import assemble
from pysim8.sim import CPU
from pysim8.sim.memory import IO_START, PAGE_SIZE, Memory

# ── Memory.used_bytes() ───────────────────────────────────────────────


class TestMemoryUsedBytes:
    """Unit tests for Memory.used_bytes()."""

    def test_empty_memory_returns_zero(self) -> None:
        m = Memory()
        assert m.used_bytes() == 0

    def test_write_one_byte_at_addr_zero(self) -> None:
        m = Memory()
        m[0] = 0x01
        assert m.used_bytes() == 1

    def test_write_one_byte_at_addr_100(self) -> None:
        m = Memory()
        m[100] = 0xFF
        assert m.used_bytes() == 1

    def test_io_region_excluded_single_byte(self) -> None:
        """A byte written inside the IO region (page 0, 232-255) is excluded."""
        m = Memory()
        m[IO_START] = 0xFF
        assert m.used_bytes() == 0

    def test_io_region_excluded_all_bytes(self) -> None:
        """All 24 IO region addresses are excluded even when all set."""
        m = Memory()
        for addr in range(IO_START, PAGE_SIZE):
            m[addr] = 0xFF
        assert m.used_bytes() == 0

    def test_io_region_last_address_excluded(self) -> None:
        """Addr 255 (last IO byte) is excluded."""
        m = Memory()
        m[255] = 0xFF
        assert m.used_bytes() == 0

    def test_byte_just_before_io_is_counted(self) -> None:
        """Addr IO_START-1 (231) is not in the IO region and must be counted."""
        m = Memory()
        m[IO_START - 1] = 0x42
        assert m.used_bytes() == 1

    def test_addr_256_counted_even_if_io_start_offset_matches(self) -> None:
        """Addr 256 is on page 1; the IO exclusion only applies to page 0."""
        m = Memory()
        m[PAGE_SIZE] = 0x01  # addr 256 = page 1, offset 0
        assert m.used_bytes() == 1

    def test_multiple_non_zero_bytes(self) -> None:
        m = Memory()
        m[10] = 0x01
        m[20] = 0x02
        m[30] = 0x03
        assert m.used_bytes() == 3

    def test_overwrite_with_zero_decrements(self) -> None:
        """Setting a byte back to 0 should reduce the count."""
        m = Memory()
        m[50] = 0xAB
        assert m.used_bytes() == 1
        m[50] = 0x00
        assert m.used_bytes() == 0

    def test_zero_byte_not_counted(self) -> None:
        """Explicitly writing 0 to an already-zero cell does not add to count."""
        m = Memory()
        m[99] = 0x00
        assert m.used_bytes() == 0

    @pytest.mark.parametrize(
        "addr, expected",
        [
            pytest.param(IO_START - 1, 1, id="just_before_io"),
            pytest.param(IO_START, 0, id="io_start"),
            pytest.param(PAGE_SIZE - 1, 0, id="io_end"),
            pytest.param(PAGE_SIZE, 1, id="page1_start"),
        ],
    )
    def test_io_boundary_parametrized(self, addr: int, expected: int) -> None:
        m = Memory()
        m[addr] = 0x55
        assert m.used_bytes() == expected


# ── CPU.peak_mem ──────────────────────────────────────────────────────


class TestCpuPeakMem:
    """Unit tests for CPU.peak_mem."""

    def test_peak_mem_zero_before_any_step(self) -> None:
        """After load() but before any step(), peak_mem is 0."""
        code = assemble("MOV A, 42\nHLT").code
        cpu = CPU()
        cpu.load(code)
        assert cpu.peak_mem == 0

    def test_peak_mem_positive_after_first_step(self) -> None:
        """peak_mem is updated after each step; after the first step it reflects
        the non-zero code bytes already in memory."""
        code = assemble("MOV A, 42\nHLT").code
        cpu = CPU()
        cpu.load(code)
        cpu.step()
        # code = [6, 0, 42, 0]; non-zero bytes: 6, 42 = 2
        assert cpu.peak_mem > 0

    def test_reset_clears_peak_mem(self) -> None:
        """reset() must bring peak_mem back to 0."""
        cpu = run("MOV A, 1\nHLT")
        assert cpu.peak_mem > 0
        cpu.reset()
        assert cpu.peak_mem == 0

    def test_peak_tracks_maximum_not_current(self) -> None:
        """If memory shrinks (byte overwritten with 0), peak stays at prior max."""
        # MOV A,1 -> MOV [50],A (mem[50]=1) -> MOV A,0 -> MOV [50],A (mem[50]=0)
        # Peak is captured when mem[50] was still 1.
        cpu = run("MOV A, 1\nMOV [50], A\nMOV A, 0\nMOV [50], A\nHLT")
        final_used = cpu.mem.used_bytes()
        # Peak must be strictly greater than final used count
        # (because one byte was zeroed out).
        assert cpu.peak_mem > final_used

    def test_peak_mem_monotonically_non_decreasing(self) -> None:
        """Collect peak_mem after each step and verify it never decreases."""
        code = assemble("MOV A, 1\nMOV [50], A\nMOV A, 0\nMOV [50], A\nHLT").code
        cpu = CPU()
        cpu.load(code)

        peaks: list[int] = []
        while cpu.step():
            peaks.append(cpu.peak_mem)
        peaks.append(cpu.peak_mem)

        for i in range(1, len(peaks)):
            assert peaks[i] >= peaks[i - 1], f"peak_mem decreased at step {i}: {peaks[i - 1]} -> {peaks[i]}"


# ── Integration ───────────────────────────────────────────────────────


class TestPeakMemIntegration:
    """Integration tests using assembled programs."""

    def test_memory_write_increases_peak(self) -> None:
        """A program that stores a value in memory produces peak_mem > 0."""
        cpu = run("MOV [80], 77\nHLT")
        assert cpu.peak_mem > 0

    def test_code_only_program_peak_equals_nonzero_code_bytes(self) -> None:
        """With no data writes, peak_mem equals the number of non-zero code bytes."""
        # MOV A,1 -> MOV B,2 -> HLT
        # Assembled: [6,0,1, 6,1,2, 0]; non-zero: 6,1,6,1,2 = 5 bytes
        code = assemble("MOV A, 1\nMOV B, 2\nHLT").code
        expected_nonzero = sum(1 for b in code if b != 0)

        cpu = CPU()
        cpu.load(code)
        cpu.run()

        assert cpu.peak_mem == expected_nonzero

    def test_data_write_adds_to_code_bytes(self) -> None:
        """Storing a non-zero value adds to the count beyond just code bytes."""
        # MOV [50], 99 -> HLT: code = [7, 50, 99, 0]
        # non-zero code bytes: 7,50,99 = 3
        # After execution mem[50] = 99 (already in code at addr 2, but addr 50 is separate)
        # Actually mem[50]=99 is a separate write at addr 50, adding 1 more non-zero byte.
        code = assemble("MOV [50], 99\nHLT").code
        code_nonzero = sum(1 for b in code if b != 0)

        cpu = CPU()
        cpu.load(code)
        cpu.run()

        # peak_mem must exceed the code-only non-zero count
        assert cpu.peak_mem > code_nonzero

    def test_peak_stays_at_max_after_zero_store(self) -> None:
        """Peak is the maximum over all steps, not the final memory state."""
        cpu = run("MOV A, 1\nMOV [60], A\nMOV A, 0\nMOV [60], A\nHLT")
        # After the last store, mem[60] = 0, so used_bytes decreases.
        # But peak must have captured the higher value from step 2.
        assert cpu.peak_mem > cpu.mem.used_bytes()

    def test_hlt_only_program_peak_zero(self) -> None:
        """HLT assembled to [0x00]; no non-zero bytes in memory, peak stays 0.

        HLT is opcode 0 and is not counted as a step (cost=0), so
        peak_mem is never updated — it remains 0 from reset.
        """
        cpu = run("HLT")
        # HLT opcode is 0 so zero bytes; no non-HLT steps → peak never updated.
        assert cpu.peak_mem == 0
