"""Memory unit: 64KB byte-addressable memory."""

from pysim8.constants import IO_START, MEM_SIZE, PAGE_SIZE, SP_INIT

__all__ = ["Memory", "MEM_SIZE", "PAGE_SIZE", "IO_START", "SP_INIT"]


class Memory:
    """64KB memory backed by a bytearray."""

    __slots__ = ("_data", "_non_zero")

    def __init__(self) -> None:
        self._data = bytearray(MEM_SIZE)
        self._non_zero = 0

    def _is_io(self, addr: int) -> bool:
        return addr < PAGE_SIZE and addr >= IO_START

    def __getitem__(self, addr: int) -> int:
        return self._data[addr]

    def __setitem__(self, addr: int, val: int) -> None:
        byte = val & 0xFF
        old = self._data[addr]
        self._data[addr] = byte
        if not self._is_io(addr):
            if old == 0 and byte != 0:
                self._non_zero += 1
            elif old != 0 and byte == 0:
                self._non_zero -= 1

    def load(self, data: bytes | list[int], offset: int = 0) -> None:
        """Load data into memory at the given offset."""
        if offset + len(data) > MEM_SIZE:
            raise ValueError(f"Data ({len(data)} bytes at offset {offset}) exceeds memory size ({MEM_SIZE})")
        for i, b in enumerate(data):
            self[offset + i] = b

    def reset(self) -> None:
        """Zero-fill memory in-place."""
        self._data[:] = b"\x00" * MEM_SIZE
        self._non_zero = 0

    def used_bytes(self) -> int:
        """Count non-zero bytes excluding the I/O region (232–255 of page 0)."""
        return self._non_zero
