"""Memory unit: 64KB byte-addressable memory."""

__all__ = ["Memory", "MEMORY_SIZE", "PAGE_SIZE", "IO_START", "SP_INIT"]

MEMORY_SIZE = 65536
PAGE_SIZE = 256
IO_START = 232
SP_INIT = 231


class Memory:
    """64KB memory backed by a bytearray."""

    MEMORY_SIZE = MEMORY_SIZE
    PAGE_SIZE = PAGE_SIZE
    IO_START = IO_START
    SP_INIT = SP_INIT

    __slots__ = ("_data",)

    def __init__(self) -> None:
        self._data = bytearray(MEMORY_SIZE)

    def __getitem__(self, addr: int) -> int:
        return self._data[addr]

    def __setitem__(self, addr: int, val: int) -> None:
        self._data[addr] = val & 0xFF

    def load(self, data: bytes | list[int], offset: int = 0) -> None:
        """Load data into memory at the given offset."""
        if offset + len(data) > MEMORY_SIZE:
            raise ValueError(
                f"Data ({len(data)} bytes at offset {offset}) "
                f"exceeds memory size ({MEMORY_SIZE})"
            )
        for i, b in enumerate(data):
            self._data[offset + i] = b & 0xFF

    def reset(self) -> None:
        """Zero-fill memory in-place."""
        self._data[:] = b"\x00" * MEMORY_SIZE
