"""ALU: purely stateless arithmetic/logic operations.

Every method returns a tuple — no side effects, no dependency on registers/flags.
"""

__all__ = ["ALU"]


class ALU:
    """Stateless ALU. All methods are @staticmethod returning tuples."""

    @staticmethod
    def add(a: int, b: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). carry = overflow > 255."""
        raw = a + b
        carry = raw > 255
        result = raw & 0xFF
        return result, carry, result == 0

    @staticmethod
    def sub(a: int, b: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). carry = underflow < 0."""
        raw = a - b
        carry = raw < 0
        result = raw % 256
        return result, carry, result == 0

    @staticmethod
    def mul(a: int, b: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). carry = overflow > 255."""
        raw = a * b
        carry = raw > 255
        result = raw & 0xFF
        return result, carry, result == 0

    @staticmethod
    def div(a: int, b: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). Integer division, no overflow possible."""
        result = a // b
        carry = result > 255 or result < 0
        result = result % 256
        return result, carry, result == 0

    @staticmethod
    def inc(a: int) -> tuple[int, bool, bool]:
        """(result, carry, zero)."""
        raw = a + 1
        carry = raw > 255
        result = raw & 0xFF
        return result, carry, result == 0

    @staticmethod
    def dec(a: int) -> tuple[int, bool, bool]:
        """(result, carry, zero)."""
        raw = a - 1
        carry = raw < 0
        result = raw % 256
        return result, carry, result == 0

    @staticmethod
    def and_op(a: int, b: int) -> tuple[int, bool]:
        """(result, zero). Carry is always False for bitwise ops."""
        result = a & b
        return result, result == 0

    @staticmethod
    def or_op(a: int, b: int) -> tuple[int, bool]:
        """(result, zero)."""
        result = a | b
        return result, result == 0

    @staticmethod
    def xor_op(a: int, b: int) -> tuple[int, bool]:
        """(result, zero)."""
        result = a ^ b
        return result, result == 0

    @staticmethod
    def not_op(a: int) -> tuple[int, bool]:
        """(result, zero). NOT = XOR 0xFF."""
        result = a ^ 0xFF
        return result, result == 0

    @staticmethod
    def shl(value: int, count: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). Requires count > 0."""
        raw = value * (1 << count)
        carry = raw > 255
        result = raw & 0xFF
        return result, carry, result == 0

    @staticmethod
    def shr(value: int, count: int) -> tuple[int, bool, bool]:
        """(result, carry, zero). Requires count > 0.

        carry = any bits shifted out.
        """
        carry = (value % (1 << count)) != 0
        result = value >> count
        return result, carry, result == 0
