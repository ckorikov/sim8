"""Assembler for the 8-bit CPU."""

from pysim8.asm.codegen import AssemblerError, AssembleResult, assemble

__all__ = ["assemble", "AssemblerError", "AssembleResult"]
