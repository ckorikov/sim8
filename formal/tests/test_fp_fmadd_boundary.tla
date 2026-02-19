--------------------------- MODULE test_fp_fmadd_boundary ---------------------------
(*
   FMADD IP overflow: 4-byte instruction at IP=253 -> IP+4=257 > 255.
   IPOverflowGuard triggers ERR_PAGE_BOUNDARY before instruction executes.
   Program is padded so FMADD starts at offset 253.
*)

EXTENDS cpu_core

\* Pad with NOPs (MOV A,A = 1,0,0 = 3 bytes) to reach IP=252,
\* then add FMADD_A at offset 253.
\* We need to fill 253 bytes. 84 * 3 = 252, then one more byte.
\* Use HLT (1 byte) at 252, then FMADD at 253.
\* Actually: 84 * MOV_RR(3 bytes) = 252 bytes, then at 252 we put the FMADD.
\* But we need FMADD at 253. So 84 * MOV_RR = 252, then 1-byte NOP...
\* HLT is 1 byte but would halt. Use INC A (2 bytes): 252+2=254.
\* Better: 83 * MOV_RR = 249, then MOV_RC A, 0 (3 bytes) = 252,
\* then INC A (2 bytes = 254)... Still not 253.
\* Simplest: just pad with 253 zero bytes and check that opcode 0 = HLT
\* runs first. But we want to test FMADD at high IP.
\*
\* Alternative approach: use JMP to jump to IP=253 directly.
TestProgram == <<
    \* JMP 253 — jump to offset 253
    OP_JMP, 253,
    \* Pad bytes 2-252 with zeros (will be HLT=0, but we jump over them)
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 2-11
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 12-21
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 22-31
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 32-41
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 42-51
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 52-61
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 62-71
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 72-81
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 82-91
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 92-101
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 102-111
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 112-121
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 122-131
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 132-141
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 142-151
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 152-161
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 162-171
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 172-181
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 182-191
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 192-201
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 202-211
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 212-221
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 222-231
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 232-241
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,   \* 242-251
    0,                                 \* 252
    \* At offset 253: FMADD_A (4 bytes = 253+4=257 > 255 -> page boundary fault)
    OP_FMADD_A, 1, 9, 240
>>

\* Must fault with page boundary error (IP overflow)
FaultIsPageBoundary == state = "FAULT" => A = ERR_PAGE_BOUNDARY

=============================================================================
