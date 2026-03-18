; io.hex.asm
; API: print_hex
; In: A=uint8, D=cursor (232..255) | Out: D=next
;
; Example (DB -> print):
;   @include "std/io.hex.asm"
;   JMP start
; value: DB 0xAB
;
; start: MOV A, [value]
;        MOV D, 232
;        CALL print_hex
;        HLT

print_hex:
        PUSH A
        PUSH B
        MOV B, A
        SHR A, 4
        CALL hex_write_nibble
        MOV A, B
        AND A, 0x0F
        CALL hex_write_nibble
        POP B
        POP A
        RET

hex_write_nibble:
        CMP A, 10
        JC hex_write_decimal_digit
        ADD A, 55
        JMP hex_write_store
hex_write_decimal_digit:
        ADD A, 48
hex_write_store:
        MOV [D], A
        INC D
        RET
