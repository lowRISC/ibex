.text
.section .text.func, "ax", @progbits
.align 2
.globl illegal_opcodes
.type illegal_opcodes, @function

illegal_opcodes:
    addi    sp, sp, -8
    sw      ra, 4(sp)

    .option push
    .option rvc

    .half   0x4002  #c_lwsp
    .half   0x6002  #c_ldsp
    .half   0x2002  #c_lqsp
    .half   0x8002  #c_jr
    .half   0x9C61  #c_reserv_1
    .half   0x9C41  #c_reserv_0
    .half   0x6201  # c_lui
    .half   0x6101  #c_addi16sp
    .half   0x0004  #c_addi4spn
    .half   0x0000  #c_illegal


    .half   0xA002  # [15:13]=101, [1:0]=10  -> cp_10 bin=5
    .half   0xE002  # [15:13]=111, [1:0]=10  -> cp_10 bin=7
    .half   0x2000  # [15:13]=001, [1:0]=00 -> cp_00 bin=1
    .half   0x6000  # [15:13]=011, [1:0]=00 -> cp_00 bin=3
    .half   0x8000  # [15:13]=100, [1:0]=00 -> cp_00 bin=4
    .half   0xA000  # [15:13]=101, [1:0]=00 -> cp_00 bin=5
    .half   0xE000  # [15:13]=111, [1:0]=00 -> cp_00 bin=7

    # auto[1]..auto[2]
    .word 0x00000007   # opcode=1  (major: LOAD-FP)   -> illegal
    .word 0x0000000B   # opcode=2  (CUSTOM-0)         -> illegal/unsupported

    # auto[6]..auto[7]
    .word 0x0000001B   # opcode=6  (OP-IMM-32 RV64)   -> illegal
    .word 0x0000001F   # opcode=7  (reserved)         -> illegal
    .half 0x0001

    # auto[9]..auto[11]
    .word 0x00000027   # opcode=9  (STORE-FP)         -> illegal
    .word 0x0000002B   # opcode=10 (CUSTOM-1)         -> illegal/unsupported
    .word 0x0000002F   # opcode=11 (AMO)              -> illegal

    # auto[14]..auto[23]
    .word 0x0000003B   # opcode=14 (OP-32 RV64)       -> illegal
    .word 0x00000043   # opcode=16 (MADD)             -> illegal
    .word 0x00000047   # opcode=17 (MSUB)             -> illegal
    .word 0x0000004B   # opcode=18 (NMSUB)            -> illegal
    .word 0x0000004F   # opcode=19 (NMADD)            -> illegal
    .word 0x00000053   # opcode=20 (OP-FP)            -> illegal
    .word 0x00000057   # opcode=21 (reserved)         -> illegal
    .word 0x0000005B   # opcode=22 (CUSTOM-2)         -> illegal/unsupported
    .word 0x0000005F   # opcode=23 (reserved)         -> illegal
    .half 0x0001

    # auto[26]
    .word 0x0000006B   # opcode=26 (reserved)         -> illegal

    # auto[29]..auto[31]
    .word 0x00000077   # opcode=29 (reserved)         -> illegal
    .word 0x0000007B   # opcode=30 (CUSTOM-3)         -> illegal/unsupported

    .option pop

    lw      ra, 4(sp)
    addi    sp, sp, 8
    ret

.size illegal_opcodes, .-illegal_opcodes
