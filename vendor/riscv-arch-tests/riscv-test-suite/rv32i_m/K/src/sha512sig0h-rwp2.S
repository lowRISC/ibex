
#include "model_test.h"
#include "arch_test.h"
RVTEST_ISA("RV32IK")

.section .text.init
.org 0x80
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN

#ifdef TEST_CASE_1

RVTEST_CASE(0,"//check ISA:=regex(.*32.*);check ISA:=regex(.*RV32.*I.*K.*);def TEST_CASE_1=True;",sha512sig0h)

RVTEST_CASE(1,"//check ISA:=regex(.*32.*);check ISA:=regex(.*RV32.*I.*ZKn.*);def TEST_CASE_1=True;",sha512sig0h)

RVTEST_SIGBASE( x31,signature_x31_1)

LA(x1,rvtest_data)

inst_0:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x2; op2:x3; dest1:x4;
lw x2, 0(x1);
lw x3, 4(x1);
sha512sig0h x4, x2, x3;
RVTEST_SIGUPD(x31,x2,0);
RVTEST_SIGUPD(x31,x4,4);

inst_1:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x3; op2:x4; dest1:x5;
lw x3, 4(x1);
lw x4, 8(x1);
sha512sig0h x5, x3, x4;
RVTEST_SIGUPD(x31,x3,8);
RVTEST_SIGUPD(x31,x5,12);

inst_2:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x4; op2:x5; dest1:x6;
lw x4, 8(x1);
lw x5, 12(x1);
sha512sig0h x6, x4, x5;
RVTEST_SIGUPD(x31,x4,16);
RVTEST_SIGUPD(x31,x6,20);

inst_3:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x5; op2:x6; dest1:x7;
lw x5, 12(x1);
lw x6, 16(x1);
sha512sig0h x7, x5, x6;
RVTEST_SIGUPD(x31,x5,24);
RVTEST_SIGUPD(x31,x7,28);

inst_4:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x6; op2:x7; dest1:x8;
lw x6, 16(x1);
lw x7, 20(x1);
sha512sig0h x8, x6, x7;
RVTEST_SIGUPD(x31,x6,32);
RVTEST_SIGUPD(x31,x8,36);

inst_5:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x7; op2:x8; dest1:x9;
lw x7, 20(x1);
lw x8, 24(x1);
sha512sig0h x9, x7, x8;
RVTEST_SIGUPD(x31,x7,40);
RVTEST_SIGUPD(x31,x9,44);

inst_6:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x8; op2:x9; dest1:x10;
lw x8, 24(x1);
lw x9, 28(x1);
sha512sig0h x10, x8, x9;
RVTEST_SIGUPD(x31,x8,48);
RVTEST_SIGUPD(x31,x10,52);

inst_7:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x9; op2:x10; dest1:x11;
lw x9, 28(x1);
lw x10, 32(x1);
sha512sig0h x11, x9, x10;
RVTEST_SIGUPD(x31,x9,56);
RVTEST_SIGUPD(x31,x11,60);

inst_8:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x10; op2:x11; dest1:x12;
lw x10, 32(x1);
lw x11, 36(x1);
sha512sig0h x12, x10, x11;
RVTEST_SIGUPD(x31,x10,64);
RVTEST_SIGUPD(x31,x12,68);

inst_9:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x11; op2:x12; dest1:x13;
lw x11, 36(x1);
lw x12, 40(x1);
sha512sig0h x13, x11, x12;
RVTEST_SIGUPD(x31,x11,72);
RVTEST_SIGUPD(x31,x13,76);

inst_10:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x12; op2:x13; dest1:x14;
lw x12, 40(x1);
lw x13, 44(x1);
sha512sig0h x14, x12, x13;
RVTEST_SIGUPD(x31,x12,80);
RVTEST_SIGUPD(x31,x14,84);

inst_11:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x13; op2:x14; dest1:x15;
lw x13, 44(x1);
lw x14, 48(x1);
sha512sig0h x15, x13, x14;
RVTEST_SIGUPD(x31,x13,88);
RVTEST_SIGUPD(x31,x15,92);

inst_12:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x14; op2:x15; dest1:x16;
lw x14, 48(x1);
lw x15, 52(x1);
sha512sig0h x16, x14, x15;
RVTEST_SIGUPD(x31,x14,96);
RVTEST_SIGUPD(x31,x16,100);

inst_13:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x15; op2:x16; dest1:x17;
lw x15, 52(x1);
lw x16, 56(x1);
sha512sig0h x17, x15, x16;
RVTEST_SIGUPD(x31,x15,104);
RVTEST_SIGUPD(x31,x17,108);

inst_14:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x16; op2:x17; dest1:x18;
lw x16, 56(x1);
lw x17, 60(x1);
sha512sig0h x18, x16, x17;
RVTEST_SIGUPD(x31,x16,112);
RVTEST_SIGUPD(x31,x18,116);

inst_15:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x17; op2:x18; dest1:x19;
lw x17, 60(x1);
lw x18, 64(x1);
sha512sig0h x19, x17, x18;
RVTEST_SIGUPD(x31,x17,120);
RVTEST_SIGUPD(x31,x19,124);

inst_16:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x18; op2:x19; dest1:x20;
lw x18, 64(x1);
lw x19, 68(x1);
sha512sig0h x20, x18, x19;
RVTEST_SIGUPD(x31,x18,128);
RVTEST_SIGUPD(x31,x20,132);

inst_17:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x19; op2:x20; dest1:x21;
lw x19, 68(x1);
lw x20, 72(x1);
sha512sig0h x21, x19, x20;
RVTEST_SIGUPD(x31,x19,136);
RVTEST_SIGUPD(x31,x21,140);

inst_18:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x20; op2:x21; dest1:x22;
lw x20, 72(x1);
lw x21, 76(x1);
sha512sig0h x22, x20, x21;
RVTEST_SIGUPD(x31,x20,144);
RVTEST_SIGUPD(x31,x22,148);

inst_19:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x21; op2:x22; dest1:x23;
lw x21, 76(x1);
lw x22, 80(x1);
sha512sig0h x23, x21, x22;
RVTEST_SIGUPD(x31,x21,152);
RVTEST_SIGUPD(x31,x23,156);

inst_20:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x22; op2:x23; dest1:x24;
lw x22, 80(x1);
lw x23, 84(x1);
sha512sig0h x24, x22, x23;
RVTEST_SIGUPD(x31,x22,160);
RVTEST_SIGUPD(x31,x24,164);

inst_21:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x23; op2:x24; dest1:x25;
lw x23, 84(x1);
lw x24, 88(x1);
sha512sig0h x25, x23, x24;
RVTEST_SIGUPD(x31,x23,168);
RVTEST_SIGUPD(x31,x25,172);

inst_22:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x24; op2:x25; dest1:x26;
lw x24, 88(x1);
lw x25, 92(x1);
sha512sig0h x26, x24, x25;
RVTEST_SIGUPD(x31,x24,176);
RVTEST_SIGUPD(x31,x26,180);

inst_23:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x25; op2:x26; dest1:x27;
lw x25, 92(x1);
lw x26, 96(x1);
sha512sig0h x27, x25, x26;
RVTEST_SIGUPD(x31,x25,184);
RVTEST_SIGUPD(x31,x27,188);

inst_24:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x26; op2:x27; dest1:x28;
lw x26, 96(x1);
lw x27, 100(x1);
sha512sig0h x28, x26, x27;
RVTEST_SIGUPD(x31,x26,192);
RVTEST_SIGUPD(x31,x28,196);

inst_25:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x27; op2:x28; dest1:x29;
lw x27, 100(x1);
lw x28, 104(x1);
sha512sig0h x29, x27, x28;
RVTEST_SIGUPD(x31,x27,200);
RVTEST_SIGUPD(x31,x29,204);

inst_26:
// Checking load-to-use hazard!
// opcode: sha512sig0h; op1:x28; op2:x29; dest1:x30;
lw x28, 104(x1);
lw x29, 108(x1);
sha512sig0h x30, x28, x29;
RVTEST_SIGUPD(x31,x28,208);
RVTEST_SIGUPD(x31,x30,212);

#endif

RVTEST_CODE_END
RVMODEL_HALT

RVTEST_DATA_BEGIN
.align 4
rvtest_data:
.word 0x924770d3
.word 0x6dcbac50
.word 0x93fdcab8
.word 0x34c2da80
.word 0xd035d259
.word 0xd2d6b877
.word 0x2904cdef
.word 0x854a9657
.word 0x53e8eb43
.word 0xff1e5bef
.word 0x0b680c1c
.word 0xdc338383
.word 0x9a6ab329
.word 0x61b0ee09
.word 0xacca7f0d
.word 0x74f2e2ed
.word 0xaf949e5e
.word 0xa96ec2b3
.word 0x220adb0a
.word 0xfb7f6f5d
.word 0xf829d29f
.word 0x9d02fc90
.word 0x0109c207
.word 0x224c0601
.word 0xe5f0307e
.word 0x8c8a18b2
.word 0x6f9fb997
.word 0x95a4d257
RVTEST_DATA_END

RVMODEL_DATA_BEGIN
rvtest_sig_begin:
sig_begin_canary:
CANARY;


signature_x31_1:
    .fill 54*(XLEN/32),4,0xdeadbeef
    
#ifdef rvtest_mtrap_routine

tsig_begin_canary:
CANARY;
mtrap_sigptr:
    .fill 64*(XLEN/32),4,0xdeadbeef
tsig_end_canary:
CANARY;

#endif

#ifdef rvtest_gpr_save

gpr_save:
    .fill 32*(XLEN/32),4,0xdeadbeef

#endif

sig_end_canary:
CANARY;
rvtest_sig_end:
RVMODEL_DATA_END
