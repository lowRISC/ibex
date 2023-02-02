
#include "model_test.h"
#include "arch_test.h"
RVTEST_ISA("RV64IK")

.section .text.init
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN

#ifdef TEST_CASE_1

RVTEST_CASE(0,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*K.*);def TEST_CASE_1=True;",sha256sum1)

RVTEST_CASE(1,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*ZKn.*);def TEST_CASE_1=True;",sha256sum1)

RVTEST_SIGBASE( x31,signature_x31_1)

LA(x1,rvtest_data)

inst_0:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x2; dest1:x3;
LREG x2, 0(x1);
sha256sum1 x3, x2;
RVTEST_SIGUPD(x31,x2,0);
RVTEST_SIGUPD(x31,x3,8);

inst_1:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x3; dest1:x4;
LREG x3, 8(x1);
sha256sum1 x4, x3;
RVTEST_SIGUPD(x31,x3,16);
RVTEST_SIGUPD(x31,x4,24);

inst_2:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x4; dest1:x5;
LREG x4, 16(x1);
sha256sum1 x5, x4;
RVTEST_SIGUPD(x31,x4,32);
RVTEST_SIGUPD(x31,x5,40);

inst_3:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x5; dest1:x6;
LREG x5, 24(x1);
sha256sum1 x6, x5;
RVTEST_SIGUPD(x31,x5,48);
RVTEST_SIGUPD(x31,x6,56);

inst_4:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x6; dest1:x7;
LREG x6, 32(x1);
sha256sum1 x7, x6;
RVTEST_SIGUPD(x31,x6,64);
RVTEST_SIGUPD(x31,x7,72);

inst_5:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x7; dest1:x8;
LREG x7, 40(x1);
sha256sum1 x8, x7;
RVTEST_SIGUPD(x31,x7,80);
RVTEST_SIGUPD(x31,x8,88);

inst_6:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x8; dest1:x9;
LREG x8, 48(x1);
sha256sum1 x9, x8;
RVTEST_SIGUPD(x31,x8,96);
RVTEST_SIGUPD(x31,x9,104);

inst_7:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x9; dest1:x10;
LREG x9, 56(x1);
sha256sum1 x10, x9;
RVTEST_SIGUPD(x31,x9,112);
RVTEST_SIGUPD(x31,x10,120);

inst_8:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x10; dest1:x11;
LREG x10, 64(x1);
sha256sum1 x11, x10;
RVTEST_SIGUPD(x31,x10,128);
RVTEST_SIGUPD(x31,x11,136);

inst_9:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x11; dest1:x12;
LREG x11, 72(x1);
sha256sum1 x12, x11;
RVTEST_SIGUPD(x31,x11,144);
RVTEST_SIGUPD(x31,x12,152);

inst_10:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x12; dest1:x13;
LREG x12, 80(x1);
sha256sum1 x13, x12;
RVTEST_SIGUPD(x31,x12,160);
RVTEST_SIGUPD(x31,x13,168);

inst_11:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x13; dest1:x14;
LREG x13, 88(x1);
sha256sum1 x14, x13;
RVTEST_SIGUPD(x31,x13,176);
RVTEST_SIGUPD(x31,x14,184);

inst_12:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x14; dest1:x15;
LREG x14, 96(x1);
sha256sum1 x15, x14;
RVTEST_SIGUPD(x31,x14,192);
RVTEST_SIGUPD(x31,x15,200);

inst_13:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x15; dest1:x16;
LREG x15, 104(x1);
sha256sum1 x16, x15;
RVTEST_SIGUPD(x31,x15,208);
RVTEST_SIGUPD(x31,x16,216);

inst_14:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x16; dest1:x17;
LREG x16, 112(x1);
sha256sum1 x17, x16;
RVTEST_SIGUPD(x31,x16,224);
RVTEST_SIGUPD(x31,x17,232);

inst_15:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x17; dest1:x18;
LREG x17, 120(x1);
sha256sum1 x18, x17;
RVTEST_SIGUPD(x31,x17,240);
RVTEST_SIGUPD(x31,x18,248);

inst_16:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x18; dest1:x19;
LREG x18, 128(x1);
sha256sum1 x19, x18;
RVTEST_SIGUPD(x31,x18,256);
RVTEST_SIGUPD(x31,x19,264);

inst_17:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x19; dest1:x20;
LREG x19, 136(x1);
sha256sum1 x20, x19;
RVTEST_SIGUPD(x31,x19,272);
RVTEST_SIGUPD(x31,x20,280);

inst_18:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x20; dest1:x21;
LREG x20, 144(x1);
sha256sum1 x21, x20;
RVTEST_SIGUPD(x31,x20,288);
RVTEST_SIGUPD(x31,x21,296);

inst_19:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x21; dest1:x22;
LREG x21, 152(x1);
sha256sum1 x22, x21;
RVTEST_SIGUPD(x31,x21,304);
RVTEST_SIGUPD(x31,x22,312);

inst_20:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x22; dest1:x23;
LREG x22, 160(x1);
sha256sum1 x23, x22;
RVTEST_SIGUPD(x31,x22,320);
RVTEST_SIGUPD(x31,x23,328);

inst_21:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x23; dest1:x24;
LREG x23, 168(x1);
sha256sum1 x24, x23;
RVTEST_SIGUPD(x31,x23,336);
RVTEST_SIGUPD(x31,x24,344);

inst_22:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x24; dest1:x25;
LREG x24, 176(x1);
sha256sum1 x25, x24;
RVTEST_SIGUPD(x31,x24,352);
RVTEST_SIGUPD(x31,x25,360);

inst_23:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x25; dest1:x26;
LREG x25, 184(x1);
sha256sum1 x26, x25;
RVTEST_SIGUPD(x31,x25,368);
RVTEST_SIGUPD(x31,x26,376);

inst_24:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x26; dest1:x27;
LREG x26, 192(x1);
sha256sum1 x27, x26;
RVTEST_SIGUPD(x31,x26,384);
RVTEST_SIGUPD(x31,x27,392);

inst_25:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x27; dest1:x28;
LREG x27, 200(x1);
sha256sum1 x28, x27;
RVTEST_SIGUPD(x31,x27,400);
RVTEST_SIGUPD(x31,x28,408);

inst_26:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x28; dest1:x29;
LREG x28, 208(x1);
sha256sum1 x29, x28;
RVTEST_SIGUPD(x31,x28,416);
RVTEST_SIGUPD(x31,x29,424);

inst_27:
// Checking load-to-use hazard!
// opcode: sha256sum1; op1:x29; dest1:x30;
LREG x29, 216(x1);
sha256sum1 x30, x29;
RVTEST_SIGUPD(x31,x29,432);
RVTEST_SIGUPD(x31,x30,440);

#endif

RVTEST_CODE_END
RVMODEL_HALT

RVTEST_DATA_BEGIN
.align 4
rvtest_data:
.dword 0x08577eb1924770d3
.dword 0x93fdcab87b89296c
.dword 0xd2d6b8777dc59a3a
.dword 0xcf84b683a749f9c5
.dword 0x854a965708ceac39
.dword 0x137a977753e8eb43
.dword 0x5c74e45eff1e5bef
.dword 0xdc3383836b9f15c4
.dword 0x5ae6a2289a6ab329
.dword 0x432779eeacca7f0d
.dword 0xaf949e5e2cb7362c
.dword 0x5cd2875ea96ec2b3
.dword 0x9d02fc90708cc1b6
.dword 0x953b00b00b54aa22
.dword 0x224c06013c53d0e3
.dword 0xe8dac663f0e58650
.dword 0x3d7c95f9e5f0307e
.dword 0x8c8a18b2aaac3142
.dword 0x785036de6f9fb997
.dword 0x95a4d257a7298c66
.dword 0x807da245d814d575
.dword 0x3d06143769b1dcbf
.dword 0x7f21682208208d09
.dword 0x14b91c79dae98554
.dword 0xc5ec6148c6880007
.dword 0x7213516d6a013380
.dword 0x4652f62dae4839a1
.dword 0x85986adb9e044706
RVTEST_DATA_END

RVMODEL_DATA_BEGIN
rvtest_sig_begin:
sig_begin_canary:
CANARY;


signature_x31_1:
    .fill 56*(XLEN/32),4,0xdeadbeef
    
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
