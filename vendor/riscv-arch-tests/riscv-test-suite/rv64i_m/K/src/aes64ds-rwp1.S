
#include "model_test.h"
#include "arch_test.h"
RVTEST_ISA("RV64IK")

.section .text.init
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN

#ifdef TEST_CASE_1

RVTEST_CASE(0,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*K.*);def TEST_CASE_1=True;",aes64ds)

RVTEST_CASE(1,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*ZKn.*);def TEST_CASE_1=True;",aes64ds)

RVTEST_SIGBASE( x31,signature_x31_1)

inst_0:
// 1st Instruction => rs1 = x1; rs2 = x2 | 2nd Instruction => rs1 = x2; rs2 = x1 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x1; op2:x2; dest1:x3; dest2:x4; dest3:x5; op1val:0x08577eb1924770d3; op2val:0x93fdcab87b89296c
LI(x1,0x08577eb1924770d3);
LI(x2,0x93fdcab87b89296c);
xor x1, x1, x2;
aes64ds x3, x1, x2;
aes64ds x4, x2, x1;
xor x5, x4, x2;
RVTEST_SIGUPD(x31,x3,0);
RVTEST_SIGUPD(x31,x4,8);
RVTEST_SIGUPD(x31,x5,16);

inst_1:
// 1st Instruction => rs1 = x2; rs2 = x3 | 2nd Instruction => rs1 = x3; rs2 = x2 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x2; op2:x3; dest1:x4; dest2:x5; dest3:x6; op1val:0x137a977753e8eb43; op2val:0x5c74e45eff1e5bef
LI(x2,0x137a977753e8eb43);
LI(x3,0x5c74e45eff1e5bef);
xor x2, x2, x3;
aes64ds x4, x2, x3;
aes64ds x5, x3, x2;
xor x6, x5, x3;
RVTEST_SIGUPD(x31,x4,24);
RVTEST_SIGUPD(x31,x5,32);
RVTEST_SIGUPD(x31,x6,40);

inst_2:
// 1st Instruction => rs1 = x3; rs2 = x4 | 2nd Instruction => rs1 = x4; rs2 = x3 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x3; op2:x4; dest1:x5; dest2:x6; dest3:x7; op1val:0xaf949e5e2cb7362c; op2val:0x5cd2875ea96ec2b3
LI(x3,0xaf949e5e2cb7362c);
LI(x4,0x5cd2875ea96ec2b3);
xor x3, x3, x4;
aes64ds x5, x3, x4;
aes64ds x6, x4, x3;
xor x7, x6, x4;
RVTEST_SIGUPD(x31,x5,48);
RVTEST_SIGUPD(x31,x6,56);
RVTEST_SIGUPD(x31,x7,64);

inst_3:
// 1st Instruction => rs1 = x4; rs2 = x5 | 2nd Instruction => rs1 = x5; rs2 = x4 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x4; op2:x5; dest1:x6; dest2:x7; dest3:x8; op1val:0xe8dac663f0e58650; op2val:0x3d7c95f9e5f0307e
LI(x4,0xe8dac663f0e58650);
LI(x5,0x3d7c95f9e5f0307e);
xor x4, x4, x5;
aes64ds x6, x4, x5;
aes64ds x7, x5, x4;
xor x8, x7, x5;
RVTEST_SIGUPD(x31,x6,72);
RVTEST_SIGUPD(x31,x7,80);
RVTEST_SIGUPD(x31,x8,88);

inst_4:
// 1st Instruction => rs1 = x5; rs2 = x6 | 2nd Instruction => rs1 = x6; rs2 = x5 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x5; op2:x6; dest1:x7; dest2:x8; dest3:x9; op1val:0x807da245d814d575; op2val:0x3d06143769b1dcbf
LI(x5,0x807da245d814d575);
LI(x6,0x3d06143769b1dcbf);
xor x5, x5, x6;
aes64ds x7, x5, x6;
aes64ds x8, x6, x5;
xor x9, x8, x6;
RVTEST_SIGUPD(x31,x7,96);
RVTEST_SIGUPD(x31,x8,104);
RVTEST_SIGUPD(x31,x9,112);

inst_5:
// 1st Instruction => rs1 = x6; rs2 = x7 | 2nd Instruction => rs1 = x7; rs2 = x6 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x6; op2:x7; dest1:x8; dest2:x9; dest3:x10; op1val:0x7213516d6a013380; op2val:0x4652f62dae4839a1
LI(x6,0x7213516d6a013380);
LI(x7,0x4652f62dae4839a1);
xor x6, x6, x7;
aes64ds x8, x6, x7;
aes64ds x9, x7, x6;
xor x10, x9, x7;
RVTEST_SIGUPD(x31,x8,120);
RVTEST_SIGUPD(x31,x9,128);
RVTEST_SIGUPD(x31,x10,136);

inst_6:
// 1st Instruction => rs1 = x7; rs2 = x8 | 2nd Instruction => rs1 = x8; rs2 = x7 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x7; op2:x8; dest1:x9; dest2:x10; dest3:x11; op1val:0x53fbff6c58fa6e1c; op2val:0x0b2e2669b66b3284
LI(x7,0x53fbff6c58fa6e1c);
LI(x8,0x0b2e2669b66b3284);
xor x7, x7, x8;
aes64ds x9, x7, x8;
aes64ds x10, x8, x7;
xor x11, x10, x8;
RVTEST_SIGUPD(x31,x9,144);
RVTEST_SIGUPD(x31,x10,152);
RVTEST_SIGUPD(x31,x11,160);

inst_7:
// 1st Instruction => rs1 = x8; rs2 = x9 | 2nd Instruction => rs1 = x9; rs2 = x8 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x8; op2:x9; dest1:x10; dest2:x11; dest3:x12; op1val:0xe918be9ffe057dc5; op2val:0x1011eeb47ff822ed
LI(x8,0xe918be9ffe057dc5);
LI(x9,0x1011eeb47ff822ed);
xor x8, x8, x9;
aes64ds x10, x8, x9;
aes64ds x11, x9, x8;
xor x12, x11, x9;
RVTEST_SIGUPD(x31,x10,168);
RVTEST_SIGUPD(x31,x11,176);
RVTEST_SIGUPD(x31,x12,184);

inst_8:
// 1st Instruction => rs1 = x9; rs2 = x10 | 2nd Instruction => rs1 = x10; rs2 = x9 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x9; op2:x10; dest1:x11; dest2:x12; dest3:x13; op1val:0xb3a63fa37d69ceef; op2val:0x70fc1afc8f0846a2
LI(x9,0xb3a63fa37d69ceef);
LI(x10,0x70fc1afc8f0846a2);
xor x9, x9, x10;
aes64ds x11, x9, x10;
aes64ds x12, x10, x9;
xor x13, x12, x10;
RVTEST_SIGUPD(x31,x11,192);
RVTEST_SIGUPD(x31,x12,200);
RVTEST_SIGUPD(x31,x13,208);

inst_9:
// 1st Instruction => rs1 = x10; rs2 = x11 | 2nd Instruction => rs1 = x11; rs2 = x10 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x10; op2:x11; dest1:x12; dest2:x13; dest3:x14; op1val:0xccadb61ffe20ce1c; op2val:0x72745307ec325eec
LI(x10,0xccadb61ffe20ce1c);
LI(x11,0x72745307ec325eec);
xor x10, x10, x11;
aes64ds x12, x10, x11;
aes64ds x13, x11, x10;
xor x14, x13, x11;
RVTEST_SIGUPD(x31,x12,216);
RVTEST_SIGUPD(x31,x13,224);
RVTEST_SIGUPD(x31,x14,232);

inst_10:
// 1st Instruction => rs1 = x11; rs2 = x12 | 2nd Instruction => rs1 = x12; rs2 = x11 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x11; op2:x12; dest1:x13; dest2:x14; dest3:x15; op1val:0xa0e0bd86d4551408; op2val:0xcebe24d906600792
LI(x11,0xa0e0bd86d4551408);
LI(x12,0xcebe24d906600792);
xor x11, x11, x12;
aes64ds x13, x11, x12;
aes64ds x14, x12, x11;
xor x15, x14, x12;
RVTEST_SIGUPD(x31,x13,240);
RVTEST_SIGUPD(x31,x14,248);
RVTEST_SIGUPD(x31,x15,256);

inst_11:
// 1st Instruction => rs1 = x12; rs2 = x13 | 2nd Instruction => rs1 = x13; rs2 = x12 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x12; op2:x13; dest1:x14; dest2:x15; dest3:x16; op1val:0xd1142724fb37bec8; op2val:0xab8534c129a2575f
LI(x12,0xd1142724fb37bec8);
LI(x13,0xab8534c129a2575f);
xor x12, x12, x13;
aes64ds x14, x12, x13;
aes64ds x15, x13, x12;
xor x16, x15, x13;
RVTEST_SIGUPD(x31,x14,264);
RVTEST_SIGUPD(x31,x15,272);
RVTEST_SIGUPD(x31,x16,280);

inst_12:
// 1st Instruction => rs1 = x13; rs2 = x14 | 2nd Instruction => rs1 = x14; rs2 = x13 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x13; op2:x14; dest1:x15; dest2:x16; dest3:x17; op1val:0x98f7c41c44115b04; op2val:0x01fbbe93a08b84f3
LI(x13,0x98f7c41c44115b04);
LI(x14,0x01fbbe93a08b84f3);
xor x13, x13, x14;
aes64ds x15, x13, x14;
aes64ds x16, x14, x13;
xor x17, x16, x14;
RVTEST_SIGUPD(x31,x15,288);
RVTEST_SIGUPD(x31,x16,296);
RVTEST_SIGUPD(x31,x17,304);

inst_13:
// 1st Instruction => rs1 = x14; rs2 = x15 | 2nd Instruction => rs1 = x15; rs2 = x14 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x14; op2:x15; dest1:x16; dest2:x17; dest3:x18; op1val:0x5916d2810e24d9cc; op2val:0x74f5add55c37849a
LI(x14,0x5916d2810e24d9cc);
LI(x15,0x74f5add55c37849a);
xor x14, x14, x15;
aes64ds x16, x14, x15;
aes64ds x17, x15, x14;
xor x18, x17, x15;
RVTEST_SIGUPD(x31,x16,312);
RVTEST_SIGUPD(x31,x17,320);
RVTEST_SIGUPD(x31,x18,328);

inst_14:
// 1st Instruction => rs1 = x15; rs2 = x16 | 2nd Instruction => rs1 = x16; rs2 = x15 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x15; op2:x16; dest1:x17; dest2:x18; dest3:x19; op1val:0x46ed745fb9fef1d6; op2val:0x9651ee657a1d33ca
LI(x15,0x46ed745fb9fef1d6);
LI(x16,0x9651ee657a1d33ca);
xor x15, x15, x16;
aes64ds x17, x15, x16;
aes64ds x18, x16, x15;
xor x19, x18, x16;
RVTEST_SIGUPD(x31,x17,336);
RVTEST_SIGUPD(x31,x18,344);
RVTEST_SIGUPD(x31,x19,352);

inst_15:
// 1st Instruction => rs1 = x16; rs2 = x17 | 2nd Instruction => rs1 = x17; rs2 = x16 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x16; op2:x17; dest1:x18; dest2:x19; dest3:x20; op1val:0x9c3d087c65835bdf; op2val:0x9b11d383484641f5
LI(x16,0x9c3d087c65835bdf);
LI(x17,0x9b11d383484641f5);
xor x16, x16, x17;
aes64ds x18, x16, x17;
aes64ds x19, x17, x16;
xor x20, x19, x17;
RVTEST_SIGUPD(x31,x18,360);
RVTEST_SIGUPD(x31,x19,368);
RVTEST_SIGUPD(x31,x20,376);

inst_16:
// 1st Instruction => rs1 = x17; rs2 = x18 | 2nd Instruction => rs1 = x18; rs2 = x17 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x17; op2:x18; dest1:x19; dest2:x20; dest3:x21; op1val:0x041bbaab97eb7c0f; op2val:0x93017690e356529c
LI(x17,0x041bbaab97eb7c0f);
LI(x18,0x93017690e356529c);
xor x17, x17, x18;
aes64ds x19, x17, x18;
aes64ds x20, x18, x17;
xor x21, x20, x18;
RVTEST_SIGUPD(x31,x19,384);
RVTEST_SIGUPD(x31,x20,392);
RVTEST_SIGUPD(x31,x21,400);

inst_17:
// 1st Instruction => rs1 = x18; rs2 = x19 | 2nd Instruction => rs1 = x19; rs2 = x18 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x18; op2:x19; dest1:x20; dest2:x21; dest3:x22; op1val:0xef677106dc17ae6e; op2val:0xc5d09b942be2d8c9
LI(x18,0xef677106dc17ae6e);
LI(x19,0xc5d09b942be2d8c9);
xor x18, x18, x19;
aes64ds x20, x18, x19;
aes64ds x21, x19, x18;
xor x22, x21, x19;
RVTEST_SIGUPD(x31,x20,408);
RVTEST_SIGUPD(x31,x21,416);
RVTEST_SIGUPD(x31,x22,424);

inst_18:
// 1st Instruction => rs1 = x19; rs2 = x20 | 2nd Instruction => rs1 = x20; rs2 = x19 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x19; op2:x20; dest1:x21; dest2:x22; dest3:x23; op1val:0x755961a98347ddf5; op2val:0x18d71be431c00570
LI(x19,0x755961a98347ddf5);
LI(x20,0x18d71be431c00570);
xor x19, x19, x20;
aes64ds x21, x19, x20;
aes64ds x22, x20, x19;
xor x23, x22, x20;
RVTEST_SIGUPD(x31,x21,432);
RVTEST_SIGUPD(x31,x22,440);
RVTEST_SIGUPD(x31,x23,448);

inst_19:
// 1st Instruction => rs1 = x20; rs2 = x21 | 2nd Instruction => rs1 = x21; rs2 = x20 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x20; op2:x21; dest1:x22; dest2:x23; dest3:x24; op1val:0x8f2248c25c3577f5; op2val:0x2a5dc0a00d453cdf
LI(x20,0x8f2248c25c3577f5);
LI(x21,0x2a5dc0a00d453cdf);
xor x20, x20, x21;
aes64ds x22, x20, x21;
aes64ds x23, x21, x20;
xor x24, x23, x21;
RVTEST_SIGUPD(x31,x22,456);
RVTEST_SIGUPD(x31,x23,464);
RVTEST_SIGUPD(x31,x24,472);

inst_20:
// 1st Instruction => rs1 = x21; rs2 = x22 | 2nd Instruction => rs1 = x22; rs2 = x21 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x21; op2:x22; dest1:x23; dest2:x24; dest3:x25; op1val:0x6dc3cceec36ffd4b; op2val:0xc2713ce25868105b
LI(x21,0x6dc3cceec36ffd4b);
LI(x22,0xc2713ce25868105b);
xor x21, x21, x22;
aes64ds x23, x21, x22;
aes64ds x24, x22, x21;
xor x25, x24, x22;
RVTEST_SIGUPD(x31,x23,480);
RVTEST_SIGUPD(x31,x24,488);
RVTEST_SIGUPD(x31,x25,496);

inst_21:
// 1st Instruction => rs1 = x22; rs2 = x23 | 2nd Instruction => rs1 = x23; rs2 = x22 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x22; op2:x23; dest1:x24; dest2:x25; dest3:x26; op1val:0xe4367ccad9716f2c; op2val:0x9ea76f0885958881
LI(x22,0xe4367ccad9716f2c);
LI(x23,0x9ea76f0885958881);
xor x22, x22, x23;
aes64ds x24, x22, x23;
aes64ds x25, x23, x22;
xor x26, x25, x23;
RVTEST_SIGUPD(x31,x24,504);
RVTEST_SIGUPD(x31,x25,512);
RVTEST_SIGUPD(x31,x26,520);

inst_22:
// 1st Instruction => rs1 = x23; rs2 = x24 | 2nd Instruction => rs1 = x24; rs2 = x23 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x23; op2:x24; dest1:x25; dest2:x26; dest3:x27; op1val:0x37c4c6b99530db93; op2val:0x132a717606aec150
LI(x23,0x37c4c6b99530db93);
LI(x24,0x132a717606aec150);
xor x23, x23, x24;
aes64ds x25, x23, x24;
aes64ds x26, x24, x23;
xor x27, x26, x24;
RVTEST_SIGUPD(x31,x25,528);
RVTEST_SIGUPD(x31,x26,536);
RVTEST_SIGUPD(x31,x27,544);

inst_23:
// 1st Instruction => rs1 = x24; rs2 = x25 | 2nd Instruction => rs1 = x25; rs2 = x24 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x24; op2:x25; dest1:x26; dest2:x27; dest3:x28; op1val:0x04d3e5f42bccd6b6; op2val:0x339863c4d216eea8
LI(x24,0x04d3e5f42bccd6b6);
LI(x25,0x339863c4d216eea8);
xor x24, x24, x25;
aes64ds x26, x24, x25;
aes64ds x27, x25, x24;
xor x28, x27, x25;
RVTEST_SIGUPD(x31,x26,552);
RVTEST_SIGUPD(x31,x27,560);
RVTEST_SIGUPD(x31,x28,568);

inst_24:
// 1st Instruction => rs1 = x25; rs2 = x26 | 2nd Instruction => rs1 = x26; rs2 = x25 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x25; op2:x26; dest1:x27; dest2:x28; dest3:x29; op1val:0xd6ac851f07155a89; op2val:0x2d885062faa97965
LI(x25,0xd6ac851f07155a89);
LI(x26,0x2d885062faa97965);
xor x25, x25, x26;
aes64ds x27, x25, x26;
aes64ds x28, x26, x25;
xor x29, x28, x26;
RVTEST_SIGUPD(x31,x27,576);
RVTEST_SIGUPD(x31,x28,584);
RVTEST_SIGUPD(x31,x29,592);

inst_25:
// 1st Instruction => rs1 = x26; rs2 = x27 | 2nd Instruction => rs1 = x27; rs2 = x26 | Result of xor goes into aes64ds & vice versa
// opcode: aes64ds; op1:x26; op2:x27; dest1:x28; dest2:x29; dest3:x30; op1val:0x8d3ba7550c3c31a8; op2val:0xb3e73cbb0d8258c4
LI(x26,0x8d3ba7550c3c31a8);
LI(x27,0xb3e73cbb0d8258c4);
xor x26, x26, x27;
aes64ds x28, x26, x27;
aes64ds x29, x27, x26;
xor x30, x29, x27;
RVTEST_SIGUPD(x31,x28,600);
RVTEST_SIGUPD(x31,x29,608);
RVTEST_SIGUPD(x31,x30,616);

#endif

RVTEST_CODE_END
RVMODEL_HALT

RVTEST_DATA_BEGIN
.align 4

rvtest_data:
.word 0xbabecafe
.word 0xbabecafe
.word 0xbabecafe
.word 0xbabecafe
RVTEST_DATA_END


RVMODEL_DATA_BEGIN
rvtest_sig_begin:
sig_begin_canary:
CANARY;


signature_x31_1:
    .fill 78*(XLEN/32),4,0xdeadbeef
    
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
