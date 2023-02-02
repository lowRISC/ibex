
#include "model_test.h"
#include "arch_test.h"
RVTEST_ISA("RV64IK")

.section .text.init
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN

#ifdef TEST_CASE_1

RVTEST_CASE(0,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*K.*);def TEST_CASE_1=True;",sm4ks)

RVTEST_CASE(1,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*ZKs.*);def TEST_CASE_1=True;",sm4ks)

RVTEST_SIGBASE( x31,signature_x31_1)

inst_0:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x1; op1:x2; op1:x3; op1:x4; dest:x5;
LI( x1,0x08577eb1924770d3);
LI( x2,0x93fdcab87b89296c);
LI( x3,0xd2d6b8777dc59a3a);
LI( x4,0xcf84b683a749f9c5);
LI( x5,0x854a965708ceac39);
sm4ks x5, x5, x1, 0;
sm4ks x5, x5, x2, 1;
sm4ks x5, x5, x3, 2;
sm4ks x5, x5, x4, 3;
RVTEST_SIGUPD(x31,x5,0);

inst_1:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x2; op1:x3; op1:x4; op1:x5; dest:x6;
LI( x2,0x137a977753e8eb43);
LI( x3,0x5c74e45eff1e5bef);
LI( x4,0xdc3383836b9f15c4);
LI( x5,0x5ae6a2289a6ab329);
LI( x6,0x432779eeacca7f0d);
sm4ks x6, x6, x2, 0;
sm4ks x6, x6, x3, 1;
sm4ks x6, x6, x4, 2;
sm4ks x6, x6, x5, 3;
RVTEST_SIGUPD(x31,x6,8);

inst_2:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x3; op1:x4; op1:x5; op1:x6; dest:x7;
LI( x3,0xaf949e5e2cb7362c);
LI( x4,0x5cd2875ea96ec2b3);
LI( x5,0x9d02fc90708cc1b6);
LI( x6,0x953b00b00b54aa22);
LI( x7,0x224c06013c53d0e3);
sm4ks x7, x7, x3, 0;
sm4ks x7, x7, x4, 1;
sm4ks x7, x7, x5, 2;
sm4ks x7, x7, x6, 3;
RVTEST_SIGUPD(x31,x7,16);

inst_3:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x4; op1:x5; op1:x6; op1:x7; dest:x8;
LI( x4,0xe8dac663f0e58650);
LI( x5,0x3d7c95f9e5f0307e);
LI( x6,0x8c8a18b2aaac3142);
LI( x7,0x785036de6f9fb997);
LI( x8,0x95a4d257a7298c66);
sm4ks x8, x8, x4, 0;
sm4ks x8, x8, x5, 1;
sm4ks x8, x8, x6, 2;
sm4ks x8, x8, x7, 3;
RVTEST_SIGUPD(x31,x8,24);

inst_4:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x5; op1:x6; op1:x7; op1:x8; dest:x9;
LI( x5,0x807da245d814d575);
LI( x6,0x3d06143769b1dcbf);
LI( x7,0x7f21682208208d09);
LI( x8,0x14b91c79dae98554);
LI( x9,0xc5ec6148c6880007);
sm4ks x9, x9, x5, 0;
sm4ks x9, x9, x6, 1;
sm4ks x9, x9, x7, 2;
sm4ks x9, x9, x8, 3;
RVTEST_SIGUPD(x31,x9,32);

inst_5:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x6; op1:x7; op1:x8; op1:x9; dest:x10;
LI( x6,0x7213516d6a013380);
LI( x7,0x4652f62dae4839a1);
LI( x8,0x85986adb9e044706);
LI( x9,0x1e9667c2dd68f201);
LI( x10,0x4d753ac174ab0a38);
sm4ks x10, x10, x6, 0;
sm4ks x10, x10, x7, 1;
sm4ks x10, x10, x8, 2;
sm4ks x10, x10, x9, 3;
RVTEST_SIGUPD(x31,x10,40);

inst_6:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x7; op1:x8; op1:x9; op1:x10; dest:x11;
LI( x7,0x53fbff6c58fa6e1c);
LI( x8,0x0b2e2669b66b3284);
LI( x9,0x51c5b8b2e59cf78f);
LI( x10,0x43032e3e1475f78d);
LI( x11,0x9535971c67a07b54);
sm4ks x11, x11, x7, 0;
sm4ks x11, x11, x8, 1;
sm4ks x11, x11, x9, 2;
sm4ks x11, x11, x10, 3;
RVTEST_SIGUPD(x31,x11,48);

inst_7:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x8; op1:x9; op1:x10; op1:x11; dest:x12;
LI( x8,0xe918be9ffe057dc5);
LI( x9,0x1011eeb47ff822ed);
LI( x10,0xac9e90327d486895);
LI( x11,0x66b072b9e5e290be);
LI( x12,0x89e6156b59672bd6);
sm4ks x12, x12, x8, 0;
sm4ks x12, x12, x9, 1;
sm4ks x12, x12, x10, 2;
sm4ks x12, x12, x11, 3;
RVTEST_SIGUPD(x31,x12,56);

inst_8:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x9; op1:x10; op1:x11; op1:x12; dest:x13;
LI( x9,0xb3a63fa37d69ceef);
LI( x10,0x70fc1afc8f0846a2);
LI( x11,0xf956ec0bf7fb4b49);
LI( x12,0x0cf25923109ff475);
LI( x13,0x26ea42ec17be082f);
sm4ks x13, x13, x9, 0;
sm4ks x13, x13, x10, 1;
sm4ks x13, x13, x11, 2;
sm4ks x13, x13, x12, 3;
RVTEST_SIGUPD(x31,x13,64);

inst_9:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x10; op1:x11; op1:x12; op1:x13; dest:x14;
LI( x10,0xccadb61ffe20ce1c);
LI( x11,0x72745307ec325eec);
LI( x12,0xb2a7a18ac9ea3210);
LI( x13,0xbd59213e27541f0b);
LI( x14,0x9e7e1fc352b42eff);
sm4ks x14, x14, x10, 0;
sm4ks x14, x14, x11, 1;
sm4ks x14, x14, x12, 2;
sm4ks x14, x14, x13, 3;
RVTEST_SIGUPD(x31,x14,72);

inst_10:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x11; op1:x12; op1:x13; op1:x14; dest:x15;
LI( x11,0xa0e0bd86d4551408);
LI( x12,0xcebe24d906600792);
LI( x13,0x4bd90a77f65cf3f3);
LI( x14,0xdbdd4dd9d9e93409);
LI( x15,0xf65e7737fbd2570d);
sm4ks x15, x15, x11, 0;
sm4ks x15, x15, x12, 1;
sm4ks x15, x15, x13, 2;
sm4ks x15, x15, x14, 3;
RVTEST_SIGUPD(x31,x15,80);

inst_11:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x12; op1:x13; op1:x14; op1:x15; dest:x16;
LI( x12,0xd1142724fb37bec8);
LI( x13,0xab8534c129a2575f);
LI( x14,0xfc6113a3312529dc);
LI( x15,0x6d3f408b31d4ff08);
LI( x16,0x8e368ce0be5265f3);
sm4ks x16, x16, x12, 0;
sm4ks x16, x16, x13, 1;
sm4ks x16, x16, x14, 2;
sm4ks x16, x16, x15, 3;
RVTEST_SIGUPD(x31,x16,88);

inst_12:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x13; op1:x14; op1:x15; op1:x16; dest:x17;
LI( x13,0x98f7c41c44115b04);
LI( x14,0x01fbbe93a08b84f3);
LI( x15,0x9c1a15286c834752);
LI( x16,0xa6faba7bcfe6bc54);
LI( x17,0xc5b3e01b11f6d600);
sm4ks x17, x17, x13, 0;
sm4ks x17, x17, x14, 1;
sm4ks x17, x17, x15, 2;
sm4ks x17, x17, x16, 3;
RVTEST_SIGUPD(x31,x17,96);

inst_13:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x14; op1:x15; op1:x16; op1:x17; dest:x18;
LI( x14,0x5916d2810e24d9cc);
LI( x15,0x74f5add55c37849a);
LI( x16,0x4850e927bfdbb3be);
LI( x17,0x67913217437cbc41);
LI( x18,0x576e3d4fa3b633ab);
sm4ks x18, x18, x14, 0;
sm4ks x18, x18, x15, 1;
sm4ks x18, x18, x16, 2;
sm4ks x18, x18, x17, 3;
RVTEST_SIGUPD(x31,x18,104);

inst_14:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x15; op1:x16; op1:x17; op1:x18; dest:x19;
LI( x15,0x46ed745fb9fef1d6);
LI( x16,0x9651ee657a1d33ca);
LI( x17,0xfe0a9c6c9a592829);
LI( x18,0x9071f3aab87ce2a5);
LI( x19,0x4e6168c8d6220b4f);
sm4ks x19, x19, x15, 0;
sm4ks x19, x19, x16, 1;
sm4ks x19, x19, x17, 2;
sm4ks x19, x19, x18, 3;
RVTEST_SIGUPD(x31,x19,112);

inst_15:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x16; op1:x17; op1:x18; op1:x19; dest:x20;
LI( x16,0x9c3d087c65835bdf);
LI( x17,0x9b11d383484641f5);
LI( x18,0x2b24ced43da82c98);
LI( x19,0xef8c60c0d12f8d4e);
LI( x20,0xf37e27a312ea67e4);
sm4ks x20, x20, x16, 0;
sm4ks x20, x20, x17, 1;
sm4ks x20, x20, x18, 2;
sm4ks x20, x20, x19, 3;
RVTEST_SIGUPD(x31,x20,120);

inst_16:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x17; op1:x18; op1:x19; op1:x20; dest:x21;
LI( x17,0x041bbaab97eb7c0f);
LI( x18,0x93017690e356529c);
LI( x19,0xd5e9d561f46a41bd);
LI( x20,0x9408ad7db13971c0);
LI( x21,0x90af95fe095b6425);
sm4ks x21, x21, x17, 0;
sm4ks x21, x21, x18, 1;
sm4ks x21, x21, x19, 2;
sm4ks x21, x21, x20, 3;
RVTEST_SIGUPD(x31,x21,128);

inst_17:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x18; op1:x19; op1:x20; op1:x21; dest:x22;
LI( x18,0xef677106dc17ae6e);
LI( x19,0xc5d09b942be2d8c9);
LI( x20,0x596f5f89ce334459);
LI( x21,0x5902a9dbe1832ab6);
LI( x22,0xb4dc7dee71dabeac);
sm4ks x22, x22, x18, 0;
sm4ks x22, x22, x19, 1;
sm4ks x22, x22, x20, 2;
sm4ks x22, x22, x21, 3;
RVTEST_SIGUPD(x31,x22,136);

inst_18:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x19; op1:x20; op1:x21; op1:x22; dest:x23;
LI( x19,0x755961a98347ddf5);
LI( x20,0x18d71be431c00570);
LI( x21,0x270e1922a422af66);
LI( x22,0xdc336338eea4dd03);
LI( x23,0xa2460e15a3da90b2);
sm4ks x23, x23, x19, 0;
sm4ks x23, x23, x20, 1;
sm4ks x23, x23, x21, 2;
sm4ks x23, x23, x22, 3;
RVTEST_SIGUPD(x31,x23,144);

inst_19:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x20; op1:x21; op1:x22; op1:x23; dest:x24;
LI( x20,0x8f2248c25c3577f5);
LI( x21,0x2a5dc0a00d453cdf);
LI( x22,0xf3281b8ef4d325c3);
LI( x23,0x947ac00e0caec993);
LI( x24,0xd60235f35c4739b7);
sm4ks x24, x24, x20, 0;
sm4ks x24, x24, x21, 1;
sm4ks x24, x24, x22, 2;
sm4ks x24, x24, x23, 3;
RVTEST_SIGUPD(x31,x24,152);

inst_20:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x21; op1:x22; op1:x23; op1:x24; dest:x25;
LI( x21,0x6dc3cceec36ffd4b);
LI( x22,0xc2713ce25868105b);
LI( x23,0x29ade05f7dddcc72);
LI( x24,0x6baeea37b4c8839b);
LI( x25,0x1e4e0fadd02bad0f);
sm4ks x25, x25, x21, 0;
sm4ks x25, x25, x22, 1;
sm4ks x25, x25, x23, 2;
sm4ks x25, x25, x24, 3;
RVTEST_SIGUPD(x31,x25,160);

inst_21:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x22; op1:x23; op1:x24; op1:x25; dest:x26;
LI( x22,0xe4367ccad9716f2c);
LI( x23,0x9ea76f0885958881);
LI( x24,0xb183406662ebf954);
LI( x25,0x796c1d88c313bc1f);
LI( x26,0xe7e94a5193b3cb9a);
sm4ks x26, x26, x22, 0;
sm4ks x26, x26, x23, 1;
sm4ks x26, x26, x24, 2;
sm4ks x26, x26, x25, 3;
RVTEST_SIGUPD(x31,x26,168);

inst_22:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x23; op1:x24; op1:x25; op1:x26; dest:x27;
LI( x23,0x37c4c6b99530db93);
LI( x24,0x132a717606aec150);
LI( x25,0x08011d17cfac3216);
LI( x26,0xd65358aaa734906b);
LI( x27,0xba1c4b6b2d9da6d7);
sm4ks x27, x27, x23, 0;
sm4ks x27, x27, x24, 1;
sm4ks x27, x27, x25, 2;
sm4ks x27, x27, x26, 3;
RVTEST_SIGUPD(x31,x27,176);

inst_23:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x24; op1:x25; op1:x26; op1:x27; dest:x28;
LI( x24,0x04d3e5f42bccd6b6);
LI( x25,0x339863c4d216eea8);
LI( x26,0x3f13091de7fcc18b);
LI( x27,0xc2cc1d388d15d800);
LI( x28,0x0165f0f02016dc16);
sm4ks x28, x28, x24, 0;
sm4ks x28, x28, x25, 1;
sm4ks x28, x28, x26, 2;
sm4ks x28, x28, x27, 3;
RVTEST_SIGUPD(x31,x28,184);

inst_24:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x25; op1:x26; op1:x27; op1:x28; dest:x29;
LI( x25,0xd6ac851f07155a89);
LI( x26,0x2d885062faa97965);
LI( x27,0x62a12347b17286fd);
LI( x28,0xa97cbf8403beaecd);
LI( x29,0xa9632e3dbd0070ae);
sm4ks x29, x29, x25, 0;
sm4ks x29, x29, x26, 1;
sm4ks x29, x29, x27, 2;
sm4ks x29, x29, x28, 3;
RVTEST_SIGUPD(x31,x29,192);

inst_25:
// Expected use-case sequence -> Aims to test things like pipeline forwarding
// opcode: sm4ks; op1:x26; op1:x27; op1:x28; op1:x29; dest:x30;
LI( x26,0x8d3ba7550c3c31a8);
LI( x27,0xb3e73cbb0d8258c4);
LI( x28,0x7587e11994038f33);
LI( x29,0x2f8d133555f7f60a);
LI( x30,0xa0a1c6ef661a191b);
sm4ks x30, x30, x26, 0;
sm4ks x30, x30, x27, 1;
sm4ks x30, x30, x28, 2;
sm4ks x30, x30, x29, 3;
RVTEST_SIGUPD(x31,x30,200);

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
    .fill 26*(XLEN/32),4,0xdeadbeef
    
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
