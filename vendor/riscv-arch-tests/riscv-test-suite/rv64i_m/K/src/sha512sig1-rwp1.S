
#include "model_test.h"
#include "arch_test.h"
RVTEST_ISA("RV64IK")

.section .text.init
.globl rvtest_entry_point
rvtest_entry_point:
RVMODEL_BOOT
RVTEST_CODE_BEGIN

#ifdef TEST_CASE_1

RVTEST_CASE(0,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*K.*);def TEST_CASE_1=True;",sha512sig1)

RVTEST_CASE(1,"//check ISA:=regex(.*64.*);check ISA:=regex(.*RV64.*I.*ZKn.*);def TEST_CASE_1=True;",sha512sig1)

RVTEST_SIGBASE( x31,signature_x31_1)

inst_0:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x3; dest1:x1; op1val:0x08577eb1924770d3; op2val:0x93fdcab87b89296c
LI(x1,0x08577eb1924770d3);
LI(x2,0x93fdcab87b89296c);
xor x3, x1, x2;
sha512sig1 x1, x3;
xor x4, x1, x2;
RVTEST_SIGUPD(x31,x3,0);
RVTEST_SIGUPD(x31,x1,8);
RVTEST_SIGUPD(x31,x4,16);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x3; dest1:x1; op1val:0x08577eb1924770d3; op2val:0x93fdcab87b89296c
LI(x1,0x08577eb1924770d3);
LI(x2,0x93fdcab87b89296c);
not x3, x2;
sha512sig1 x1, x3;
not x4, x1;
RVTEST_SIGUPD(x31,x3,24);
RVTEST_SIGUPD(x31,x1,32);
RVTEST_SIGUPD(x31,x4,40);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x3; dest1:x1; op1val:0x08577eb1924770d3; op2val:0x93fdcab87b89296c
LI(x1,0x08577eb1924770d3);
LI(x2,0x93fdcab87b89296c);
add x3, x1, x2;
sha512sig1 x1, x3;
add x4, x1, x2;
RVTEST_SIGUPD(x31,x3,48);
RVTEST_SIGUPD(x31,x1,56);
RVTEST_SIGUPD(x31,x4,64);

inst_1:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x4; dest1:x2; op1val:0x137a977753e8eb43; op2val:0x5c74e45eff1e5bef
LI(x2,0x137a977753e8eb43);
LI(x3,0x5c74e45eff1e5bef);
xor x4, x2, x3;
sha512sig1 x2, x4;
xor x5, x2, x3;
RVTEST_SIGUPD(x31,x4,72);
RVTEST_SIGUPD(x31,x2,80);
RVTEST_SIGUPD(x31,x5,88);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x4; dest1:x2; op1val:0x137a977753e8eb43; op2val:0x5c74e45eff1e5bef
LI(x2,0x137a977753e8eb43);
LI(x3,0x5c74e45eff1e5bef);
not x4, x3;
sha512sig1 x2, x4;
not x5, x2;
RVTEST_SIGUPD(x31,x4,96);
RVTEST_SIGUPD(x31,x2,104);
RVTEST_SIGUPD(x31,x5,112);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x4; dest1:x2; op1val:0x137a977753e8eb43; op2val:0x5c74e45eff1e5bef
LI(x2,0x137a977753e8eb43);
LI(x3,0x5c74e45eff1e5bef);
add x4, x2, x3;
sha512sig1 x2, x4;
add x5, x2, x3;
RVTEST_SIGUPD(x31,x4,120);
RVTEST_SIGUPD(x31,x2,128);
RVTEST_SIGUPD(x31,x5,136);

inst_2:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x5; dest1:x3; op1val:0xaf949e5e2cb7362c; op2val:0x5cd2875ea96ec2b3
LI(x3,0xaf949e5e2cb7362c);
LI(x4,0x5cd2875ea96ec2b3);
xor x5, x3, x4;
sha512sig1 x3, x5;
xor x6, x3, x4;
RVTEST_SIGUPD(x31,x5,144);
RVTEST_SIGUPD(x31,x3,152);
RVTEST_SIGUPD(x31,x6,160);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x5; dest1:x3; op1val:0xaf949e5e2cb7362c; op2val:0x5cd2875ea96ec2b3
LI(x3,0xaf949e5e2cb7362c);
LI(x4,0x5cd2875ea96ec2b3);
not x5, x4;
sha512sig1 x3, x5;
not x6, x3;
RVTEST_SIGUPD(x31,x5,168);
RVTEST_SIGUPD(x31,x3,176);
RVTEST_SIGUPD(x31,x6,184);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x5; dest1:x3; op1val:0xaf949e5e2cb7362c; op2val:0x5cd2875ea96ec2b3
LI(x3,0xaf949e5e2cb7362c);
LI(x4,0x5cd2875ea96ec2b3);
add x5, x3, x4;
sha512sig1 x3, x5;
add x6, x3, x4;
RVTEST_SIGUPD(x31,x5,192);
RVTEST_SIGUPD(x31,x3,200);
RVTEST_SIGUPD(x31,x6,208);

inst_3:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x6; dest1:x4; op1val:0xe8dac663f0e58650; op2val:0x3d7c95f9e5f0307e
LI(x4,0xe8dac663f0e58650);
LI(x5,0x3d7c95f9e5f0307e);
xor x6, x4, x5;
sha512sig1 x4, x6;
xor x7, x4, x5;
RVTEST_SIGUPD(x31,x6,216);
RVTEST_SIGUPD(x31,x4,224);
RVTEST_SIGUPD(x31,x7,232);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x6; dest1:x4; op1val:0xe8dac663f0e58650; op2val:0x3d7c95f9e5f0307e
LI(x4,0xe8dac663f0e58650);
LI(x5,0x3d7c95f9e5f0307e);
not x6, x5;
sha512sig1 x4, x6;
not x7, x4;
RVTEST_SIGUPD(x31,x6,240);
RVTEST_SIGUPD(x31,x4,248);
RVTEST_SIGUPD(x31,x7,256);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x6; dest1:x4; op1val:0xe8dac663f0e58650; op2val:0x3d7c95f9e5f0307e
LI(x4,0xe8dac663f0e58650);
LI(x5,0x3d7c95f9e5f0307e);
add x6, x4, x5;
sha512sig1 x4, x6;
add x7, x4, x5;
RVTEST_SIGUPD(x31,x6,264);
RVTEST_SIGUPD(x31,x4,272);
RVTEST_SIGUPD(x31,x7,280);

inst_4:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x7; dest1:x5; op1val:0x807da245d814d575; op2val:0x3d06143769b1dcbf
LI(x5,0x807da245d814d575);
LI(x6,0x3d06143769b1dcbf);
xor x7, x5, x6;
sha512sig1 x5, x7;
xor x8, x5, x6;
RVTEST_SIGUPD(x31,x7,288);
RVTEST_SIGUPD(x31,x5,296);
RVTEST_SIGUPD(x31,x8,304);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x7; dest1:x5; op1val:0x807da245d814d575; op2val:0x3d06143769b1dcbf
LI(x5,0x807da245d814d575);
LI(x6,0x3d06143769b1dcbf);
not x7, x6;
sha512sig1 x5, x7;
not x8, x5;
RVTEST_SIGUPD(x31,x7,312);
RVTEST_SIGUPD(x31,x5,320);
RVTEST_SIGUPD(x31,x8,328);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x7; dest1:x5; op1val:0x807da245d814d575; op2val:0x3d06143769b1dcbf
LI(x5,0x807da245d814d575);
LI(x6,0x3d06143769b1dcbf);
add x7, x5, x6;
sha512sig1 x5, x7;
add x8, x5, x6;
RVTEST_SIGUPD(x31,x7,336);
RVTEST_SIGUPD(x31,x5,344);
RVTEST_SIGUPD(x31,x8,352);

inst_5:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x8; dest1:x6; op1val:0x7213516d6a013380; op2val:0x4652f62dae4839a1
LI(x6,0x7213516d6a013380);
LI(x7,0x4652f62dae4839a1);
xor x8, x6, x7;
sha512sig1 x6, x8;
xor x9, x6, x7;
RVTEST_SIGUPD(x31,x8,360);
RVTEST_SIGUPD(x31,x6,368);
RVTEST_SIGUPD(x31,x9,376);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x8; dest1:x6; op1val:0x7213516d6a013380; op2val:0x4652f62dae4839a1
LI(x6,0x7213516d6a013380);
LI(x7,0x4652f62dae4839a1);
not x8, x7;
sha512sig1 x6, x8;
not x9, x6;
RVTEST_SIGUPD(x31,x8,384);
RVTEST_SIGUPD(x31,x6,392);
RVTEST_SIGUPD(x31,x9,400);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x8; dest1:x6; op1val:0x7213516d6a013380; op2val:0x4652f62dae4839a1
LI(x6,0x7213516d6a013380);
LI(x7,0x4652f62dae4839a1);
add x8, x6, x7;
sha512sig1 x6, x8;
add x9, x6, x7;
RVTEST_SIGUPD(x31,x8,408);
RVTEST_SIGUPD(x31,x6,416);
RVTEST_SIGUPD(x31,x9,424);

inst_6:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x9; dest1:x7; op1val:0x53fbff6c58fa6e1c; op2val:0x0b2e2669b66b3284
LI(x7,0x53fbff6c58fa6e1c);
LI(x8,0x0b2e2669b66b3284);
xor x9, x7, x8;
sha512sig1 x7, x9;
xor x10, x7, x8;
RVTEST_SIGUPD(x31,x9,432);
RVTEST_SIGUPD(x31,x7,440);
RVTEST_SIGUPD(x31,x10,448);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x9; dest1:x7; op1val:0x53fbff6c58fa6e1c; op2val:0x0b2e2669b66b3284
LI(x7,0x53fbff6c58fa6e1c);
LI(x8,0x0b2e2669b66b3284);
not x9, x8;
sha512sig1 x7, x9;
not x10, x7;
RVTEST_SIGUPD(x31,x9,456);
RVTEST_SIGUPD(x31,x7,464);
RVTEST_SIGUPD(x31,x10,472);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x9; dest1:x7; op1val:0x53fbff6c58fa6e1c; op2val:0x0b2e2669b66b3284
LI(x7,0x53fbff6c58fa6e1c);
LI(x8,0x0b2e2669b66b3284);
add x9, x7, x8;
sha512sig1 x7, x9;
add x10, x7, x8;
RVTEST_SIGUPD(x31,x9,480);
RVTEST_SIGUPD(x31,x7,488);
RVTEST_SIGUPD(x31,x10,496);

inst_7:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x10; dest1:x8; op1val:0xe918be9ffe057dc5; op2val:0x1011eeb47ff822ed
LI(x8,0xe918be9ffe057dc5);
LI(x9,0x1011eeb47ff822ed);
xor x10, x8, x9;
sha512sig1 x8, x10;
xor x11, x8, x9;
RVTEST_SIGUPD(x31,x10,504);
RVTEST_SIGUPD(x31,x8,512);
RVTEST_SIGUPD(x31,x11,520);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x10; dest1:x8; op1val:0xe918be9ffe057dc5; op2val:0x1011eeb47ff822ed
LI(x8,0xe918be9ffe057dc5);
LI(x9,0x1011eeb47ff822ed);
not x10, x9;
sha512sig1 x8, x10;
not x11, x8;
RVTEST_SIGUPD(x31,x10,528);
RVTEST_SIGUPD(x31,x8,536);
RVTEST_SIGUPD(x31,x11,544);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x10; dest1:x8; op1val:0xe918be9ffe057dc5; op2val:0x1011eeb47ff822ed
LI(x8,0xe918be9ffe057dc5);
LI(x9,0x1011eeb47ff822ed);
add x10, x8, x9;
sha512sig1 x8, x10;
add x11, x8, x9;
RVTEST_SIGUPD(x31,x10,552);
RVTEST_SIGUPD(x31,x8,560);
RVTEST_SIGUPD(x31,x11,568);

inst_8:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x11; dest1:x9; op1val:0xb3a63fa37d69ceef; op2val:0x70fc1afc8f0846a2
LI(x9,0xb3a63fa37d69ceef);
LI(x10,0x70fc1afc8f0846a2);
xor x11, x9, x10;
sha512sig1 x9, x11;
xor x12, x9, x10;
RVTEST_SIGUPD(x31,x11,576);
RVTEST_SIGUPD(x31,x9,584);
RVTEST_SIGUPD(x31,x12,592);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x11; dest1:x9; op1val:0xb3a63fa37d69ceef; op2val:0x70fc1afc8f0846a2
LI(x9,0xb3a63fa37d69ceef);
LI(x10,0x70fc1afc8f0846a2);
not x11, x10;
sha512sig1 x9, x11;
not x12, x9;
RVTEST_SIGUPD(x31,x11,600);
RVTEST_SIGUPD(x31,x9,608);
RVTEST_SIGUPD(x31,x12,616);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x11; dest1:x9; op1val:0xb3a63fa37d69ceef; op2val:0x70fc1afc8f0846a2
LI(x9,0xb3a63fa37d69ceef);
LI(x10,0x70fc1afc8f0846a2);
add x11, x9, x10;
sha512sig1 x9, x11;
add x12, x9, x10;
RVTEST_SIGUPD(x31,x11,624);
RVTEST_SIGUPD(x31,x9,632);
RVTEST_SIGUPD(x31,x12,640);

inst_9:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x12; dest1:x10; op1val:0xccadb61ffe20ce1c; op2val:0x72745307ec325eec
LI(x10,0xccadb61ffe20ce1c);
LI(x11,0x72745307ec325eec);
xor x12, x10, x11;
sha512sig1 x10, x12;
xor x13, x10, x11;
RVTEST_SIGUPD(x31,x12,648);
RVTEST_SIGUPD(x31,x10,656);
RVTEST_SIGUPD(x31,x13,664);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x12; dest1:x10; op1val:0xccadb61ffe20ce1c; op2val:0x72745307ec325eec
LI(x10,0xccadb61ffe20ce1c);
LI(x11,0x72745307ec325eec);
not x12, x11;
sha512sig1 x10, x12;
not x13, x10;
RVTEST_SIGUPD(x31,x12,672);
RVTEST_SIGUPD(x31,x10,680);
RVTEST_SIGUPD(x31,x13,688);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x12; dest1:x10; op1val:0xccadb61ffe20ce1c; op2val:0x72745307ec325eec
LI(x10,0xccadb61ffe20ce1c);
LI(x11,0x72745307ec325eec);
add x12, x10, x11;
sha512sig1 x10, x12;
add x13, x10, x11;
RVTEST_SIGUPD(x31,x12,696);
RVTEST_SIGUPD(x31,x10,704);
RVTEST_SIGUPD(x31,x13,712);

inst_10:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x13; dest1:x11; op1val:0xa0e0bd86d4551408; op2val:0xcebe24d906600792
LI(x11,0xa0e0bd86d4551408);
LI(x12,0xcebe24d906600792);
xor x13, x11, x12;
sha512sig1 x11, x13;
xor x14, x11, x12;
RVTEST_SIGUPD(x31,x13,720);
RVTEST_SIGUPD(x31,x11,728);
RVTEST_SIGUPD(x31,x14,736);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x13; dest1:x11; op1val:0xa0e0bd86d4551408; op2val:0xcebe24d906600792
LI(x11,0xa0e0bd86d4551408);
LI(x12,0xcebe24d906600792);
not x13, x12;
sha512sig1 x11, x13;
not x14, x11;
RVTEST_SIGUPD(x31,x13,744);
RVTEST_SIGUPD(x31,x11,752);
RVTEST_SIGUPD(x31,x14,760);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x13; dest1:x11; op1val:0xa0e0bd86d4551408; op2val:0xcebe24d906600792
LI(x11,0xa0e0bd86d4551408);
LI(x12,0xcebe24d906600792);
add x13, x11, x12;
sha512sig1 x11, x13;
add x14, x11, x12;
RVTEST_SIGUPD(x31,x13,768);
RVTEST_SIGUPD(x31,x11,776);
RVTEST_SIGUPD(x31,x14,784);

inst_11:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x14; dest1:x12; op1val:0xd1142724fb37bec8; op2val:0xab8534c129a2575f
LI(x12,0xd1142724fb37bec8);
LI(x13,0xab8534c129a2575f);
xor x14, x12, x13;
sha512sig1 x12, x14;
xor x15, x12, x13;
RVTEST_SIGUPD(x31,x14,792);
RVTEST_SIGUPD(x31,x12,800);
RVTEST_SIGUPD(x31,x15,808);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x14; dest1:x12; op1val:0xd1142724fb37bec8; op2val:0xab8534c129a2575f
LI(x12,0xd1142724fb37bec8);
LI(x13,0xab8534c129a2575f);
not x14, x13;
sha512sig1 x12, x14;
not x15, x12;
RVTEST_SIGUPD(x31,x14,816);
RVTEST_SIGUPD(x31,x12,824);
RVTEST_SIGUPD(x31,x15,832);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x14; dest1:x12; op1val:0xd1142724fb37bec8; op2val:0xab8534c129a2575f
LI(x12,0xd1142724fb37bec8);
LI(x13,0xab8534c129a2575f);
add x14, x12, x13;
sha512sig1 x12, x14;
add x15, x12, x13;
RVTEST_SIGUPD(x31,x14,840);
RVTEST_SIGUPD(x31,x12,848);
RVTEST_SIGUPD(x31,x15,856);

inst_12:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x15; dest1:x13; op1val:0x98f7c41c44115b04; op2val:0x01fbbe93a08b84f3
LI(x13,0x98f7c41c44115b04);
LI(x14,0x01fbbe93a08b84f3);
xor x15, x13, x14;
sha512sig1 x13, x15;
xor x16, x13, x14;
RVTEST_SIGUPD(x31,x15,864);
RVTEST_SIGUPD(x31,x13,872);
RVTEST_SIGUPD(x31,x16,880);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x15; dest1:x13; op1val:0x98f7c41c44115b04; op2val:0x01fbbe93a08b84f3
LI(x13,0x98f7c41c44115b04);
LI(x14,0x01fbbe93a08b84f3);
not x15, x14;
sha512sig1 x13, x15;
not x16, x13;
RVTEST_SIGUPD(x31,x15,888);
RVTEST_SIGUPD(x31,x13,896);
RVTEST_SIGUPD(x31,x16,904);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x15; dest1:x13; op1val:0x98f7c41c44115b04; op2val:0x01fbbe93a08b84f3
LI(x13,0x98f7c41c44115b04);
LI(x14,0x01fbbe93a08b84f3);
add x15, x13, x14;
sha512sig1 x13, x15;
add x16, x13, x14;
RVTEST_SIGUPD(x31,x15,912);
RVTEST_SIGUPD(x31,x13,920);
RVTEST_SIGUPD(x31,x16,928);

inst_13:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x16; dest1:x14; op1val:0x5916d2810e24d9cc; op2val:0x74f5add55c37849a
LI(x14,0x5916d2810e24d9cc);
LI(x15,0x74f5add55c37849a);
xor x16, x14, x15;
sha512sig1 x14, x16;
xor x17, x14, x15;
RVTEST_SIGUPD(x31,x16,936);
RVTEST_SIGUPD(x31,x14,944);
RVTEST_SIGUPD(x31,x17,952);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x16; dest1:x14; op1val:0x5916d2810e24d9cc; op2val:0x74f5add55c37849a
LI(x14,0x5916d2810e24d9cc);
LI(x15,0x74f5add55c37849a);
not x16, x15;
sha512sig1 x14, x16;
not x17, x14;
RVTEST_SIGUPD(x31,x16,960);
RVTEST_SIGUPD(x31,x14,968);
RVTEST_SIGUPD(x31,x17,976);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x16; dest1:x14; op1val:0x5916d2810e24d9cc; op2val:0x74f5add55c37849a
LI(x14,0x5916d2810e24d9cc);
LI(x15,0x74f5add55c37849a);
add x16, x14, x15;
sha512sig1 x14, x16;
add x17, x14, x15;
RVTEST_SIGUPD(x31,x16,984);
RVTEST_SIGUPD(x31,x14,992);
RVTEST_SIGUPD(x31,x17,1000);

inst_14:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x17; dest1:x15; op1val:0x46ed745fb9fef1d6; op2val:0x9651ee657a1d33ca
LI(x15,0x46ed745fb9fef1d6);
LI(x16,0x9651ee657a1d33ca);
xor x17, x15, x16;
sha512sig1 x15, x17;
xor x18, x15, x16;
RVTEST_SIGUPD(x31,x17,1008);
RVTEST_SIGUPD(x31,x15,1016);
RVTEST_SIGUPD(x31,x18,1024);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x17; dest1:x15; op1val:0x46ed745fb9fef1d6; op2val:0x9651ee657a1d33ca
LI(x15,0x46ed745fb9fef1d6);
LI(x16,0x9651ee657a1d33ca);
not x17, x16;
sha512sig1 x15, x17;
not x18, x15;
RVTEST_SIGUPD(x31,x17,1032);
RVTEST_SIGUPD(x31,x15,1040);
RVTEST_SIGUPD(x31,x18,1048);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x17; dest1:x15; op1val:0x46ed745fb9fef1d6; op2val:0x9651ee657a1d33ca
LI(x15,0x46ed745fb9fef1d6);
LI(x16,0x9651ee657a1d33ca);
add x17, x15, x16;
sha512sig1 x15, x17;
add x18, x15, x16;
RVTEST_SIGUPD(x31,x17,1056);
RVTEST_SIGUPD(x31,x15,1064);
RVTEST_SIGUPD(x31,x18,1072);

inst_15:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x18; dest1:x16; op1val:0x9c3d087c65835bdf; op2val:0x9b11d383484641f5
LI(x16,0x9c3d087c65835bdf);
LI(x17,0x9b11d383484641f5);
xor x18, x16, x17;
sha512sig1 x16, x18;
xor x19, x16, x17;
RVTEST_SIGUPD(x31,x18,1080);
RVTEST_SIGUPD(x31,x16,1088);
RVTEST_SIGUPD(x31,x19,1096);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x18; dest1:x16; op1val:0x9c3d087c65835bdf; op2val:0x9b11d383484641f5
LI(x16,0x9c3d087c65835bdf);
LI(x17,0x9b11d383484641f5);
not x18, x17;
sha512sig1 x16, x18;
not x19, x16;
RVTEST_SIGUPD(x31,x18,1104);
RVTEST_SIGUPD(x31,x16,1112);
RVTEST_SIGUPD(x31,x19,1120);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x18; dest1:x16; op1val:0x9c3d087c65835bdf; op2val:0x9b11d383484641f5
LI(x16,0x9c3d087c65835bdf);
LI(x17,0x9b11d383484641f5);
add x18, x16, x17;
sha512sig1 x16, x18;
add x19, x16, x17;
RVTEST_SIGUPD(x31,x18,1128);
RVTEST_SIGUPD(x31,x16,1136);
RVTEST_SIGUPD(x31,x19,1144);

inst_16:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x19; dest1:x17; op1val:0x041bbaab97eb7c0f; op2val:0x93017690e356529c
LI(x17,0x041bbaab97eb7c0f);
LI(x18,0x93017690e356529c);
xor x19, x17, x18;
sha512sig1 x17, x19;
xor x20, x17, x18;
RVTEST_SIGUPD(x31,x19,1152);
RVTEST_SIGUPD(x31,x17,1160);
RVTEST_SIGUPD(x31,x20,1168);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x19; dest1:x17; op1val:0x041bbaab97eb7c0f; op2val:0x93017690e356529c
LI(x17,0x041bbaab97eb7c0f);
LI(x18,0x93017690e356529c);
not x19, x18;
sha512sig1 x17, x19;
not x20, x17;
RVTEST_SIGUPD(x31,x19,1176);
RVTEST_SIGUPD(x31,x17,1184);
RVTEST_SIGUPD(x31,x20,1192);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x19; dest1:x17; op1val:0x041bbaab97eb7c0f; op2val:0x93017690e356529c
LI(x17,0x041bbaab97eb7c0f);
LI(x18,0x93017690e356529c);
add x19, x17, x18;
sha512sig1 x17, x19;
add x20, x17, x18;
RVTEST_SIGUPD(x31,x19,1200);
RVTEST_SIGUPD(x31,x17,1208);
RVTEST_SIGUPD(x31,x20,1216);

inst_17:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x20; dest1:x18; op1val:0xef677106dc17ae6e; op2val:0xc5d09b942be2d8c9
LI(x18,0xef677106dc17ae6e);
LI(x19,0xc5d09b942be2d8c9);
xor x20, x18, x19;
sha512sig1 x18, x20;
xor x21, x18, x19;
RVTEST_SIGUPD(x31,x20,1224);
RVTEST_SIGUPD(x31,x18,1232);
RVTEST_SIGUPD(x31,x21,1240);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x20; dest1:x18; op1val:0xef677106dc17ae6e; op2val:0xc5d09b942be2d8c9
LI(x18,0xef677106dc17ae6e);
LI(x19,0xc5d09b942be2d8c9);
not x20, x19;
sha512sig1 x18, x20;
not x21, x18;
RVTEST_SIGUPD(x31,x20,1248);
RVTEST_SIGUPD(x31,x18,1256);
RVTEST_SIGUPD(x31,x21,1264);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x20; dest1:x18; op1val:0xef677106dc17ae6e; op2val:0xc5d09b942be2d8c9
LI(x18,0xef677106dc17ae6e);
LI(x19,0xc5d09b942be2d8c9);
add x20, x18, x19;
sha512sig1 x18, x20;
add x21, x18, x19;
RVTEST_SIGUPD(x31,x20,1272);
RVTEST_SIGUPD(x31,x18,1280);
RVTEST_SIGUPD(x31,x21,1288);

inst_18:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x21; dest1:x19; op1val:0x755961a98347ddf5; op2val:0x18d71be431c00570
LI(x19,0x755961a98347ddf5);
LI(x20,0x18d71be431c00570);
xor x21, x19, x20;
sha512sig1 x19, x21;
xor x22, x19, x20;
RVTEST_SIGUPD(x31,x21,1296);
RVTEST_SIGUPD(x31,x19,1304);
RVTEST_SIGUPD(x31,x22,1312);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x21; dest1:x19; op1val:0x755961a98347ddf5; op2val:0x18d71be431c00570
LI(x19,0x755961a98347ddf5);
LI(x20,0x18d71be431c00570);
not x21, x20;
sha512sig1 x19, x21;
not x22, x19;
RVTEST_SIGUPD(x31,x21,1320);
RVTEST_SIGUPD(x31,x19,1328);
RVTEST_SIGUPD(x31,x22,1336);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x21; dest1:x19; op1val:0x755961a98347ddf5; op2val:0x18d71be431c00570
LI(x19,0x755961a98347ddf5);
LI(x20,0x18d71be431c00570);
add x21, x19, x20;
sha512sig1 x19, x21;
add x22, x19, x20;
RVTEST_SIGUPD(x31,x21,1344);
RVTEST_SIGUPD(x31,x19,1352);
RVTEST_SIGUPD(x31,x22,1360);

inst_19:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x22; dest1:x20; op1val:0x8f2248c25c3577f5; op2val:0x2a5dc0a00d453cdf
LI(x20,0x8f2248c25c3577f5);
LI(x21,0x2a5dc0a00d453cdf);
xor x22, x20, x21;
sha512sig1 x20, x22;
xor x23, x20, x21;
RVTEST_SIGUPD(x31,x22,1368);
RVTEST_SIGUPD(x31,x20,1376);
RVTEST_SIGUPD(x31,x23,1384);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x22; dest1:x20; op1val:0x8f2248c25c3577f5; op2val:0x2a5dc0a00d453cdf
LI(x20,0x8f2248c25c3577f5);
LI(x21,0x2a5dc0a00d453cdf);
not x22, x21;
sha512sig1 x20, x22;
not x23, x20;
RVTEST_SIGUPD(x31,x22,1392);
RVTEST_SIGUPD(x31,x20,1400);
RVTEST_SIGUPD(x31,x23,1408);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x22; dest1:x20; op1val:0x8f2248c25c3577f5; op2val:0x2a5dc0a00d453cdf
LI(x20,0x8f2248c25c3577f5);
LI(x21,0x2a5dc0a00d453cdf);
add x22, x20, x21;
sha512sig1 x20, x22;
add x23, x20, x21;
RVTEST_SIGUPD(x31,x22,1416);
RVTEST_SIGUPD(x31,x20,1424);
RVTEST_SIGUPD(x31,x23,1432);

inst_20:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x23; dest1:x21; op1val:0x6dc3cceec36ffd4b; op2val:0xc2713ce25868105b
LI(x21,0x6dc3cceec36ffd4b);
LI(x22,0xc2713ce25868105b);
xor x23, x21, x22;
sha512sig1 x21, x23;
xor x24, x21, x22;
RVTEST_SIGUPD(x31,x23,1440);
RVTEST_SIGUPD(x31,x21,1448);
RVTEST_SIGUPD(x31,x24,1456);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x23; dest1:x21; op1val:0x6dc3cceec36ffd4b; op2val:0xc2713ce25868105b
LI(x21,0x6dc3cceec36ffd4b);
LI(x22,0xc2713ce25868105b);
not x23, x22;
sha512sig1 x21, x23;
not x24, x21;
RVTEST_SIGUPD(x31,x23,1464);
RVTEST_SIGUPD(x31,x21,1472);
RVTEST_SIGUPD(x31,x24,1480);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x23; dest1:x21; op1val:0x6dc3cceec36ffd4b; op2val:0xc2713ce25868105b
LI(x21,0x6dc3cceec36ffd4b);
LI(x22,0xc2713ce25868105b);
add x23, x21, x22;
sha512sig1 x21, x23;
add x24, x21, x22;
RVTEST_SIGUPD(x31,x23,1488);
RVTEST_SIGUPD(x31,x21,1496);
RVTEST_SIGUPD(x31,x24,1504);

inst_21:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x24; dest1:x22; op1val:0xe4367ccad9716f2c; op2val:0x9ea76f0885958881
LI(x22,0xe4367ccad9716f2c);
LI(x23,0x9ea76f0885958881);
xor x24, x22, x23;
sha512sig1 x22, x24;
xor x25, x22, x23;
RVTEST_SIGUPD(x31,x24,1512);
RVTEST_SIGUPD(x31,x22,1520);
RVTEST_SIGUPD(x31,x25,1528);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x24; dest1:x22; op1val:0xe4367ccad9716f2c; op2val:0x9ea76f0885958881
LI(x22,0xe4367ccad9716f2c);
LI(x23,0x9ea76f0885958881);
not x24, x23;
sha512sig1 x22, x24;
not x25, x22;
RVTEST_SIGUPD(x31,x24,1536);
RVTEST_SIGUPD(x31,x22,1544);
RVTEST_SIGUPD(x31,x25,1552);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x24; dest1:x22; op1val:0xe4367ccad9716f2c; op2val:0x9ea76f0885958881
LI(x22,0xe4367ccad9716f2c);
LI(x23,0x9ea76f0885958881);
add x24, x22, x23;
sha512sig1 x22, x24;
add x25, x22, x23;
RVTEST_SIGUPD(x31,x24,1560);
RVTEST_SIGUPD(x31,x22,1568);
RVTEST_SIGUPD(x31,x25,1576);

inst_22:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x25; dest1:x23; op1val:0x37c4c6b99530db93; op2val:0x132a717606aec150
LI(x23,0x37c4c6b99530db93);
LI(x24,0x132a717606aec150);
xor x25, x23, x24;
sha512sig1 x23, x25;
xor x26, x23, x24;
RVTEST_SIGUPD(x31,x25,1584);
RVTEST_SIGUPD(x31,x23,1592);
RVTEST_SIGUPD(x31,x26,1600);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x25; dest1:x23; op1val:0x37c4c6b99530db93; op2val:0x132a717606aec150
LI(x23,0x37c4c6b99530db93);
LI(x24,0x132a717606aec150);
not x25, x24;
sha512sig1 x23, x25;
not x26, x23;
RVTEST_SIGUPD(x31,x25,1608);
RVTEST_SIGUPD(x31,x23,1616);
RVTEST_SIGUPD(x31,x26,1624);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x25; dest1:x23; op1val:0x37c4c6b99530db93; op2val:0x132a717606aec150
LI(x23,0x37c4c6b99530db93);
LI(x24,0x132a717606aec150);
add x25, x23, x24;
sha512sig1 x23, x25;
add x26, x23, x24;
RVTEST_SIGUPD(x31,x25,1632);
RVTEST_SIGUPD(x31,x23,1640);
RVTEST_SIGUPD(x31,x26,1648);

inst_23:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x26; dest1:x24; op1val:0x04d3e5f42bccd6b6; op2val:0x339863c4d216eea8
LI(x24,0x04d3e5f42bccd6b6);
LI(x25,0x339863c4d216eea8);
xor x26, x24, x25;
sha512sig1 x24, x26;
xor x27, x24, x25;
RVTEST_SIGUPD(x31,x26,1656);
RVTEST_SIGUPD(x31,x24,1664);
RVTEST_SIGUPD(x31,x27,1672);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x26; dest1:x24; op1val:0x04d3e5f42bccd6b6; op2val:0x339863c4d216eea8
LI(x24,0x04d3e5f42bccd6b6);
LI(x25,0x339863c4d216eea8);
not x26, x25;
sha512sig1 x24, x26;
not x27, x24;
RVTEST_SIGUPD(x31,x26,1680);
RVTEST_SIGUPD(x31,x24,1688);
RVTEST_SIGUPD(x31,x27,1696);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x26; dest1:x24; op1val:0x04d3e5f42bccd6b6; op2val:0x339863c4d216eea8
LI(x24,0x04d3e5f42bccd6b6);
LI(x25,0x339863c4d216eea8);
add x26, x24, x25;
sha512sig1 x24, x26;
add x27, x24, x25;
RVTEST_SIGUPD(x31,x26,1704);
RVTEST_SIGUPD(x31,x24,1712);
RVTEST_SIGUPD(x31,x27,1720);

inst_24:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x27; dest1:x25; op1val:0xd6ac851f07155a89; op2val:0x2d885062faa97965
LI(x25,0xd6ac851f07155a89);
LI(x26,0x2d885062faa97965);
xor x27, x25, x26;
sha512sig1 x25, x27;
xor x28, x25, x26;
RVTEST_SIGUPD(x31,x27,1728);
RVTEST_SIGUPD(x31,x25,1736);
RVTEST_SIGUPD(x31,x28,1744);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x27; dest1:x25; op1val:0xd6ac851f07155a89; op2val:0x2d885062faa97965
LI(x25,0xd6ac851f07155a89);
LI(x26,0x2d885062faa97965);
not x27, x26;
sha512sig1 x25, x27;
not x28, x25;
RVTEST_SIGUPD(x31,x27,1752);
RVTEST_SIGUPD(x31,x25,1760);
RVTEST_SIGUPD(x31,x28,1768);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x27; dest1:x25; op1val:0xd6ac851f07155a89; op2val:0x2d885062faa97965
LI(x25,0xd6ac851f07155a89);
LI(x26,0x2d885062faa97965);
add x27, x25, x26;
sha512sig1 x25, x27;
add x28, x25, x26;
RVTEST_SIGUPD(x31,x27,1776);
RVTEST_SIGUPD(x31,x25,1784);
RVTEST_SIGUPD(x31,x28,1792);

inst_25:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x28; dest1:x26; op1val:0x8d3ba7550c3c31a8; op2val:0xb3e73cbb0d8258c4
LI(x26,0x8d3ba7550c3c31a8);
LI(x27,0xb3e73cbb0d8258c4);
xor x28, x26, x27;
sha512sig1 x26, x28;
xor x29, x26, x27;
RVTEST_SIGUPD(x31,x28,1800);
RVTEST_SIGUPD(x31,x26,1808);
RVTEST_SIGUPD(x31,x29,1816);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x28; dest1:x26; op1val:0x8d3ba7550c3c31a8; op2val:0xb3e73cbb0d8258c4
LI(x26,0x8d3ba7550c3c31a8);
LI(x27,0xb3e73cbb0d8258c4);
not x28, x27;
sha512sig1 x26, x28;
not x29, x26;
RVTEST_SIGUPD(x31,x28,1824);
RVTEST_SIGUPD(x31,x26,1832);
RVTEST_SIGUPD(x31,x29,1840);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x28; dest1:x26; op1val:0x8d3ba7550c3c31a8; op2val:0xb3e73cbb0d8258c4
LI(x26,0x8d3ba7550c3c31a8);
LI(x27,0xb3e73cbb0d8258c4);
add x28, x26, x27;
sha512sig1 x26, x28;
add x29, x26, x27;
RVTEST_SIGUPD(x31,x28,1848);
RVTEST_SIGUPD(x31,x26,1856);
RVTEST_SIGUPD(x31,x29,1864);

inst_26:
// Forwarded xor into sha512sig1 & the result back into xor
// opcode: sha512sig1; op1:x29; dest1:x27; op1val:0x239853f9120ff957; op2val:0x2d13320e40d0e5e7
LI(x27,0x239853f9120ff957);
LI(x28,0x2d13320e40d0e5e7);
xor x29, x27, x28;
sha512sig1 x27, x29;
xor x30, x27, x28;
RVTEST_SIGUPD(x31,x29,1872);
RVTEST_SIGUPD(x31,x27,1880);
RVTEST_SIGUPD(x31,x30,1888);

// Forwarded not into sha512sig1 & the result back into not
// opcode: sha512sig1; op1:x29; dest1:x27; op1val:0x239853f9120ff957; op2val:0x2d13320e40d0e5e7
LI(x27,0x239853f9120ff957);
LI(x28,0x2d13320e40d0e5e7);
not x29, x28;
sha512sig1 x27, x29;
not x30, x27;
RVTEST_SIGUPD(x31,x29,1896);
RVTEST_SIGUPD(x31,x27,1904);
RVTEST_SIGUPD(x31,x30,1912);

// Forwarded add into sha512sig1 & the result back into add
// opcode: sha512sig1; op1:x29; dest1:x27; op1val:0x239853f9120ff957; op2val:0x2d13320e40d0e5e7
LI(x27,0x239853f9120ff957);
LI(x28,0x2d13320e40d0e5e7);
add x29, x27, x28;
sha512sig1 x27, x29;
add x30, x27, x28;
RVTEST_SIGUPD(x31,x29,1920);
RVTEST_SIGUPD(x31,x27,1928);
RVTEST_SIGUPD(x31,x30,1936);

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
    .fill 243*(XLEN/32),4,0xdeadbeef
    
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
