
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

inst_0:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x3; op2:x2; dest1:x1; op1val:0x924770d3; op2val:0x6dcbac50
LI(x1,0x924770d3);
LI(x2,0x6dcbac50);
xor x3, x1, x2;
sha512sig0h x1, x3, x2;
xor x4, x1, x2;
RVTEST_SIGUPD(x31,x3,0);
RVTEST_SIGUPD(x31,x1,4);
RVTEST_SIGUPD(x31,x4,8);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x3; op2:x2; dest1:x1; op1val:0x924770d3; op2val:0x6dcbac50
LI(x1,0x924770d3);
LI(x2,0x6dcbac50);
not x3, x2;
sha512sig0h x1, x3, x2;
not x4, x1;
RVTEST_SIGUPD(x31,x3,12);
RVTEST_SIGUPD(x31,x1,16);
RVTEST_SIGUPD(x31,x4,20);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x3; op2:x2; dest1:x1; op1val:0x924770d3; op2val:0x6dcbac50
LI(x1,0x924770d3);
LI(x2,0x6dcbac50);
add x3, x1, x2;
sha512sig0h x1, x3, x2;
add x4, x1, x2;
RVTEST_SIGUPD(x31,x3,24);
RVTEST_SIGUPD(x31,x1,28);
RVTEST_SIGUPD(x31,x4,32);

inst_1:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x4; op2:x3; dest1:x2; op1val:0xd2d6b877; op2val:0x2904cdef
LI(x2,0xd2d6b877);
LI(x3,0x2904cdef);
xor x4, x2, x3;
sha512sig0h x2, x4, x3;
xor x5, x2, x3;
RVTEST_SIGUPD(x31,x4,36);
RVTEST_SIGUPD(x31,x2,40);
RVTEST_SIGUPD(x31,x5,44);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x4; op2:x3; dest1:x2; op1val:0xd2d6b877; op2val:0x2904cdef
LI(x2,0xd2d6b877);
LI(x3,0x2904cdef);
not x4, x3;
sha512sig0h x2, x4, x3;
not x5, x2;
RVTEST_SIGUPD(x31,x4,48);
RVTEST_SIGUPD(x31,x2,52);
RVTEST_SIGUPD(x31,x5,56);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x4; op2:x3; dest1:x2; op1val:0xd2d6b877; op2val:0x2904cdef
LI(x2,0xd2d6b877);
LI(x3,0x2904cdef);
add x4, x2, x3;
sha512sig0h x2, x4, x3;
add x5, x2, x3;
RVTEST_SIGUPD(x31,x4,60);
RVTEST_SIGUPD(x31,x2,64);
RVTEST_SIGUPD(x31,x5,68);

inst_2:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x5; op2:x4; dest1:x3; op1val:0x0b680c1c; op2val:0xdc338383
LI(x3,0x0b680c1c);
LI(x4,0xdc338383);
xor x5, x3, x4;
sha512sig0h x3, x5, x4;
xor x6, x3, x4;
RVTEST_SIGUPD(x31,x5,72);
RVTEST_SIGUPD(x31,x3,76);
RVTEST_SIGUPD(x31,x6,80);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x5; op2:x4; dest1:x3; op1val:0x0b680c1c; op2val:0xdc338383
LI(x3,0x0b680c1c);
LI(x4,0xdc338383);
not x5, x4;
sha512sig0h x3, x5, x4;
not x6, x3;
RVTEST_SIGUPD(x31,x5,84);
RVTEST_SIGUPD(x31,x3,88);
RVTEST_SIGUPD(x31,x6,92);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x5; op2:x4; dest1:x3; op1val:0x0b680c1c; op2val:0xdc338383
LI(x3,0x0b680c1c);
LI(x4,0xdc338383);
add x5, x3, x4;
sha512sig0h x3, x5, x4;
add x6, x3, x4;
RVTEST_SIGUPD(x31,x5,96);
RVTEST_SIGUPD(x31,x3,100);
RVTEST_SIGUPD(x31,x6,104);

inst_3:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x6; op2:x5; dest1:x4; op1val:0x74f2e2ed; op2val:0xaf949e5e
LI(x4,0x74f2e2ed);
LI(x5,0xaf949e5e);
xor x6, x4, x5;
sha512sig0h x4, x6, x5;
xor x7, x4, x5;
RVTEST_SIGUPD(x31,x6,108);
RVTEST_SIGUPD(x31,x4,112);
RVTEST_SIGUPD(x31,x7,116);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x6; op2:x5; dest1:x4; op1val:0x74f2e2ed; op2val:0xaf949e5e
LI(x4,0x74f2e2ed);
LI(x5,0xaf949e5e);
not x6, x5;
sha512sig0h x4, x6, x5;
not x7, x4;
RVTEST_SIGUPD(x31,x6,120);
RVTEST_SIGUPD(x31,x4,124);
RVTEST_SIGUPD(x31,x7,128);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x6; op2:x5; dest1:x4; op1val:0x74f2e2ed; op2val:0xaf949e5e
LI(x4,0x74f2e2ed);
LI(x5,0xaf949e5e);
add x6, x4, x5;
sha512sig0h x4, x6, x5;
add x7, x4, x5;
RVTEST_SIGUPD(x31,x6,132);
RVTEST_SIGUPD(x31,x4,136);
RVTEST_SIGUPD(x31,x7,140);

inst_4:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x7; op2:x6; dest1:x5; op1val:0xf829d29f; op2val:0x9d02fc90
LI(x5,0xf829d29f);
LI(x6,0x9d02fc90);
xor x7, x5, x6;
sha512sig0h x5, x7, x6;
xor x8, x5, x6;
RVTEST_SIGUPD(x31,x7,144);
RVTEST_SIGUPD(x31,x5,148);
RVTEST_SIGUPD(x31,x8,152);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x7; op2:x6; dest1:x5; op1val:0xf829d29f; op2val:0x9d02fc90
LI(x5,0xf829d29f);
LI(x6,0x9d02fc90);
not x7, x6;
sha512sig0h x5, x7, x6;
not x8, x5;
RVTEST_SIGUPD(x31,x7,156);
RVTEST_SIGUPD(x31,x5,160);
RVTEST_SIGUPD(x31,x8,164);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x7; op2:x6; dest1:x5; op1val:0xf829d29f; op2val:0x9d02fc90
LI(x5,0xf829d29f);
LI(x6,0x9d02fc90);
add x7, x5, x6;
sha512sig0h x5, x7, x6;
add x8, x5, x6;
RVTEST_SIGUPD(x31,x7,168);
RVTEST_SIGUPD(x31,x5,172);
RVTEST_SIGUPD(x31,x8,176);

inst_5:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x8; op2:x7; dest1:x6; op1val:0x8c8a18b2; op2val:0x6f9fb997
LI(x6,0x8c8a18b2);
LI(x7,0x6f9fb997);
xor x8, x6, x7;
sha512sig0h x6, x8, x7;
xor x9, x6, x7;
RVTEST_SIGUPD(x31,x8,180);
RVTEST_SIGUPD(x31,x6,184);
RVTEST_SIGUPD(x31,x9,188);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x8; op2:x7; dest1:x6; op1val:0x8c8a18b2; op2val:0x6f9fb997
LI(x6,0x8c8a18b2);
LI(x7,0x6f9fb997);
not x8, x7;
sha512sig0h x6, x8, x7;
not x9, x6;
RVTEST_SIGUPD(x31,x8,192);
RVTEST_SIGUPD(x31,x6,196);
RVTEST_SIGUPD(x31,x9,200);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x8; op2:x7; dest1:x6; op1val:0x8c8a18b2; op2val:0x6f9fb997
LI(x6,0x8c8a18b2);
LI(x7,0x6f9fb997);
add x8, x6, x7;
sha512sig0h x6, x8, x7;
add x9, x6, x7;
RVTEST_SIGUPD(x31,x8,204);
RVTEST_SIGUPD(x31,x6,208);
RVTEST_SIGUPD(x31,x9,212);

inst_6:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x9; op2:x8; dest1:x7; op1val:0x7f216822; op2val:0xa86b8a6e
LI(x7,0x7f216822);
LI(x8,0xa86b8a6e);
xor x9, x7, x8;
sha512sig0h x7, x9, x8;
xor x10, x7, x8;
RVTEST_SIGUPD(x31,x9,216);
RVTEST_SIGUPD(x31,x7,220);
RVTEST_SIGUPD(x31,x10,224);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x9; op2:x8; dest1:x7; op1val:0x7f216822; op2val:0xa86b8a6e
LI(x7,0x7f216822);
LI(x8,0xa86b8a6e);
not x9, x8;
sha512sig0h x7, x9, x8;
not x10, x7;
RVTEST_SIGUPD(x31,x9,228);
RVTEST_SIGUPD(x31,x7,232);
RVTEST_SIGUPD(x31,x10,236);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x9; op2:x8; dest1:x7; op1val:0x7f216822; op2val:0xa86b8a6e
LI(x7,0x7f216822);
LI(x8,0xa86b8a6e);
add x9, x7, x8;
sha512sig0h x7, x9, x8;
add x10, x7, x8;
RVTEST_SIGUPD(x31,x9,240);
RVTEST_SIGUPD(x31,x7,244);
RVTEST_SIGUPD(x31,x10,248);

inst_7:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x10; op2:x9; dest1:x8; op1val:0x18bb28e9; op2val:0xceb506f6
LI(x8,0x18bb28e9);
LI(x9,0xceb506f6);
xor x10, x8, x9;
sha512sig0h x8, x10, x9;
xor x11, x8, x9;
RVTEST_SIGUPD(x31,x10,252);
RVTEST_SIGUPD(x31,x8,256);
RVTEST_SIGUPD(x31,x11,260);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x10; op2:x9; dest1:x8; op1val:0x18bb28e9; op2val:0xceb506f6
LI(x8,0x18bb28e9);
LI(x9,0xceb506f6);
not x10, x9;
sha512sig0h x8, x10, x9;
not x11, x8;
RVTEST_SIGUPD(x31,x10,264);
RVTEST_SIGUPD(x31,x8,268);
RVTEST_SIGUPD(x31,x11,272);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x10; op2:x9; dest1:x8; op1val:0x18bb28e9; op2val:0xceb506f6
LI(x8,0x18bb28e9);
LI(x9,0xceb506f6);
add x10, x8, x9;
sha512sig0h x8, x10, x9;
add x11, x8, x9;
RVTEST_SIGUPD(x31,x10,276);
RVTEST_SIGUPD(x31,x8,280);
RVTEST_SIGUPD(x31,x11,284);

inst_8:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x11; op2:x10; dest1:x9; op1val:0x1e9667c2; op2val:0x74ab0a38
LI(x9,0x1e9667c2);
LI(x10,0x74ab0a38);
xor x11, x9, x10;
sha512sig0h x9, x11, x10;
xor x12, x9, x10;
RVTEST_SIGUPD(x31,x11,288);
RVTEST_SIGUPD(x31,x9,292);
RVTEST_SIGUPD(x31,x12,296);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x11; op2:x10; dest1:x9; op1val:0x1e9667c2; op2val:0x74ab0a38
LI(x9,0x1e9667c2);
LI(x10,0x74ab0a38);
not x11, x10;
sha512sig0h x9, x11, x10;
not x12, x9;
RVTEST_SIGUPD(x31,x11,300);
RVTEST_SIGUPD(x31,x9,304);
RVTEST_SIGUPD(x31,x12,308);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x11; op2:x10; dest1:x9; op1val:0x1e9667c2; op2val:0x74ab0a38
LI(x9,0x1e9667c2);
LI(x10,0x74ab0a38);
add x11, x9, x10;
sha512sig0h x9, x11, x10;
add x12, x9, x10;
RVTEST_SIGUPD(x31,x11,312);
RVTEST_SIGUPD(x31,x9,316);
RVTEST_SIGUPD(x31,x12,320);

inst_9:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x12; op2:x11; dest1:x10; op1val:0x6f4930c8; op2val:0xb66b3284
LI(x10,0x6f4930c8);
LI(x11,0xb66b3284);
xor x12, x10, x11;
sha512sig0h x10, x12, x11;
xor x13, x10, x11;
RVTEST_SIGUPD(x31,x12,324);
RVTEST_SIGUPD(x31,x10,328);
RVTEST_SIGUPD(x31,x13,332);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x12; op2:x11; dest1:x10; op1val:0x6f4930c8; op2val:0xb66b3284
LI(x10,0x6f4930c8);
LI(x11,0xb66b3284);
not x12, x11;
sha512sig0h x10, x12, x11;
not x13, x10;
RVTEST_SIGUPD(x31,x12,336);
RVTEST_SIGUPD(x31,x10,340);
RVTEST_SIGUPD(x31,x13,344);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x12; op2:x11; dest1:x10; op1val:0x6f4930c8; op2val:0xb66b3284
LI(x10,0x6f4930c8);
LI(x11,0xb66b3284);
add x12, x10, x11;
sha512sig0h x10, x12, x11;
add x13, x10, x11;
RVTEST_SIGUPD(x31,x12,348);
RVTEST_SIGUPD(x31,x10,352);
RVTEST_SIGUPD(x31,x13,356);

inst_10:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x13; op2:x12; dest1:x11; op1val:0x9535971c; op2val:0xde9a896f
LI(x11,0x9535971c);
LI(x12,0xde9a896f);
xor x13, x11, x12;
sha512sig0h x11, x13, x12;
xor x14, x11, x12;
RVTEST_SIGUPD(x31,x13,360);
RVTEST_SIGUPD(x31,x11,364);
RVTEST_SIGUPD(x31,x14,368);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x13; op2:x12; dest1:x11; op1val:0x9535971c; op2val:0xde9a896f
LI(x11,0x9535971c);
LI(x12,0xde9a896f);
not x13, x12;
sha512sig0h x11, x13, x12;
not x14, x11;
RVTEST_SIGUPD(x31,x13,372);
RVTEST_SIGUPD(x31,x11,376);
RVTEST_SIGUPD(x31,x14,380);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x13; op2:x12; dest1:x11; op1val:0x9535971c; op2val:0xde9a896f
LI(x11,0x9535971c);
LI(x12,0xde9a896f);
add x13, x11, x12;
sha512sig0h x11, x13, x12;
add x14, x11, x12;
RVTEST_SIGUPD(x31,x13,384);
RVTEST_SIGUPD(x31,x11,388);
RVTEST_SIGUPD(x31,x14,392);

inst_11:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x14; op2:x13; dest1:x12; op1val:0x1011eeb4; op2val:0x66b072b9
LI(x12,0x1011eeb4);
LI(x13,0x66b072b9);
xor x14, x12, x13;
sha512sig0h x12, x14, x13;
xor x15, x12, x13;
RVTEST_SIGUPD(x31,x14,396);
RVTEST_SIGUPD(x31,x12,400);
RVTEST_SIGUPD(x31,x15,404);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x14; op2:x13; dest1:x12; op1val:0x1011eeb4; op2val:0x66b072b9
LI(x12,0x1011eeb4);
LI(x13,0x66b072b9);
not x14, x13;
sha512sig0h x12, x14, x13;
not x15, x12;
RVTEST_SIGUPD(x31,x14,408);
RVTEST_SIGUPD(x31,x12,412);
RVTEST_SIGUPD(x31,x15,416);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x14; op2:x13; dest1:x12; op1val:0x1011eeb4; op2val:0x66b072b9
LI(x12,0x1011eeb4);
LI(x13,0x66b072b9);
add x14, x12, x13;
sha512sig0h x12, x14, x13;
add x15, x12, x13;
RVTEST_SIGUPD(x31,x14,420);
RVTEST_SIGUPD(x31,x12,424);
RVTEST_SIGUPD(x31,x15,428);

inst_12:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x15; op2:x14; dest1:x13; op1val:0x00b97ea6; op2val:0x89112f0a
LI(x13,0x00b97ea6);
LI(x14,0x89112f0a);
xor x15, x13, x14;
sha512sig0h x13, x15, x14;
xor x16, x13, x14;
RVTEST_SIGUPD(x31,x15,432);
RVTEST_SIGUPD(x31,x13,436);
RVTEST_SIGUPD(x31,x16,440);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x15; op2:x14; dest1:x13; op1val:0x00b97ea6; op2val:0x89112f0a
LI(x13,0x00b97ea6);
LI(x14,0x89112f0a);
not x15, x14;
sha512sig0h x13, x15, x14;
not x16, x13;
RVTEST_SIGUPD(x31,x15,444);
RVTEST_SIGUPD(x31,x13,448);
RVTEST_SIGUPD(x31,x16,452);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x15; op2:x14; dest1:x13; op1val:0x00b97ea6; op2val:0x89112f0a
LI(x13,0x00b97ea6);
LI(x14,0x89112f0a);
add x15, x13, x14;
sha512sig0h x13, x15, x14;
add x16, x13, x14;
RVTEST_SIGUPD(x31,x15,456);
RVTEST_SIGUPD(x31,x13,460);
RVTEST_SIGUPD(x31,x16,464);

inst_13:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x16; op2:x15; dest1:x14; op1val:0x72745307; op2val:0xb9e93d52
LI(x14,0x72745307);
LI(x15,0xb9e93d52);
xor x16, x14, x15;
sha512sig0h x14, x16, x15;
xor x17, x14, x15;
RVTEST_SIGUPD(x31,x16,468);
RVTEST_SIGUPD(x31,x14,472);
RVTEST_SIGUPD(x31,x17,476);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x16; op2:x15; dest1:x14; op1val:0x72745307; op2val:0xb9e93d52
LI(x14,0x72745307);
LI(x15,0xb9e93d52);
not x16, x15;
sha512sig0h x14, x16, x15;
not x17, x14;
RVTEST_SIGUPD(x31,x16,480);
RVTEST_SIGUPD(x31,x14,484);
RVTEST_SIGUPD(x31,x17,488);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x16; op2:x15; dest1:x14; op1val:0x72745307; op2val:0xb9e93d52
LI(x14,0x72745307);
LI(x15,0xb9e93d52);
add x16, x14, x15;
sha512sig0h x14, x16, x15;
add x17, x14, x15;
RVTEST_SIGUPD(x31,x16,492);
RVTEST_SIGUPD(x31,x14,496);
RVTEST_SIGUPD(x31,x17,500);

inst_14:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x17; op2:x16; dest1:x15; op1val:0x9e7e1fc3; op2val:0xafe08a13
LI(x15,0x9e7e1fc3);
LI(x16,0xafe08a13);
xor x17, x15, x16;
sha512sig0h x15, x17, x16;
xor x18, x15, x16;
RVTEST_SIGUPD(x31,x17,504);
RVTEST_SIGUPD(x31,x15,508);
RVTEST_SIGUPD(x31,x18,512);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x17; op2:x16; dest1:x15; op1val:0x9e7e1fc3; op2val:0xafe08a13
LI(x15,0x9e7e1fc3);
LI(x16,0xafe08a13);
not x17, x16;
sha512sig0h x15, x17, x16;
not x18, x15;
RVTEST_SIGUPD(x31,x17,516);
RVTEST_SIGUPD(x31,x15,520);
RVTEST_SIGUPD(x31,x18,524);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x17; op2:x16; dest1:x15; op1val:0x9e7e1fc3; op2val:0xafe08a13
LI(x15,0x9e7e1fc3);
LI(x16,0xafe08a13);
add x17, x15, x16;
sha512sig0h x15, x17, x16;
add x18, x15, x16;
RVTEST_SIGUPD(x31,x17,528);
RVTEST_SIGUPD(x31,x15,532);
RVTEST_SIGUPD(x31,x18,536);

inst_15:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x18; op2:x17; dest1:x16; op1val:0xdbdd4dd9; op2val:0xb7debb9b
LI(x16,0xdbdd4dd9);
LI(x17,0xb7debb9b);
xor x18, x16, x17;
sha512sig0h x16, x18, x17;
xor x19, x16, x17;
RVTEST_SIGUPD(x31,x18,540);
RVTEST_SIGUPD(x31,x16,544);
RVTEST_SIGUPD(x31,x19,548);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x18; op2:x17; dest1:x16; op1val:0xdbdd4dd9; op2val:0xb7debb9b
LI(x16,0xdbdd4dd9);
LI(x17,0xb7debb9b);
not x18, x17;
sha512sig0h x16, x18, x17;
not x19, x16;
RVTEST_SIGUPD(x31,x18,552);
RVTEST_SIGUPD(x31,x16,556);
RVTEST_SIGUPD(x31,x19,560);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x18; op2:x17; dest1:x16; op1val:0xdbdd4dd9; op2val:0xb7debb9b
LI(x16,0xdbdd4dd9);
LI(x17,0xb7debb9b);
add x18, x16, x17;
sha512sig0h x16, x18, x17;
add x19, x16, x17;
RVTEST_SIGUPD(x31,x18,564);
RVTEST_SIGUPD(x31,x16,568);
RVTEST_SIGUPD(x31,x19,572);

inst_16:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x19; op2:x18; dest1:x17; op1val:0xab8534c1; op2val:0x242a809b
LI(x17,0xab8534c1);
LI(x18,0x242a809b);
xor x19, x17, x18;
sha512sig0h x17, x19, x18;
xor x20, x17, x18;
RVTEST_SIGUPD(x31,x19,576);
RVTEST_SIGUPD(x31,x17,580);
RVTEST_SIGUPD(x31,x20,584);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x19; op2:x18; dest1:x17; op1val:0xab8534c1; op2val:0x242a809b
LI(x17,0xab8534c1);
LI(x18,0x242a809b);
not x19, x18;
sha512sig0h x17, x19, x18;
not x20, x17;
RVTEST_SIGUPD(x31,x19,588);
RVTEST_SIGUPD(x31,x17,592);
RVTEST_SIGUPD(x31,x20,596);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x19; op2:x18; dest1:x17; op1val:0xab8534c1; op2val:0x242a809b
LI(x17,0xab8534c1);
LI(x18,0x242a809b);
add x19, x17, x18;
sha512sig0h x17, x19, x18;
add x20, x17, x18;
RVTEST_SIGUPD(x31,x19,600);
RVTEST_SIGUPD(x31,x17,604);
RVTEST_SIGUPD(x31,x20,608);

inst_17:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x20; op2:x19; dest1:x18; op1val:0xffec35fe; op2val:0x6c69a172
LI(x18,0xffec35fe);
LI(x19,0x6c69a172);
xor x20, x18, x19;
sha512sig0h x18, x20, x19;
xor x21, x18, x19;
RVTEST_SIGUPD(x31,x20,612);
RVTEST_SIGUPD(x31,x18,616);
RVTEST_SIGUPD(x31,x21,620);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x20; op2:x19; dest1:x18; op1val:0xffec35fe; op2val:0x6c69a172
LI(x18,0xffec35fe);
LI(x19,0x6c69a172);
not x20, x19;
sha512sig0h x18, x20, x19;
not x21, x18;
RVTEST_SIGUPD(x31,x20,624);
RVTEST_SIGUPD(x31,x18,628);
RVTEST_SIGUPD(x31,x21,632);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x20; op2:x19; dest1:x18; op1val:0xffec35fe; op2val:0x6c69a172
LI(x18,0xffec35fe);
LI(x19,0x6c69a172);
add x20, x18, x19;
sha512sig0h x18, x20, x19;
add x21, x18, x19;
RVTEST_SIGUPD(x31,x20,636);
RVTEST_SIGUPD(x31,x18,640);
RVTEST_SIGUPD(x31,x21,644);

inst_18:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x21; op2:x20; dest1:x19; op1val:0x35a7efc0; op2val:0x9c1a1528
LI(x19,0x35a7efc0);
LI(x20,0x9c1a1528);
xor x21, x19, x20;
sha512sig0h x19, x21, x20;
xor x22, x19, x20;
RVTEST_SIGUPD(x31,x21,648);
RVTEST_SIGUPD(x31,x19,652);
RVTEST_SIGUPD(x31,x22,656);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x21; op2:x20; dest1:x19; op1val:0x35a7efc0; op2val:0x9c1a1528
LI(x19,0x35a7efc0);
LI(x20,0x9c1a1528);
not x21, x20;
sha512sig0h x19, x21, x20;
not x22, x19;
RVTEST_SIGUPD(x31,x21,660);
RVTEST_SIGUPD(x31,x19,664);
RVTEST_SIGUPD(x31,x22,668);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x21; op2:x20; dest1:x19; op1val:0x35a7efc0; op2val:0x9c1a1528
LI(x19,0x35a7efc0);
LI(x20,0x9c1a1528);
add x21, x19, x20;
sha512sig0h x19, x21, x20;
add x22, x19, x20;
RVTEST_SIGUPD(x31,x21,672);
RVTEST_SIGUPD(x31,x19,676);
RVTEST_SIGUPD(x31,x22,680);

inst_19:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x22; op2:x21; dest1:x20; op1val:0x4133e4d7; op2val:0x74f5add5
LI(x20,0x4133e4d7);
LI(x21,0x74f5add5);
xor x22, x20, x21;
sha512sig0h x20, x22, x21;
xor x23, x20, x21;
RVTEST_SIGUPD(x31,x22,684);
RVTEST_SIGUPD(x31,x20,688);
RVTEST_SIGUPD(x31,x23,692);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x22; op2:x21; dest1:x20; op1val:0x4133e4d7; op2val:0x74f5add5
LI(x20,0x4133e4d7);
LI(x21,0x74f5add5);
not x22, x21;
sha512sig0h x20, x22, x21;
not x23, x20;
RVTEST_SIGUPD(x31,x22,696);
RVTEST_SIGUPD(x31,x20,700);
RVTEST_SIGUPD(x31,x23,704);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x22; op2:x21; dest1:x20; op1val:0x4133e4d7; op2val:0x74f5add5
LI(x20,0x4133e4d7);
LI(x21,0x74f5add5);
add x22, x20, x21;
sha512sig0h x20, x22, x21;
add x23, x20, x21;
RVTEST_SIGUPD(x31,x22,708);
RVTEST_SIGUPD(x31,x20,712);
RVTEST_SIGUPD(x31,x23,716);

inst_20:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x23; op2:x22; dest1:x21; op1val:0x81aa70ac; op2val:0x437cbc41
LI(x21,0x81aa70ac);
LI(x22,0x437cbc41);
xor x23, x21, x22;
sha512sig0h x21, x23, x22;
xor x24, x21, x22;
RVTEST_SIGUPD(x31,x23,720);
RVTEST_SIGUPD(x31,x21,724);
RVTEST_SIGUPD(x31,x24,728);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x23; op2:x22; dest1:x21; op1val:0x81aa70ac; op2val:0x437cbc41
LI(x21,0x81aa70ac);
LI(x22,0x437cbc41);
not x23, x22;
sha512sig0h x21, x23, x22;
not x24, x21;
RVTEST_SIGUPD(x31,x23,732);
RVTEST_SIGUPD(x31,x21,736);
RVTEST_SIGUPD(x31,x24,740);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x23; op2:x22; dest1:x21; op1val:0x81aa70ac; op2val:0x437cbc41
LI(x21,0x81aa70ac);
LI(x22,0x437cbc41);
add x23, x21, x22;
sha512sig0h x21, x23, x22;
add x24, x21, x22;
RVTEST_SIGUPD(x31,x23,744);
RVTEST_SIGUPD(x31,x21,748);
RVTEST_SIGUPD(x31,x24,752);

inst_21:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x24; op2:x23; dest1:x22; op1val:0xb847f03e; op2val:0xcb256db7
LI(x22,0xb847f03e);
LI(x23,0xcb256db7);
xor x24, x22, x23;
sha512sig0h x22, x24, x23;
xor x25, x22, x23;
RVTEST_SIGUPD(x31,x24,756);
RVTEST_SIGUPD(x31,x22,760);
RVTEST_SIGUPD(x31,x25,764);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x24; op2:x23; dest1:x22; op1val:0xb847f03e; op2val:0xcb256db7
LI(x22,0xb847f03e);
LI(x23,0xcb256db7);
not x24, x23;
sha512sig0h x22, x24, x23;
not x25, x22;
RVTEST_SIGUPD(x31,x24,768);
RVTEST_SIGUPD(x31,x22,772);
RVTEST_SIGUPD(x31,x25,776);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x24; op2:x23; dest1:x22; op1val:0xb847f03e; op2val:0xcb256db7
LI(x22,0xb847f03e);
LI(x23,0xcb256db7);
add x24, x22, x23;
sha512sig0h x22, x24, x23;
add x25, x22, x23;
RVTEST_SIGUPD(x31,x24,780);
RVTEST_SIGUPD(x31,x22,784);
RVTEST_SIGUPD(x31,x25,788);

inst_22:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x25; op2:x24; dest1:x23; op1val:0xbd8d9d60; op2val:0x9c3d087c
LI(x23,0xbd8d9d60);
LI(x24,0x9c3d087c);
xor x25, x23, x24;
sha512sig0h x23, x25, x24;
xor x26, x23, x24;
RVTEST_SIGUPD(x31,x25,792);
RVTEST_SIGUPD(x31,x23,796);
RVTEST_SIGUPD(x31,x26,800);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x25; op2:x24; dest1:x23; op1val:0xbd8d9d60; op2val:0x9c3d087c
LI(x23,0xbd8d9d60);
LI(x24,0x9c3d087c);
not x25, x24;
sha512sig0h x23, x25, x24;
not x26, x23;
RVTEST_SIGUPD(x31,x25,804);
RVTEST_SIGUPD(x31,x23,808);
RVTEST_SIGUPD(x31,x26,812);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x25; op2:x24; dest1:x23; op1val:0xbd8d9d60; op2val:0x9c3d087c
LI(x23,0xbd8d9d60);
LI(x24,0x9c3d087c);
add x25, x23, x24;
sha512sig0h x23, x25, x24;
add x26, x23, x24;
RVTEST_SIGUPD(x31,x25,816);
RVTEST_SIGUPD(x31,x23,820);
RVTEST_SIGUPD(x31,x26,824);

inst_23:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x26; op2:x25; dest1:x24; op1val:0xbeb2993a; op2val:0xf37e27a3
LI(x24,0xbeb2993a);
LI(x25,0xf37e27a3);
xor x26, x24, x25;
sha512sig0h x24, x26, x25;
xor x27, x24, x25;
RVTEST_SIGUPD(x31,x26,828);
RVTEST_SIGUPD(x31,x24,832);
RVTEST_SIGUPD(x31,x27,836);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x26; op2:x25; dest1:x24; op1val:0xbeb2993a; op2val:0xf37e27a3
LI(x24,0xbeb2993a);
LI(x25,0xf37e27a3);
not x26, x25;
sha512sig0h x24, x26, x25;
not x27, x24;
RVTEST_SIGUPD(x31,x26,840);
RVTEST_SIGUPD(x31,x24,844);
RVTEST_SIGUPD(x31,x27,848);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x26; op2:x25; dest1:x24; op1val:0xbeb2993a; op2val:0xf37e27a3
LI(x24,0xbeb2993a);
LI(x25,0xf37e27a3);
add x26, x24, x25;
sha512sig0h x24, x26, x25;
add x27, x24, x25;
RVTEST_SIGUPD(x31,x26,852);
RVTEST_SIGUPD(x31,x24,856);
RVTEST_SIGUPD(x31,x27,860);

inst_24:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x27; op2:x26; dest1:x25; op1val:0x0cd5d8e2; op2val:0x90af95fe
LI(x25,0x0cd5d8e2);
LI(x26,0x90af95fe);
xor x27, x25, x26;
sha512sig0h x25, x27, x26;
xor x28, x25, x26;
RVTEST_SIGUPD(x31,x27,864);
RVTEST_SIGUPD(x31,x25,868);
RVTEST_SIGUPD(x31,x28,872);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x27; op2:x26; dest1:x25; op1val:0x0cd5d8e2; op2val:0x90af95fe
LI(x25,0x0cd5d8e2);
LI(x26,0x90af95fe);
not x27, x26;
sha512sig0h x25, x27, x26;
not x28, x25;
RVTEST_SIGUPD(x31,x27,876);
RVTEST_SIGUPD(x31,x25,880);
RVTEST_SIGUPD(x31,x28,884);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x27; op2:x26; dest1:x25; op1val:0x0cd5d8e2; op2val:0x90af95fe
LI(x25,0x0cd5d8e2);
LI(x26,0x90af95fe);
add x27, x25, x26;
sha512sig0h x25, x27, x26;
add x28, x25, x26;
RVTEST_SIGUPD(x31,x27,888);
RVTEST_SIGUPD(x31,x25,892);
RVTEST_SIGUPD(x31,x28,896);

inst_25:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x28; op2:x27; dest1:x26; op1val:0xfff5618b; op2val:0x596f5f89
LI(x26,0xfff5618b);
LI(x27,0x596f5f89);
xor x28, x26, x27;
sha512sig0h x26, x28, x27;
xor x29, x26, x27;
RVTEST_SIGUPD(x31,x28,900);
RVTEST_SIGUPD(x31,x26,904);
RVTEST_SIGUPD(x31,x29,908);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x28; op2:x27; dest1:x26; op1val:0xfff5618b; op2val:0x596f5f89
LI(x26,0xfff5618b);
LI(x27,0x596f5f89);
not x28, x27;
sha512sig0h x26, x28, x27;
not x29, x26;
RVTEST_SIGUPD(x31,x28,912);
RVTEST_SIGUPD(x31,x26,916);
RVTEST_SIGUPD(x31,x29,920);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x28; op2:x27; dest1:x26; op1val:0xfff5618b; op2val:0x596f5f89
LI(x26,0xfff5618b);
LI(x27,0x596f5f89);
add x28, x26, x27;
sha512sig0h x26, x28, x27;
add x29, x26, x27;
RVTEST_SIGUPD(x31,x28,924);
RVTEST_SIGUPD(x31,x26,928);
RVTEST_SIGUPD(x31,x29,932);

inst_26:
// Forwarded xor into sha512sig0h & the result back into xor
// opcode: sha512sig0h; op1:x29; op2:x28; dest1:x27; op1val:0xb4dc7dee; op2val:0x9c1f741f
LI(x27,0xb4dc7dee);
LI(x28,0x9c1f741f);
xor x29, x27, x28;
sha512sig0h x27, x29, x28;
xor x30, x27, x28;
RVTEST_SIGUPD(x31,x29,936);
RVTEST_SIGUPD(x31,x27,940);
RVTEST_SIGUPD(x31,x30,944);

// Forwarded not into sha512sig0h & the result back into not
// opcode: sha512sig0h; op1:x29; op2:x28; dest1:x27; op1val:0xb4dc7dee; op2val:0x9c1f741f
LI(x27,0xb4dc7dee);
LI(x28,0x9c1f741f);
not x29, x28;
sha512sig0h x27, x29, x28;
not x30, x27;
RVTEST_SIGUPD(x31,x29,948);
RVTEST_SIGUPD(x31,x27,952);
RVTEST_SIGUPD(x31,x30,956);

// Forwarded add into sha512sig0h & the result back into add
// opcode: sha512sig0h; op1:x29; op2:x28; dest1:x27; op1val:0xb4dc7dee; op2val:0x9c1f741f
LI(x27,0xb4dc7dee);
LI(x28,0x9c1f741f);
add x29, x27, x28;
sha512sig0h x27, x29, x28;
add x30, x27, x28;
RVTEST_SIGUPD(x31,x29,960);
RVTEST_SIGUPD(x31,x27,964);
RVTEST_SIGUPD(x31,x30,968);

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
