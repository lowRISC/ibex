// Copyleft 

// Masks to isolate bits 6-0 and 14-12
#define MASK_6_0     0x0000007F  // Mask for bits 6-0 (7 bits)
#define MASK_14_12   0x00007000  // Mask for bits 14-12 (3 bits)

// Macro to clear and set bits 6-0 (opcode)
#define SET_BITS_6_0(value, new_bits) \
    (((value) & ~MASK_6_0) | ((new_bits) & MASK_6_0))

// Macro to clear and set bits 14-12 (funct3)
#define SET_BITS_14_12(value, new_bits) \
    (((value) & ~MASK_14_12) | (((new_bits) << 12) & MASK_14_12))


#include "simple_system_common.h"
#include "tinyprintf.h"

// Define START_TIMING and END_TIMING macros
#define START_TIMING(initval)  initval = getTicks()
#define END_TIMING(initval, value)  printf("Timing for %s: %u cycles\n", value, getTicks() - initval)

int main(int argc, char **argv) {

  printf("Hello test instr\n");

    unsigned int enc_instr64 = 0xBEAD0000;  // Example value
   unsigned int dummy = 0xBADCAFE;

    // Setting bits 6-0 and 14-12 using macros
    enc_instr64 = SET_BITS_6_0(enc_instr64, 0x3F);  // Set bits 6-0 to 0x3F
    enc_instr64 = SET_BITS_14_12(enc_instr64, 0x3);   // Set bits 14-12 to 0x3







unsigned int startTicks;

START_TIMING(startTicks);
asm volatile (
  "li t3, 0xBADCAFE\n"   // Load 1 into t3
  "li t4, 0xBADCAFE\n"   // Load 2 into t4
  "li t5, 0xBADCAFE\n"   // Load 3 into t5
  "li t6, 0xBADCAFE\n"   // Load 4 into t6
  :                // No output operands
  :                // No input operands
  : "t3", "t4", "t5", "t6"  // Clobber list (indicates the registers modified)
);
END_TIMING(startTicks, "loading t3-t6 with immediate values ");

#ifdef vlen64
    // Inline assembly to output the values
 asm volatile (
  ".word 0xBEAD003F\n"
  ".word 0xBADCAFE\n"

  );
 #else
//      vle32.q Q0, 1, 2, 3, 4                  # encoding: [0x7f,0x50,0x00,0x06,0x01,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x01,0x00,0x00,0x00]
START_TIMING(startTicks);
 asm volatile (
  ".word 0x0600507f\n"
  ".word 0xBADCAFE\n"
  ".word 0xBADCAFE\n"
  ".word 0xBADCAFE\n"
  ".word 0xBADCAFE\n"

  );
END_TIMING(startTicks, "vle32.q Q0, 1, 2, 3, 4 ");
//       vle32.q Q1, 10, 20, 30, 40                  # encoding: [0xff,0x50,0x00,0x06,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]
 asm volatile (
  ".word 0x060050ff\n"
  ".word 0x00000010\n"
  ".word 0x00000020\n"
  ".word 0x00000030\n"
  ".word 0x00000040\n"

  );

//       vle32.q Q2, 1, 2, 3, 3                  # encoding: [0x7f,0x51,0x00,0x06,0x01,0x00,0x00,0x00,0x02,0x00,0x00,0x00,0x03,0x00,0x00,0x00,0x03,0x00,0x00,0x00]
asm volatile (
  ".word 0x0600517f\n"
  ".word 0x00000001\n"
  ".word 0x00000002\n"
  ".word 0x00000003\n"
  ".word 0x00000003\n"

  );

//       vle32.q Q3, 1, 1, 28, 28                # encoding: [0xff,0x51,0x00,0x06,0x01,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x1c,0x00,0x00,0x00,0x1c,0x00,0x00,0x00]
asm volatile (
  ".word 0x060051ff\n"
  ".word 0x00000001\n"
  ".word 0x00000001\n"
  ".word 0x0000001c\n"
  ".word 0x0000001c\n"

  );

//      conv2dex.f32    a0, Q0, s2, Q3, s1, Q2, Q1, Q0, s0 # encoding: [0x7f,0x15,0x99,0x00,0x01,0x80,0x21,0x00,0x08,0x00,0x00,0x00]
asm volatile (
  ".word 0x0099157f\n"
  ".word 0x00218001\n"
  ".word 0x00000008\n"

  );
asm volatile (
  "li a0, 0xBADCAFE\n"
  "li s2, 0xBADBEE\n"
  "li s1, 0xDADA\n"
);
 //     gemm.f32        a0, Q0, s2, Q0, s1, Q0, zero, 0, 0 # encoding: [0x3f,0x05,0x99,0x0e,0x00,0x00,0x00,0x00]
asm volatile (
  ".word 0x0e99053f\n"
  ".word 0x00000000\n"
  );
printf("custom-0 instr begin\n");    

  asm volatile(".word (0x0       << 25) | \
              (0b11101   << 20) | \
              (0b11100   << 15) | \
              (0x00      <<  7) | \
              (0b0001011 <<  0)   \n");
     volatile int errors = 0;

    asm volatile(".word (0x0       << 25) | \
              (0b11101   << 20) | \
              (0b11100   << 15) | \
              (0x00      <<  7) | \
              (0b0001011 <<  0)   \n");            
//errors=1;
  asm volatile(".word (0b00111   << 27) | \
              (0b00      << 25) | \
              (0b00110   << 20) | \
              (0b00101   << 15) | \
              (0b0       << 14) | \
              (0b0       << 13) | \
              (0b001     << 10) | \
              (0b001     <<  7) | \
              (0b0101011 <<  0)   \n");
           printf("custom-0 instr end\n");      
#endif

  return 0;
}
