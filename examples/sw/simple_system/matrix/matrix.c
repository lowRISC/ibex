/*
 * Copyright 2020 ETH Zurich
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include "simple_system_common.h"

void matmulNxN(float* matA, float* matB, float* matC, const int N);

#define N 25

float matA[N*N], matB[N*N];
float matC[N*N], matC_ref[N*N];

void activate_random_stall(void)
{
  // Address vector for rnd_stall_reg, to control memory stalls/interrupt
  volatile unsigned int *rnd_stall_reg[16];

  // Setup the address vector
  rnd_stall_reg[0] = 0x16000000;
  for (int i = 1; i < 16; i++) {
    rnd_stall_reg[i] = rnd_stall_reg[i-1] + 1; // It is a pointer to int ("+ 1" means "the next int")
  }

  /* The interposition of the stall generator between CPU and MEM should happen BEFORE the stall generetor is active */
  // Interpose the stall generator between CPU and D-MEM (rnd_stall_reg[1])
  *rnd_stall_reg[1] = 0x01;
  // Interpose the stall generator between CPU and I-MEM (rnd_stall_reg[0])
  *rnd_stall_reg[0] = 0x01;

  // DATA MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[5])
  *rnd_stall_reg[5] = 0x05;
  // Set n. stalls on  GNT (rnd_stall_reg[7])
  *rnd_stall_reg[7] = 0x05;
  // Set n. stalls on VALID (rnd_stall_reg[9])
  *rnd_stall_reg[9] = 0x05;

  // INSTRUCTION MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[4])
  *rnd_stall_reg[4] = 0x05;
  // Set n. stalls on  GNT (rnd_stall_reg[6])
  *rnd_stall_reg[6] = 0x05;
  // Set n. stalls on VALID (rnd_stall_reg[8])
  *rnd_stall_reg[8] = 0x05;

  /* Activating stalls on D and I Mem has to be done as last operation. Do not change the order. */
  // Set stall mode on D-MEM (off=0, standard=1, random=2) (rnd_stall_reg[3])
  *rnd_stall_reg[3] = 0x02;
  // Set stall mode on I-MEM (off=0, standard=1, random=2) (rnd_stall_reg[2])
  *rnd_stall_reg[2] = 0x02;
}

int main(int argc, char *argv[])
{

#ifdef RANDOM_MEM_STALL
    activate_random_stall();
#endif

  for (int i = 0; i < N; ++i) {
    matC_ref[i] = 9469.599609375f;
  }
  for (int i = N; i < 2*N; ++i) {
    matC_ref[i] = 9402.7197265625f;
  }
  for (int i = 2*N; i < 3*N; ++i) {
    matC_ref[i] = 9335.8408203125f;
  }
  for (int i = 3*N; i < 4*N; ++i) {
    matC_ref[i] = 9268.9609375f;
  }
  for (int i = 4*N; i < 5*N; ++i) {
    matC_ref[i] = 9202.0810546875f;
  }
  for (int i = 5*N; i < 6*N; ++i) {
    matC_ref[i] = 9135.201171875f;
  }
  for (int i = 6*N; i < 7*N; ++i) {
    matC_ref[i] = 9068.3203125f;
  }
  for (int i = 7*N; i < 8*N; ++i) {
    matC_ref[i] = 9001.44140625f;
  }
  for (int i = 8*N; i < 9*N; ++i) {
    matC_ref[i] = 8934.5625f;
  }
  for (int i = 9*N; i < 10*N; ++i){
    matC_ref[i] = 8867.681640625f;
  }
  for (int i = 10*N; i < 11*N; ++i){
    matC_ref[i] = 8800.802734375f;
  }
  for (int i = 11*N; i < 12*N; ++i){
    matC_ref[i] = 8733.921875f;
  }
  for (int i = 12*N; i < 13*N; ++i){
    matC_ref[i] = 8667.0419921875f;
  }
  for (int i = 13*N; i < 14*N; ++i){
    matC_ref[i] = 8600.162109375f;
  }
  for (int i = 14*N; i < 15*N; ++i){
    matC_ref[i] = 8533.283203125f;
  }
  for (int i = 15*N; i < 16*N; ++i){
    matC_ref[i] = 8466.4033203125f;
  }
  for (int i = 16*N; i < 17*N; ++i){
    matC_ref[i] = 8399.52246094f;
  }
  for (int i = 17*N; i < 18*N; ++i){
    matC_ref[i] = 8332.642578125f;
  }
  for (int i = 18*N; i < 19*N; ++i){
    matC_ref[i] = 8265.7646484375f;
  }
  for (int i = 19*N; i < 20*N; ++i){
    matC_ref[i] = 8198.8837890625f;
  }
  for (int i = 20*N; i < 21*N; ++i){
    matC_ref[i] = 8132.00341796875f;
  }
  for (int i = 21*N; i < 22*N; ++i){
    matC_ref[i] = 8065.12451171875f;
  }
  for (int i = 22*N; i < 23*N; ++i){
    matC_ref[i] = 7998.2451171875f;
  }
  for (int i = 23*N; i < 24*N; ++i){
    matC_ref[i] = 7931.36474609375f;
  }
  for (int i = 24*N; i < 25*N; ++i){
    matC_ref[i] = 7864.484375f;
  }


  float tmpA, tmpB, tmpC;
  int error = 0;

  tmpA = 62.299999237060546875f;
  tmpB = 0.800000011920928955078125f;
  tmpC = 0.439999997615814208984375f;

  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      matA[i*N+j] = tmpA;
      matB[i*N+j] = tmpB;
    }
    tmpA = tmpA - tmpC;
    tmpB = tmpB + tmpC;
  }

  matmulNxN(matA, matB, matC, N);

  for (int i = 0; i < N*N; ++i) {
    if (matC_ref[i] != matC[i]) {
      error++;
      puts("Error!");
      // printf("Error at index %d, expected %x, got %x\n", i, (*(int*)&matC_ref[i]), (*(int*)&matC[i]));
    }
  }

  if (error)
    return error;
  else
    return EXIT_SUCCESS;
}
