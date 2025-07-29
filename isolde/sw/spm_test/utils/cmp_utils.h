/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

#ifndef ISOLDE_CMP_UTILS__H
#define ISOLDE_CMP_UTILS__H

uint32_t cmp_arrays(uint32_t* ref, uint32_t* arr, uint32_t elems){

uint32_t testOK=1;
for (uint32_t i = 0; i < elems; ++i) {
    if (ref[i] != arr[i]) {
      printf("Error at index %d,(hex values) expected: %08x got: %08x\n", i, ref[i],
             arr[i]);
      testOK = 0;
      //break;
    }
  }
  return testOK;
}
#endif