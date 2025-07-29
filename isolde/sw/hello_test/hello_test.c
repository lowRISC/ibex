/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

//#include <stdio.h>
#include <bsp/tinyprintf.h>
#include <bsp/simple_system_common.h>
#include <bsp/simple_system_regs.h>
#include <stdlib.h>


int main(int argc, char *argv[]) {

    printf("***  \n");
    printf("***  Hello World from ISOLDE!\n");
    printf("***  \n");
    #ifdef RV_DM_TEST
    while (1) {
        asm volatile ("wfi");
    }
    #else
    return 0xBADC0FFE;
    #endif

}
