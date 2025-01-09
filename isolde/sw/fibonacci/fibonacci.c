/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */

//#include <stdio.h>
#include <bsp/tinyprintf.h>
#include <bsp/simple_system_common.h>
#include <bsp/simple_system_regs.h>
#include <stdlib.h>

static int fib(int i) {
    return (i>1) ? fib(i-1) + fib(i-2) : i;
}

 char dummyData[]={1,2,3,4,5,6};
int main(int argc, char *argv[]) {

    
    START_PERFCNT(1);

    int i;
    const int num =  sizeof(dummyData)/sizeof(dummyData[0]);

    printf("starting fib(%d)...\n", num);
    START_TIMING(FIBONACCI);
    for(i=0; i<num; i++) {
        printf("fib(%d) = %d\n", i, fib(i));

    }
    END_TIMING(FIBONACCI);
    printf("finishing...\n");

   
   
    //force missaligend reads/writes
    for(i=0;i<num;++i)
        printf("[before ]dummyData[%d] = %d\n", i, dummyData[i]);
    printf("writing test..\n");
     for(i=0;i<num;++i){
        dummyData[i]=fib(i);
        printf("[after  ]dummyData[%d] = %d\n", i, dummyData[i]);
    }
   STOP_PERFCNT(1); 
    return 0;
}
