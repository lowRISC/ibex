
/*
inspired  from
REPO   = https://github.com/five-embeddev/riscv-scratchpad.git
BRANCH = master
HASH   = de0c663
PATH   = baremetal-startup-c/src/startup.c

   Simple C++ startup routine to setup CRT
   SPDX-License-Identifier: Unlicense

   (https://five-embeddev.com/ | http://www.shincbm.com/) 


*/

#include "tinyprintf.h"
#include "simple_system_common.h"

extern int main(int argc, char *argv[]);


void startup(){
 init_printf(0, _putcf);
 int rc= main(0, 0);
  _Exit(rc);

}