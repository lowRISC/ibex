
#define TINYPRINTF_DEFINE_TFP_PRINTF   1
#define TINYPRINTF_DEFINE_TFP_SPRINTF  1 
#include "tinyprintf.h"

#include "simple_system_common.h"


extern int main(int argc, char *argv[]);



 void _putcf (void * unused, char c) {
  (int)unused;
  DEV_WRITE(SIM_CTRL_BASE + SIM_CTRL_OUT, (unsigned char)c); 
}

int putchar(char c){
  _putcf (0,  c);
  return 1;
}



void startup(){
 init_printf(0, _putcf);
 main(0, 0);
}