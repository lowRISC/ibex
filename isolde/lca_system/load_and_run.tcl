set INSTR_BIN ./sw/bin/hello_test-instr.bin
set DATA_BIN ./sw/bin/hello_test-data.bin
reset halt
load_image $INSTR_BIN 0x00100000 bin
load_image $DATA_BIN  0x00110000 bin
reg pc 0x100080
resume
#force exit
reset halt
reg pc 0x100000
resume
