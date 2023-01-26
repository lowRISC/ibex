import targets

class HiFive1Hart(targets.Hart):
    xlen = 32
    ram = 0x80000000
    ram_size = 16 * 1024
    instruction_hardware_breakpoint_count = 2
    misa = 0x40001105

class HiFive1(targets.Target):
    harts = [HiFive1Hart()]
