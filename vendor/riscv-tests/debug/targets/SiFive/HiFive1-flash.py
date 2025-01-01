import targets

# Like HiFive1, but put code in flash

class HiFive1FlashHart(targets.Hart):
    xlen = 32
    ram = 0x80000000
    ram_size = 16 * 1024
    instruction_hardware_breakpoint_count = 2
    misa = 0x40001105
    link_script_path = "HiFive1-flash.lds"

class HiFive1Flash(targets.Target):
    harts = [HiFive1FlashHart()]
    openocd_config_path = "HiFive1.cfg"
