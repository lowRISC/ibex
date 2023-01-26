import targets

class E300Hart(targets.Hart):
    xlen = 32
    ram = 0x80000000
    ram_size = 64 * 1024
    instruction_hardware_breakpoint_count = 2
    link_script_path = "Freedom.lds"

class E300(targets.Target):
    openocd_config_path = "Freedom.cfg"
    harts = [E300Hart()]
    invalid_memory_returns_zero = True
