import targets

class E51(targets.Hart):
    xlen = 64
    ram = 0x80000000
    ram_size = 1024 * 1024
    bad_address = 0x3000000000 + 0x3FFFFFFFFF + 1
    instruction_hardware_breakpoint_count = 2
    reset_vectors = [0x1004]
    misa = 0x8000000000101105

class U54(targets.Hart):
    xlen = 64
    ram = 0x80000000
    ram_size = 1024 * 1024
    bad_address = 0x3000000000 + 0x3FFFFFFFFF + 1
    instruction_hardware_breakpoint_count = 2
    reset_vectors = [0x1004]
    misa = 0x800000000014112d

class HiFiveUnleashed(targets.Target):
    support_hasel = False
    support_memory_sampling = False # Needs SBA
    harts = [E51(), U54(), U54(), U54(), U54()]
