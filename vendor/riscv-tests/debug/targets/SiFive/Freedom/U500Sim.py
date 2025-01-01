import targets
import testlib

class U500Hart(targets.Hart):
    xlen = 64
    ram = 0x80000000
    ram_size = 256 * 1024 * 1024
    instruction_hardware_breakpoint_count = 2
    link_script_path = "Freedom.lds"

class U500Sim(targets.Target):
    timeout_sec = 6000
    openocd_config_path = "Freedom.cfg"
    harts = [U500Hart()]

    def target(self):
        return testlib.VcsSim(sim_cmd=self.sim_cmd, debug=False)
