import spike64  # pylint: disable=import-error

import targets
import testlib

class spike64_2_rtos(targets.Target):
    harts = [spike64.spike64_hart(misa=0x8000000000141129),
            spike64.spike64_hart(misa=0x8000000000141129)]
    openocd_config_path = "spike-rtos.cfg"
    timeout_sec = 60
    implements_custom_test = True
    support_hasel = False
    test_semihosting = False
    support_manual_hwbp = False # not supported with `-rtos riscv`
    support_memory_sampling = False # not supported with `-rtos riscv`

    def create(self):
        return testlib.Spike(self, abstract_rti=30, support_hasel=False,
                support_abstract_csr=False)
