import spike32  # pylint: disable=import-error

import targets
import testlib

class spike32_2(targets.Target):
    harts = [spike32.spike32_hart(misa=0x40141125),
            spike32.spike32_hart(misa=0x40141125)]
    openocd_config_path = "spike-2.cfg"
    timeout_sec = 30
    implements_custom_test = True

    def create(self):
        return testlib.Spike(self, isa="RV32IMAFC", progbufsize=0, dmi_rti=4,
                support_abstract_csr=True, support_abstract_fpr=True,
                support_haltgroups=False)
