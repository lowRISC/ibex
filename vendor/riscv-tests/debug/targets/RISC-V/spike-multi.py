import spike32  # pylint: disable=import-error
import spike64  # pylint: disable=import-error

import targets
import testlib

class multispike(targets.Target):
    harts = [
        spike32.spike32_hart(misa=0x4034112d, system=0),
        spike32.spike32_hart(misa=0x4034112d, system=0),
        spike64.spike64_hart(misa=0x8000000000341129, system=1),
        spike64.spike64_hart(misa=0x8000000000341129, system=1)]
    openocd_config_path = "spike-multi.cfg"
    timeout_sec = 30
    server_timeout_sec = 120
    implements_custom_test = True
    support_hasel = False
    support_memory_sampling = False # Needs SBA

    def create(self):
        return testlib.MultiSpike(
            [
                testlib.Spike(self, isa="RV64IMAFDV",
                    support_hasel=False, support_abstract_csr=False,
                    vlen=512, elen=64, harts=self.harts[2:]),
                testlib.Spike(self, isa="RV32IMAFDCV",
                    support_abstract_csr=True, support_haltgroups=False,
                    # elen must be at least 64 because D is supported.
                    elen=64, harts=self.harts[:2]),
                ])
