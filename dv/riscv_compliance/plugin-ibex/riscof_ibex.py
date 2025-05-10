import os
import logging

import riscof.utils as utils
from riscof.pluginTemplate import pluginTemplate

logger = logging.getLogger()

class ibex(pluginTemplate):
    __model__ = "ibex"
    __version__ = "XXX"

    def __init__(self, *args, **kwargs):
        sclass = super().__init__(*args, **kwargs)
        config = kwargs.get('config')
        if config is None:
            print("Please enter input file paths in configuration.")
            raise SystemExit(1)
        #self.dut_exe = os.path.join(config['PATH'] if 'PATH' in config else "","serv")
        #self.num_jobs = str(config['jobs'] if 'jobs' in config else 1)
        self.pluginpath=os.path.abspath(config['pluginpath'])
        self.isa_spec = os.path.abspath(config['ispec'])
        self.platform_spec = os.path.abspath(config['pspec'])
        if 'target_run' in config and config['target_run']=='0':
            self.target_run = False
        else:
            self.target_run = True
        return sclass

    def initialise(self, suite, work_dir, archtest_env):
       self.compile_cmd = 'riscv64-unknown-elf-gcc -march={0} \
         -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g\
         -T '+self.pluginpath+'/env/link.ld\
         -I '+self.pluginpath+'/env/\
         -I ' + archtest_env + ' {1} -o {2} {3}'
       self.objcopy_cmd = 'riscv64-unknown-elf-objcopy -O binary {0} {1}.bin'
       self.objdump_cmd = 'riscv64-unknown-elf-objdump -D {0} > {1}.disass'
       self.vmem_cmd    = 'srec_cat {0}.bin -binary -offset 0x0000 -byte-swap 4 -o {0}.vmem -vmem'
       self.simulate_cmd = './build/lowrisc_ibex_ibex_riscv_compliance_3.5/sim-verilator/Vibex_riscv_compliance \
        --term-after-cycles=100000 \
        --raminit={0}/{1}.vmem \
        > {0}/signature.stdout'
       self.sigdump_cmd = 'grep \"^SIGNATURE: \" signature.stdout | sed \'s/SIGNATURE: 0x//\' > DUT-ibex.signature'

       buil_ibex = 'fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_riscv_compliance --RV32E=0 --RV32M=ibex_pkg::RV32MNone'
       utils.shellCommand(buil_ibex).run()
  
    def build(self, isa_yaml, platform_yaml):
      ispec = utils.load_yaml(isa_yaml)['hart0']
      self.xlen = ('64' if 64 in ispec['supported_xlen'] else '32')
      self.isa = 'rv' + self.xlen
      if "I" in ispec["ISA"]:
          self.isa += 'i'
      if "M" in ispec["ISA"]:
          self.isa += 'm'
      if "F" in ispec["ISA"]:
          self.isa += 'f'
      if "D" in ispec["ISA"]:
          self.isa += 'd'
      if "C" in ispec["ISA"]:
          self.isa += 'c'
      self.compile_cmd = self.compile_cmd+' -mabi='+('lp64 ' if 64 in ispec['supported_xlen'] else 'ilp32 ')

    def runTests(self, testList):
      for testname in testList:
          testentry = testList[testname]
          test = testentry['test_path']
          test_dir = testentry['work_dir']
          file_name = 'ibex-{0}'.format(test.rsplit('/',1)[1][:-2])

          elf = '{0}.elf'.format(file_name)
          compile_macros= ' -D' + " -D".join(testentry['macros'])
          marchstr = testentry['isa'].lower()

          compile_run = self.compile_cmd.format(marchstr, test, elf, compile_macros)
          utils.shellCommand(compile_run).run(cwd=test_dir)
          
          objcopy_run = self.objcopy_cmd.format(elf,file_name)
          utils.shellCommand(objcopy_run).run(cwd=test_dir)
          
          objdump_run = self.objdump_cmd.format(elf,file_name)
          utils.shellCommand(objdump_run).run(cwd=test_dir)

          vmem_run = self.vmem_cmd.format(file_name)
          utils.shellCommand(vmem_run).run(cwd=test_dir)

          sim_run = self.simulate_cmd.format(test_dir,file_name)
          utils.shellCommand(sim_run).run()

          utils.shellCommand(self.sigdump_cmd).run(cwd=test_dir)
      if not self.target_run:
          raise SystemExit