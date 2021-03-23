import os
import re
import shutil
import subprocess
import shlex
import logging
import random
import string
from string import Template
import sys

import riscof.utils as utils
import riscof.constants as constants
from riscof.pluginTemplate import pluginTemplate

riscv_prefix = 'riscv32-unknown-elf-'

logger = logging.getLogger()

class Ibex(pluginTemplate):
    __model__ = "Ibex"
    __version__ = "0.1.0"

    def __init__(self, *args, **kwargs):
        sclass = super().__init__(*args, **kwargs)

        config = kwargs.get('config')
        if config is None:
            print("Please enter input file paths in configuration.")
            raise SystemExit

        config_dir = kwargs.get('config_dir')
        self.isa_spec      = utils.absolute_path(config_dir, config['ispec'])
        self.platform_spec = utils.absolute_path(config_dir, config['pspec'])
        self.modelpath     = utils.absolute_path(config_dir, config['pluginpath'])
        ibexSim = os.getenv('IBEX_SIMULATOR')
        if ibexSim is None:
           ibexSimEntry = config.get('ibexSimulator')
           if ibexSimEntry:
                ibexSim = utils.absolute_path(config_dir, ibexSimEntry)
           else:
                logger.error("Ibex simulator not set. Either use envrionment "\
                        "variable 'IBEX_SIMULATOR' or the model config key "\
                        "'ibexSimulator'.")
                raise SystemExit
        self.ibexSimulator = ibexSim

        self.riscv_prefix = os.getenv('RISCV_PREFIX', riscv_prefix)

        self.c_args = ['-march={march}',
                '-static',
                '-mcmodel=medany',
                '-fvisibility=hidden',
                '-nostdlib',
                '-nostartfiles']

        return sclass

    def initialise(self, suite, work_dir, compliance_env):
        self.work_dir = work_dir
        self.riscv_gcc = self.riscv_prefix + 'gcc'
        self.c_args += ['-T '+self.modelpath+'/env/link.ld',
                '-I '+self.modelpath+'/env/',
                '-I '+compliance_env]

    def build(self, isa_yaml, platform_yaml):
        ispec = utils.load_yaml(isa_yaml)['hart0']
        self.xlen = ispec["supported_xlen"][0]
        self.c_args += ['-mabi=ilp{xlen}', '{test}', '-o {output}']

    def runTests(self, testList):
        for file in testList:
            testentry = testList[file]
            test = os.path.join(constants.root, str(file))
            test_dir = testentry['work_dir']

            test_name = os.path.splitext(os.path.basename(test))[0]
            elf_name = '{}-{}'.format(self.name[:-1], test_name) + '.elf'

            ibex_test_path = os.path.join(test_dir, self.name[:-1])
            sig_file =  ibex_test_path + ".signature"
            sim_stdout_file = ibex_test_path + '.stdout'

            # compile each test
            args = ' '.join(self.c_args).format(
                    march = testentry['isa'].lower(),
                    xlen = self.xlen,
                    test = test,
                    output = elf_name)
            compile_cmd = self.riscv_gcc + ' ' + args + ' -D' + " -D".join(testentry['macros'])

            logger.debug('Compiling test: ' + test)
            utils.shellCommand(compile_cmd).run(cwd=test_dir)

            # execute each test on simulator/DUT
            ibex_verilator = self.ibexSimulator + \
                    ' --load-elf={}'.format(elf_name) + \
                    ' --term-after-cycle=100000 > {0}'.format(sim_stdout_file)

            logger.debug('Executing simulator' + ibex_verilator)
            utils.shellCommand(ibex_verilator).run(cwd=test_dir)

            # create signature from simulator stdout
            f_stdout = open(sim_stdout_file, 'r')
            stdout = f_stdout.read()
            r = re.compile('SIGNATURE: 0x(.*)')
            signature = r.findall(stdout)
            f_stdout.close()
            f_sig = open(sig_file, 'w')
            for s in signature:
                print(s, file=f_sig)
            f_sig.close()
