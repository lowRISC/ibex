import logging
import os
import shutil
import string
import sys

import riscof.utils as utils
import riscof.constants as constants
from riscof.pluginTemplate import pluginTemplate

logger = logging.getLogger()

class rc_reference(pluginTemplate):
    __model__ = "rc_reference"
    __version__ = "0.1.0"

    def __init__(self, *args, **kwargs):
        sclass = super().__init__(*args, **kwargs)

        config = kwargs.get('config')
        if config is None:
            print("Please enter input file paths in configuration.")
            raise SystemExit

        test_suite = os.getenv('RISCV_TEST_SUITE')
        if test_suite is None:
            config_dir = kwargs.get('config_dir')
            test_suite_entry = config.get('riscvTestSuite')
            if test_suite_entry:
                test_suite = utils.absolute_path(config_dir, test_suite_entry)
            else:
                logger.error("Path to reference signature not set. "\
                        "Please set envrionment variable 'RISCV_TEST_SUITE' "\
                        "or config key 'riscvTestSuite'.")
                raise SystemExit
        self.test_suite_path = test_suite

        return sclass

    def initialise(self, suite, work_dir, compliance_env):
        self.work_dir = work_dir


    def build(self, isa_yaml, platform_yaml):
        return

    def runTests(self, testList):
        for file in testList:
            testentry = testList[file]
            test = os.path.join(constants.root, str(file))
            test_dir = testentry['work_dir']

            test_name = os.path.splitext(os.path.basename(test))[0]

            # Extract the extension of the current test
            tested_extension = os.path.split(os.path.dirname(os.path.dirname(test_dir)))[1]

            # Create the path to the reference signature based on the current
            # extension and a known file structure
            ref_sig = os.path.join(self.test_suite_path, tested_extension)
            ref_sig = os.path.join(ref_sig, "references")
            ref_sig = os.path.join(ref_sig, test_name + ".reference_output")

            # Output file is stored in the current test output and a fixed file name
            test_sig = os.path.join(test_dir, "Reference-rc_reference.signature")

            # Copy reference signature as test signature
            shutil.copyfile(ref_sig, test_sig)
