"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Regression script for RISC-V random instruction generator
"""

import argparse
import os
import re
import subprocess
import sys

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_DV_SCRIPTS = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv/scripts')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'), _DV_SCRIPTS] +
                sys.path)

    from lib import (get_seed, process_regression_list,
                     read_yaml, run_cmd, run_parallel_cmd,
                     setup_logging, RET_FAIL)
    import logging

    from spike_log_to_trace_csv import process_spike_sim_log
    from ovpsim_log_to_trace_csv import process_ovpsim_sim_log
    from instr_trace_compare import compare_trace_csv

    from ibex_log_to_trace_csv import process_ibex_sim_log, check_ibex_uvm_log

finally:
    sys.path = _OLD_SYS_PATH


def subst_opt(string, name, enable, replacement):
    '''Substitute the <name> option in string

    If enable is False, <name> is replaced by '' in string. If it is True,
    <name> is replaced by replacement, which should be a string or None. If
    replacement is None and <name> occurs in string, we throw an error.

    '''
    needle = '<{}>'.format(name)
    if not enable:
        return string.replace(needle, '')

    if replacement is None:
        if needle in string:
            raise RuntimeError('No replacement defined for {} '
                               '(used in string: {!r}).'
                               .format(needle, string))
        return string

    return string.replace(needle, replacement)


def subst_env_vars(string, env_vars):
    '''Substitute environment variables in string

    env_vars should be a string with a comma-separated list of environment
    variables to substitute. For each environment variable, V, in the list, any
    occurrence of <V> in string will be replaced by the value of the
    environment variable with that name. If <V> occurs in the string but $V is
    not set in the environment, an error is raised.

    '''
    env_vars = env_vars.strip()
    if not env_vars:
        return string

    for env_var in env_vars.split(','):
        env_var = env_var.strip()
        needle = '<{}>'.format(env_var)
        if needle in string:
            value = os.environ.get(env_var)
            if value is None:
                raise RuntimeError('Cannot substitute {} in command because '
                                   'the environment variable ${} is not set.'
                                   .format(needle, env_var))
            string = string.replace(needle, value)

    return string


def subst_cmd(cmd, enable_dict, opts_dict, env_vars):
    '''Substitute options and environment variables in cmd

    enable_dict should be a dict mapping names to bools. For each key, N, in
    enable_dict, if enable_dict[N] is False, then all occurrences of <N> in cmd
    will be replaced with ''. If enable_dict[N] is True, all occurrences of <N>
    in cmd will be replaced with opts_dict[N].

    If N is not a key in opts_dict, this is no problem unless cmd contains
    <N>, in which case we throw a RuntimeError.

    Finally, the environment variables are substituted as described in
    subst_env_vars.

    '''
    for name, enable in enable_dict.items():
        cmd = subst_opt(cmd, name, enable, opts_dict.get(name))

    return subst_env_vars(cmd, env_vars)


def get_yaml_for_simulator(simulator, yaml_path):
    '''Read yaml at yaml_path and find entry for simulator'''
    logging.info("Processing simulator setup file : %s" % yaml_path)
    for entry in read_yaml(yaml_path):
        if entry.get('tool') == simulator:
            return entry

    raise RuntimeError("Cannot find RTL simulator {}".format(simulator))


def get_simulator_cmd(simulator, yaml_path, enables):
    '''Get compile and run commands for the testbench

    simulator is the name of the simulator to use. yaml_path is the path to a
    yaml file describing various command line options. enables is a dictionary
    keyed by option names with boolean values: true if the option is enabled.

    Returns (compile_cmds, sim_cmd), which are the simulator commands to
    compile and run the testbench, respectively. compile_cmd is a list of
    strings (multiple commands); sim_cmd is a single string.

    '''
    entry = get_yaml_for_simulator(simulator, yaml_path)
    env_vars = entry.get('env_var', '')

    return ([subst_cmd(arg, enables, entry['compile'], env_vars)
             for arg in entry['compile']['cmd']],
            subst_cmd(entry['sim']['cmd'], enables, entry['sim'], env_vars))


def rtl_compile(compile_cmds, output_dir, lsf_cmd, opts):
    """Run the instruction generator

    Args:
      compile_cmd : Compile commands
      output_dir  : Output directory of the ELF files
      lsf_cmd     : LSF command to run compilation
      opts        : Compile options for the generator
    """
    # Compile the TB
    logging.info("Compiling TB")
    for cmd in compile_cmds:
        cmd = re.sub("<out>", output_dir, cmd)
        cmd = re.sub("<cmp_opts>", opts, cmd)
        logging.debug("Compile command: %s" % cmd)
        run_cmd(cmd)


def rtl_sim(sim_cmd, simulator, test_list, output_dir, bin_dir,
            lsf_cmd, seed, opts):
    """Run the instruction generator

    Args:
      sim_cmd    : Simulation command
      simulator  : Simulator being used
      test_list  : List of assembly programs
      output_dir : Simulation output directory
      bin_dir    : Directory of the ELF files
      lsf_cmd    : LSF command to run simulation
      seed       : Seed of RTL simulation
      opts       : Simulation options
    """
    check_return_code = True
    # Don't check return code for IUS sims, as a failure will short circuit
    # the entire simulation flow
    if simulator == "ius":
        check_return_code = False
        logging.debug("Disable return code checking for %s simulator"
                      % simulator)
    # Run the RTL simulation
    sim_cmd = re.sub("<out>", output_dir, sim_cmd)
    sim_cmd = re.sub("<sim_opts>", opts, sim_cmd)
    sim_cmd = re.sub("<cwd>", _CORE_IBEX, sim_cmd)
    logging.info("Running RTL simulation...")
    cmd_list = []
    for test in test_list:
        for i in range(test['iterations']):
            rand_seed = get_seed(seed)
            test_sim_cmd = re.sub("<seed>", str(rand_seed), sim_cmd)
            if "sim_opts" in test:
                test_sim_cmd += ' '
                test_sim_cmd += test['sim_opts']
            sim_dir = output_dir + ("/%s.%d" % (test['test'], i))
            run_cmd(("mkdir -p %s" % sim_dir))
            os.chdir(sim_dir)
            binary = ("%s/%s_%d.bin" % (bin_dir, test['test'], i))
            cmd = (lsf_cmd + " " + test_sim_cmd +
                   (" +UVM_TESTNAME=%s " % test['rtl_test']) +
                   (" +bin=%s " % binary) +
                   (" -l sim.log "))
            cmd = re.sub('\n', '', cmd)
            if lsf_cmd == "":
                logging.info("Running %s with %s" % (test['rtl_test'], binary))
                run_cmd(cmd, 300, check_return_code=check_return_code)
            else:
                cmd_list.append(cmd)
    if lsf_cmd != "":
        logging.info("Running %0d simulation jobs." % len(cmd_list))
        run_parallel_cmd(cmd_list, 600, check_return_code=check_return_code)


def compare(test_list, iss, output_dir, verbose):
    """Compare RTL & ISS simulation reult

    Args:
      test_list   : List of assembly programs to be compiled
      iss         : List of instruction set simulators
      output_dir  : Output directory of the ELF files
      verbose     : Verbose logging
    """
    report = ("%s/regr.log" % output_dir).rstrip()
    for test in test_list:
        compare_opts = test.get('compare_opts', {})
        in_order_mode = compare_opts.get('in_order_mode', 1)
        coalescing_limit = compare_opts.get('coalescing_limit', 0)
        verbose = compare_opts.get('verbose', 0)
        mismatch = compare_opts.get('mismatch_print_limit', 5)
        compare_final = compare_opts.get('compare_final_value_only', 0)
        for i in range(0, test['iterations']):
            elf = ("%s/asm_tests/%s.%d.o" % (output_dir, test['test'], i))
            logging.info("Comparing %s/DUT sim result : %s" % (iss, elf))
            run_cmd(("echo 'Test binary: %s' >> %s" % (elf, report)))
            uvm_log = ("%s/rtl_sim/%s.%d/sim.log" %
                       (output_dir, test['test'], i))
            rtl_log = ("%s/rtl_sim/%s.%d/trace_core_00000000.log" %
                       (output_dir, test['test'], i))
            rtl_csv = ("%s/rtl_sim/%s.%d/trace_core_00000000.csv" %
                       (output_dir, test['test'], i))
            test_name = "%s.%d" % (test['test'], i)
            process_ibex_sim_log(rtl_log, rtl_csv, 1)
            if 'no_post_compare' in test and test['no_post_compare'] == 1:
                check_ibex_uvm_log(uvm_log, "ibex", test_name, report)
            else:
                iss_log = ("%s/instr_gen/%s_sim/%s.%d.log" %
                           (output_dir, iss, test['test'], i))
                iss_csv = ("%s/instr_gen/%s_sim/%s.%d.csv" %
                           (output_dir, iss, test['test'], i))
                if iss == "spike":
                    process_spike_sim_log(iss_log, iss_csv)
                elif iss == "ovpsim":
                    process_ovpsim_sim_log(iss_log, iss_csv)
                else:
                    logging.error("Unsupported ISS" % iss)
                    sys.exit(RET_FAIL)
                uvm_result = check_ibex_uvm_log(uvm_log, "ibex",
                                                test_name, report, False)
                if not uvm_result:
                    check_ibex_uvm_log(uvm_log, "ibex", test_name, report)
                else:
                    if 'compare_opts' in test:
                        compare_trace_csv(rtl_csv, iss_csv, "ibex", iss,
                                          report, in_order_mode,
                                          coalescing_limit, verbose,
                                          mismatch, compare_final)
                    else:
                        compare_trace_csv(rtl_csv, iss_csv, "ibex",
                                          iss, report)
    passed_cnt = run_cmd("grep PASSED %s | wc -l" % report).strip()
    failed_cnt = run_cmd("grep FAILED %s | wc -l" % report).strip()
    summary = ("%s PASSED, %s FAILED" % (passed_cnt, failed_cnt))
    logging.info(summary)
    run_cmd(("echo %s >> %s" % (summary, report)))
    logging.info("RTL & ISS regression report is saved to %s" % report)


def main():
    '''Entry point when run as a script'''

    # Parse input arguments
    parser = argparse.ArgumentParser()

    parser.add_argument("--o", type=str, default="./out",
                        help="Output directory name")
    parser.add_argument("--riscv_dv_root", type=str, default="",
                        help="Root directory of RISCV-DV")
    parser.add_argument("--testlist", type=str,
                        default="riscv_dv_extension/testlist.yaml",
                        help="Regression testlist")
    parser.add_argument("--test", type=str, default="all",
                        help="Test name, 'all' means all tests in the list")
    parser.add_argument("--seed", type=int, default=-1,
                        help=("Randomization seed; the default of -1 picks "
                              "a random seed"))
    parser.add_argument("--iterations", type=int, default=0,
                        help="Override the iteration count in the test list")
    parser.add_argument("--simulator", type=str, default="vcs",
                        help="RTL simulator to use (default: vcs)")
    parser.add_argument("--simulator_yaml", type=str,
                        default="yaml/rtl_simulation.yaml",
                        help="RTL simulator setting YAML")
    parser.add_argument("--iss", type=str, default="spike",
                        help="Instruction set simulator")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.add_argument("--cmp_opts", type=str, default="",
                        help="Compile options for the generator")
    parser.add_argument("--sim_opts", type=str, default="",
                        help="Simulation options for the generator")
    parser.add_argument("--en_cov", type=str, default=0,
                        help="Enable coverage dump")
    parser.add_argument("--en_wave", type=str, default=0,
                        help="Enable waveform dump")
    parser.add_argument("--steps", type=str, default="all",
                        help="Run steps: compile,sim,compare")
    parser.add_argument("--lsf_cmd", type=str, default="",
                        help=("LSF command. Run in local sequentially if lsf "
                              "command is not specified"))

    args = parser.parse_args()
    setup_logging(args.verbose)
    parser.set_defaults(verbose=False)

    # Create the output directory
    output_dir = ("%s/rtl_sim" % args.o)
    bin_dir = ("%s/instr_gen/asm_tests" % args.o)
    subprocess.run(["mkdir", "-p", output_dir])

    steps = {
        'compile': args.steps == "all" or re.match("compile", args.steps),
        'sim': args.steps == "all" or re.match("sim", args.steps),
        'compare': args.steps == "all" or re.match("compare", args.steps)
    }

    compile_cmds = []
    sim_cmd = ""
    matched_list = []
    if steps['compile'] or steps['sim']:
        enables = {
            'cov_opts': True if args.en_cov == '1' else False,
            'wave_opts': True if args.en_wave == '1' else False
        }
        compile_cmds, sim_cmd = get_simulator_cmd(args.simulator,
                                                  args.simulator_yaml, enables)

    if steps['sim'] or steps['compare']:
        process_regression_list(args.testlist, args.test, args.iterations,
                                matched_list, args.riscv_dv_root)
        if not matched_list:
            sys.exit("Cannot find %s in %s" % (args.test, args.testlist))

    # Compile TB
    if steps['compile']:
        rtl_compile(compile_cmds, output_dir, args.lsf_cmd, args.cmp_opts)

    # Run RTL simulation
    if steps['sim']:
        rtl_sim(sim_cmd, args.simulator, matched_list, output_dir, bin_dir,
                args.lsf_cmd, args.seed, args.sim_opts)

    # Compare RTL & ISS simulation result.;
    if steps['compare']:
        compare(matched_list, args.iss, args.o, args.verbose)


if __name__ == '__main__':
    try:
        main()
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(RET_FAIL)
