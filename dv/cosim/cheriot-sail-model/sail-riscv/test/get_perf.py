#!/usr/bin/python
# Estimates the performance of the C backend based on aggregating the unit-tests.
# Assumes a complete run over the unit-tests has been done.

import os, glob

def test_perf(d, test_pat, test_type):
    couts = glob.glob(os.path.join(d, test_pat))
    if len(couts) == 0: return

    total_insts = 0
    total_msecs = 0
    for c in couts:
        with open(c, "r") as f:
            insts = 0
            msecs = 0
            perf  = None
            for l in f.readlines():
                if l.startswith("Instructions:"): insts = int(l.split()[1])
                if l.startswith("Execution:"):    msecs = int(l.split()[1])
                if l.startswith("Perf:"):         perf  = l
            #print("Test {0}: {1} insts, {2} msecs".format(c, insts, msecs))
            #if perf: print(perf)
            total_insts += insts
            total_msecs += msecs

    Kips = total_insts/total_msecs if total_msecs != 0 else float("nan")
    print("Average {0} performance: {1} Kips".format(test_type, Kips))

def get_test_pat(iset, emode):
    return "rv64{0}-{1}-*.cout".format(iset, emode)

if __name__ == '__main__':
    test_dir = os.path.join(os.path.dirname(__file__), "riscv-tests")
    for mode in ["p", "v"]:
        test_perf(test_dir, get_test_pat("ui", mode), "ui-{0}".format(mode))
        test_perf(test_dir, get_test_pat("um", mode), "um-{0}".format(mode))
        test_perf(test_dir, get_test_pat("ua", mode), "ua-{0}".format(mode))
        test_perf(test_dir, get_test_pat("uc", mode), "uc-{0}".format(mode))
        test_perf(test_dir, get_test_pat("si", mode), "si-{0}".format(mode))
        test_perf(test_dir, get_test_pat("mi", mode), "mi-{0}".format(mode))
        test_perf(test_dir, get_test_pat("*",  mode), mode)
