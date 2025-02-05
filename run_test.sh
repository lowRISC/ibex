#!/bin/bash

set -euo pipefail

TEST_NAME=$1

cd dv/uvm/core_ibex

RETCODE=0
make SIMULATOR=vcs TEST=$TEST_NAME ITERATIONS=1 WAVES=1 || RETCODE=$?

if [[ $RETCODE -ne 0 ]]; then
    mv /tmp/code/dv/uvm/core_ibex/out/run/tests /tmp/artifacts
    cat /tmp/artifacts/**/rtl_sim.log
    vpd2vcd $(ls /tmp/artifacts/**/waves.vpd) /tmp/artifacts/waves.vcd
fi

exit $RETCODE
