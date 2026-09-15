#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
RISCVDIR="$DIR/.."
RISCVTESTDIR="$RISCVDIR/sail-riscv/test"

RED='\033[0;91m'
GREEN='\033[0;92m'
YELLOW='\033[0;93m'
NC='\033[0m'

rm -f $DIR/tests.xml

pass=0
fail=0
XML=""

function green {
    (( pass += 1 ))
    printf "$1: ${GREEN}$2${NC}\n"
    XML+="    <testcase name=\"$1\"/>\n"
}

function yellow {
    (( fail += 1 ))
    printf "$1: ${YELLOW}$2${NC}\n"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function red {
    (( fail += 1 ))
    printf "$1: ${RED}$2${NC}\n"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function finish_suite {
    printf "$1: Passed ${pass} out of $(( pass + fail ))\n\n"
    XML="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$XML  </testsuite>\n"
    printf "$XML" >> $DIR/tests.xml
    XML=""
    pass=0
    fail=0
}

SAILLIBDIR="$DIR/../../lib/"

printf "<testsuites>\n" >> $DIR/tests.xml

cd $RISCVDIR

# Do 'make clean' to avoid cross-arch pollution.
make clean

printf "Building 64-bit RISCV specification...\n"

if make ocaml_emulator/cheri_riscv_ocaml_sim_RV64 ;
then
    green "Building 64-bit RISCV OCaml emulator" "ok"
else
    red "Building 64-bit RISCV OCaml emulator" "fail"
fi
for test in $RISCVTESTDIR/riscv-tests/rv64*.elf; do
    # skip F/D tests on OCaml for now
    pat='rv64ud-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    pat='rv64uf-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    if $RISCVDIR/ocaml_emulator/cheri_riscv_ocaml_sim_RV64 "$test" >"${test/.elf/.out}" 2>&1 && grep -q SUCCESS "${test/.elf/.out}"
    then
       green "OCaml-64 $(basename $test)" "ok"
    else
       red "OCaml-64 $(basename $test)" "fail"
    fi
done
finish_suite "64-bit RISCV OCaml tests"

if make c_emulator/cheri_riscv_sim_RV64;
then
    green "Building 64-bit RISCV C emulator" "ok"
else
    red "Building 64-bit RISCV C emulator" "fail"
fi
for test in $RISCVTESTDIR/riscv-tests/rv64*.elf; do
    if timeout 5 $RISCVDIR/c_emulator/cheri_riscv_sim_RV64 -p $test > ${test%.elf}.cout 2>&1 && grep -q SUCCESS ${test%.elf}.cout
    then
	green "C-64 $(basename $test)" "ok"
    else
	red "C-64 $(basename $test)" "fail"
    fi
done
finish_suite "64-bit RISCV C tests"

printf "</testsuites>\n" >> $DIR/tests.xml
