#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
RISCVDIR="$DIR/.."

RED='\033[0;91m'
GREEN='\033[0;92m'
YELLOW='\033[0;93m'
NC='\033[0m'

rm -f $DIR/tests.xml

pass=0
fail=0
all_pass=0
all_fail=0
SUITE_XML=""
SUITES_XML=""

function green {
    (( pass += 1 ))
    printf "$1: ${GREEN}$2${NC}\n"
    SUITE_XML+="    <testcase name=\"$1\"/>\n"
}

function yellow {
    (( fail += 1 ))
    printf "$1: ${YELLOW}$2${NC}\n"
    SUITE_XML+="    <testcase name=\"$1\">\n      <failure message=\"$2\">$2</failure>\n    </testcase>\n"
}

function red {
    (( fail += 1 ))
    printf "$1: ${RED}$2${NC}\n"
    SUITE_XML+="    <testcase name=\"$1\">\n      <failure message=\"$2\">$2</failure>\n    </testcase>\n"
}

function finish_suite {
    printf "$1: Passed ${pass} out of $(( pass + fail ))\n\n"
    SUITES_XML+="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$SUITE_XML  </testsuite>\n"
    SUITE_XML=""
    (( all_pass += pass )) || :
    (( all_fail += fail )) || :
    pass=0
    fail=0
}

SAILLIBDIR="$DIR/../../lib/"

cd $RISCVDIR

# Do 'make clean' to avoid cross-arch pollution.
make clean

printf "Building 32-bit RISCV specification...\n"
if ARCH=RV32 make ocaml_emulator/riscv_ocaml_sim_RV32 ;
then
    green "Building 32-bit RISCV OCaml emulator" "ok"
else
    red "Building 32-bit RISCV OCaml emulator" "fail"
fi
for test in $DIR/riscv-tests/rv32*.elf; do
    # skip F/D tests on OCaml for now
    pat='rv32ud-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    pat='rv32uf-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    if $RISCVDIR/ocaml_emulator/riscv_ocaml_sim_RV32 "$test" >"${test/.elf/.out}" 2>&1 && grep -q SUCCESS "${test/.elf/.out}"
    then
       green "OCaml-32 $(basename $test)" "ok"
    else
       red "OCaml-32 $(basename $test)" "fail"
    fi
done
finish_suite "32-bit RISCV OCaml tests"


if ARCH=RV32 make c_emulator/riscv_sim_RV32;
then
    green "Building 32-bit RISCV C emulator" "ok"
else
    red "Building 32-bit RISCV C emulator" "fail"
fi
for test in $DIR/riscv-tests/rv32*.elf; do
    if timeout 5 $RISCVDIR/c_emulator/riscv_sim_RV32 -p $test > ${test%.elf}.cout 2>&1 && grep -q SUCCESS ${test%.elf}.cout
    then
	green "C-32 $(basename $test)" "ok"
    else
	red "C-32 $(basename $test)" "fail"
    fi
done
finish_suite "32-bit RISCV C tests"

# Do 'make clean' to avoid cross-arch pollution.
make clean

printf "Building 64-bit RISCV specification...\n"

if make ocaml_emulator/riscv_ocaml_sim_RV64 ;
then
    green "Building 64-bit RISCV OCaml emulator" "ok"
else
    red "Building 64-bit RISCV OCaml emulator" "fail"
fi
for test in $DIR/riscv-tests/rv64*.elf; do
    # skip F/D tests on OCaml for now
    pat='rv64ud-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    pat='rv64uf-.+elf'
    if [[ $(basename $test) =~ $pat ]];
    then continue
    fi
    if $RISCVDIR/ocaml_emulator/riscv_ocaml_sim_RV64 "$test" >"${test/.elf/.out}" 2>&1 && grep -q SUCCESS "${test/.elf/.out}"
    then
       green "OCaml-64 $(basename $test)" "ok"
    else
       red "OCaml-64 $(basename $test)" "fail"
    fi
done
finish_suite "64-bit RISCV OCaml tests"

if make c_emulator/riscv_sim_RV64;
then
    green "Building 64-bit RISCV C emulator" "ok"
else
    red "Building 64-bit RISCV C emulator" "fail"
fi
for test in $DIR/riscv-tests/rv64*.elf; do
    if timeout 5 $RISCVDIR/c_emulator/riscv_sim_RV64 -p $test > ${test%.elf}.cout 2>&1 && grep -q SUCCESS ${test%.elf}.cout
    then
	green "C-64 $(basename $test)" "ok"
    else
	red "C-64 $(basename $test)" "fail"
    fi
done
finish_suite "64-bit RISCV C tests"

# Do 'make clean' to avoid cross-arch pollution.
make clean

if ARCH=RV32 make c_emulator/riscv_rvfi_RV32;
then
    green "Building 32-bit RISCV RVFI C emulator" "ok"
else
    red "Building 32-bit RISCV RVFI C emulator" "fail"
fi
finish_suite "32-bit RISCV RVFI C tests"

# Do 'make clean' to avoid cross-arch pollution.
make clean

if ARCH=RV64 make c_emulator/riscv_rvfi_RV64;
then
    green "Building 64-bit RISCV RVFI C emulator" "ok"
else
    red "Building 64-bit RISCV RVFI C emulator" "fail"
fi
finish_suite "64-bit RISCV RVFI C tests"

printf "Passed ${all_pass} out of $(( all_pass + all_fail ))\n\n"
XML="<testsuites tests=\"$(( all_pass + all_fail ))\" failures=\"${all_fail}\">\n$SUITES_XML</testsuites>\n"
printf "$XML" > $DIR/tests.xml

if [ $all_fail -gt 0 ]
then
    exit 1
fi
