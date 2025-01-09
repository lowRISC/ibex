 #!/bin/bash

if [[ "$1" == "verilate" ]]; then
    make veri-clean verilate
fi

make TEST=vlinstr_test test-clean test-build veri-run
