#!/bin/csh

# Test all defined clock setups scripts with all configurations. This might take some time!

#rm -r ./synthesis_results;

python3 ./ri5cly-manage.py --setup_script ./synopsys_setup_scripts/setup_10.tcl;
python3 ./ri5cly-manage.py --synthesize_all;

python3 ./ri5cly-manage.py --setup_script ./synopsys_setup_scripts/setup_5.tcl;
python3 ./ri5cly-manage.py --synthesize_all;

python3 ./ri5cly-manage.py --setup_script ./synopsys_setup_scripts/setup_3.tcl;
python3 ./ri5cly-manage.py --synthesize_all;

python3 ./ri5cly-manage.py --report_all;


