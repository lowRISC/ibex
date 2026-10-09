ida_database -open -name xlm_testrig_out/waves.db
ida_probe -log -wave -wave_probe_args="core_ibex_testrig_tb_top -all -depth all -memories"
run
