set NUM_CORES 16;
set CLOCK_SLOW 10;  # 100 MHz
set DESIGN_NAME imperio_${CLOCK_SLOW}

set USE_CORNER     "SLOW"   ;# "SLOW | NOMINAL"
set USE_CORE       "LITTLE_RISCV"  ;# "RISCV | OR10N | LITTLE_RISCV"
set RI5CY_LATCH_RF "TRUE"   ;# "TRUE | FALSE"
set UNGROUP_CORE   "FALSE"  ;# "TRUE | FALSE"

set ASIC_PATH  ../rtl
set RTL_PATH   ../pulpino/rtl
set IPS_PATH   ../pulpino/ips

set search_path [ join "$IPS_PATH/axi/wb2axi
                        $IPS_PATH/axi/per2axi
                        $IPS_PATH/axi/axi2per
                        $IPS_PATH/axi/axi2mem
                        $IPS_PATH/axi/axi_node
                        $IPS_PATH/apb/apb_i2c
                        $IPS_PATH/apb/apb_event_unit/include
                        $RTL_PATH/includes
                        $search_path"
                ]

set RISCV_PATH                  $IPS_PATH/riscv
set OR10N_PATH                  $IPS_PATH/or10n
set LITTLE_RISCV_PATH		$IPS_PATH/little-riscv
set AXI_PATH                    $IPS_PATH/axi
set SCM_PATH                    $IPS_PATH/scm
set APB_PATH                    $IPS_PATH/apb
set PULPINO_PATH                $RTL_PATH
set ADV_DEBUG_IF_PATH           $IPS_PATH/adv_dbg_if/rtl

# supress port can become inout port (for interfaces crossing hierarchy)
suppress_message {VER-735}

# suppress 'assert property not supported'
suppress_message {VER-708}
