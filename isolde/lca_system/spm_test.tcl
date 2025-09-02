reset halt
# test.tcl - OpenOCD Tcl script to write and verify memory contents
# riscv set_mem_access progbuf
riscv set_mem_access sysbus

reset halt
set width 32

# Base address for testing
set base_addr 0x80001000

# Define addresses and expected values
set test_data {
    0xDEADBEEF
    0xCAFEF00D
    0xCAFEDEEA
    0x12345678
    0x15678
    0x26789
    0x3789A
    0x489AB
    0x59ABC
}
proc run_mem_test {access_mode base_addr width test_data} {
    puts "============================================="
    puts "Running memory test with access mode: $access_mode"
    riscv set_mem_access $access_mode

    reset halt
    set overall_match 1
    set addr $base_addr

    foreach value $test_data {
        puts "---------------------------------------------"
        puts "Writing memory at [format 0x%08X $addr] with value $value..."
        write_memory $addr $width $value phys

        puts "Reading memory at [format 0x%08X $addr]..."
        set read_values [read_memory $addr $width 1 phys]

        puts "Verifying memory contents at [format 0x%08X $addr]..."
        set actual [lindex $read_values 0]
        if {$value != $actual} {
            puts "ERROR: Mismatch at [format 0x%08X $addr]: expected $value, got $actual"
            set overall_match 0
        } else {
            puts "SUCCESS: Memory at [format 0x%08X $addr] matches expected value."
        }

        # Increment address by word size (bytes)
        set addr [expr {$addr + ($width / 8)}]
    }

    if {$overall_match} {
        puts "ALL TESTS PASSED for $access_mode."
    } else {
        puts "ONE OR MORE TESTS FAILED for $access_mode."
    }
    return $overall_match
}

# Run both tests
set result_sysbus   [run_mem_test sysbus   $base_addr $width $test_data]
set result_progbuf  [run_mem_test progbuf  $base_addr $width $test_data]

puts "============================================="
if {$result_sysbus && $result_progbuf} {
    puts "ALL TESTS PASSED (sysbus + progbuf)."
} else {
    puts "ONE OR MORE TESTS FAILED (sysbus and/or progbuf)."
}

shutdown
