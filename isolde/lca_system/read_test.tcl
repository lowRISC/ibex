reset halt 
# test.tcl - OpenOCD Tcl script to write and verify memory contents
#riscv set_mem_access progbuf
riscv set_mem_access sysbus

reset halt 
set width 32

# Define addresses and expected values
set tests {
    {0x00100000 {0x0badc0de 0xdeadbeaf}}
    {0x00110000 {0x12345678 0xabcdef01}}
    {0x00140000 {0xa5a5a5a5 0x5a5a5a5a}}
}

set overall_match 1

foreach test $tests {
    set addr [lindex $test 0]
    set expected_values [lindex $test 1]

    puts "---------------------------------------------"
    puts "Writing memory at $addr..."
    write_memory $addr $width $expected_values phys

    puts "Reading memory at $addr..."
    set read_values [read_memory $addr $width [llength $expected_values] phys]

    puts "Verifying memory contents at $addr..."
    set match 1
    for {set i 0} {$i < [llength $expected_values]} {incr i} {
        set expected [lindex $expected_values $i]
        set actual [lindex $read_values $i]
        if {$expected != $actual} {
            puts "ERROR: Mismatch at $addr word $i: expected $expected, got $actual"
            set match 0
        }
    }

    if {$match} {
        puts "SUCCESS: Memory at $addr matches expected values."
    } else {
        puts "FAILURE: Memory verification failed at $addr."
        set overall_match 0
    }
}

puts "============================================="
if {$overall_match} {
    puts "ALL TESTS PASSED."
} else {
    puts "ONE OR MORE TESTS FAILED."
}

shutdown
