reset halt 
# Specify which RISC-V memory access method(s) shall be used, ie sysbus - Access memory via RISC-V Debug System Bus interface. 
riscv set_mem_access sysbus
# Define the address and values
set addr 0x100080
set width 32
set expected_values {0x0badc0de 0xdeadbeaf}

# Write the expected values to memory
puts "Writing memory at $addr..."
write_memory $addr $width $expected_values phys

# Read back the values
puts "Reading memory at $addr..."
set read_values [read_memory $addr $width [llength $expected_values] phys]

# Compare the read values with expected values
puts "Verifying memory contents..."
set match 1
for {set i 0} {$i < [llength $expected_values]} {incr i} {
    set expected [lindex $expected_values $i]
    set actual [lindex $read_values $i]
    if {$expected != $actual} {
        puts "ERROR: Mismatch at word $i: expected $expected, got $actual"
        set match 0
    }
}

if {$match} {
    puts "SUCCESS: Memory contents match expected values."
} else {
    puts "FAILURE: Memory verification failed."
}

#shutdown


reset halt 
# Specify which RISC-V memory access method(s) shall be used, ie sysbus - Access memory via RISC-V Debug System Bus interface. 
riscv set_mem_access sysbus
#dump_image imem.bin  0x100000 100
load_image instr.hex  
reg pc 0x00100080
resume
shutdown

