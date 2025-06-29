import sys
import os

def parse_hex_file(input_file):
    memory = {}
    current_addr = None

    with open(input_file, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith('@'):
                current_addr = int(line[1:], 16)
            else:
                bytes_str = line.split()
                for byte_str in bytes_str:
                    memory[current_addr] = int(byte_str, 16)
                    current_addr += 1
    return memory

def write_bin(memory, start_addr, length, output_file):
    with open(output_file, 'wb') as f:
        for addr in range(start_addr, start_addr + length):
            byte = memory.get(addr, 0)
            f.write(bytes([byte]))

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python hex2bin_split.py input.hex instr.bin data.bin")
        sys.exit(1)

    input_hex = sys.argv[1]
    instr_bin = sys.argv[2]
    data_bin = sys.argv[3]

    # Define memory regions (change if you modify the linker script)
    instr_base = 0x00100000
    instr_size = 0x8000
    data_base  = 0x00110000
    data_size  = 0x30000

    mem = parse_hex_file(input_hex)

    write_bin(mem, instr_base, instr_size, instr_bin)
    write_bin(mem, data_base, data_size, data_bin)

    print(f"Generated: {instr_bin} and {data_bin}")
