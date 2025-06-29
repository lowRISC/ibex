import argparse
from intelhex import IntelHex

def parse_raw_hex_file(filename):
    ih = IntelHex()
    with open(filename, "r") as f:
        current_addr = None
        for line in f:
            line = line.strip()
            if line.startswith("@"):
                current_addr = int(line[1:], 16)
            elif current_addr is not None:
                bytes_str = line.strip().split()
                for byte_str in bytes_str:
                    ih[current_addr] = int(byte_str, 16)
                    current_addr += 1
    return ih

def parse_args():
    parser = argparse.ArgumentParser(description="Split Intel HEX file by address range.")
    parser.add_argument("--input", required=True, help="Input Intel HEX file")

    parser.add_argument("--instr-base", type=lambda x: int(x, 0), required=True, help="Instruction base address (e.g., 0x00100000)")
    parser.add_argument("--instr-size", type=lambda x: int(x, 0), required=True, help="Instruction memory size (e.g., 0x8000)")
    parser.add_argument("--instr-out", default="instr.hex", help="Output file for instruction memory region")

    parser.add_argument("--data-base", type=lambda x: int(x, 0), required=True, help="Data base address (e.g., 0x00110000)")
    parser.add_argument("--data-size", type=lambda x: int(x, 0), required=True, help="Data memory size (e.g., 0x30000)")
    parser.add_argument("--data-out", default="data.hex", help="Output file for data memory region")

    parser.add_argument("--verbose", action="store_true", help="Print matched address ranges and stats")

    return parser.parse_args()


def main():
    args = parse_args()

    instr_base = args.instr_base
    instr_end = instr_base + args.instr_size
    data_base = args.data_base
    data_end = data_base + args.data_size

    ih = parse_raw_hex_file(args.input)
    instr_hex = IntelHex()
    data_hex = IntelHex()

    instr_count = 0
    data_count = 0
    skipped = 0

    for addr in ih.addresses():
        byte = ih[addr]
        if instr_base <= addr < instr_end:
            instr_hex[addr] = byte
            instr_count += 1
        elif data_base <= addr < data_end:
            data_hex[addr] = byte
            data_count += 1
        else:
            skipped += 1
            continue

    instr_hex.write_hex_file(args.instr_out)
    data_hex.write_hex_file(args.data_out)

    print("✅ Split complete.")
    print(f"📦 Instruction region: {instr_count} bytes → {args.instr_out}")
    print(f"📦 Data region       : {data_count} bytes → {args.data_out}")
    print(f"🚫 Skipped outside   : {skipped} bytes")

    if args.verbose:
        print(f"\nAddress ranges:")
        print(f"  Instr: 0x{instr_base:08X} - 0x{instr_end - 1:08X}")
        print(f"  Data : 0x{data_base:08X} - 0x{data_end - 1:08X}")


if __name__ == "__main__":
    main()
