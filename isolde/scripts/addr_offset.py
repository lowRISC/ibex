import sys

def process_hex_file(input_file, output_file, offset):
    with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
        for line in infile:
            if line.startswith('@'):
                # Extract the address and convert to an integer
                address = int(line[1:].strip(), 16)
                # Subtract the offset
                new_address = address - offset
                # Write the modified address back in hex format, with '@' prefix
                outfile.write(f"@{new_address:08X}\n")
            else:
                # Write data lines without modification
                outfile.write(line)

if __name__ == "__main__":
    # Check if the correct number of arguments are provided
    if len(sys.argv) != 4:
        print("Usage: python addr_offset.py <input_file> <output_file> <offset>")
        sys.exit(1)

    # Get arguments from command line
    input_file = sys.argv[1]
    output_file = sys.argv[2]
    try:
        offset = int(sys.argv[3], 16)  # Parse the offset as a hex value
    except ValueError:
        print(f"Invalid offset: {sys.argv[3]}. Please provide a valid hex number (e.g., 0x00100000).")
        sys.exit(1)

    # Run the function to process the file
    process_hex_file(input_file, output_file, offset)

    print(f"Processed hex file saved as {output_file}.")
