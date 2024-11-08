import os
import argparse

# Set up command-line argument parsing
parser = argparse.ArgumentParser(description='Transform relative paths to absolute paths in a specified file.')
parser.add_argument('base_dir', type=str, help='The base directory to resolve relative paths against.')
parser.add_argument('input_file', type=str, help='The input file containing the paths.')
parser.add_argument('output_file', type=str, help='The output file to write modified paths.')

args = parser.parse_args()

# Get the absolute path of the base directory provided by the user
base_dir = os.path.abspath(args.base_dir)

# Read the input file and filter out the unwanted lines
with open(args.input_file, 'r') as file:
    lines = file.readlines()

# Write the filtered lines to the output file
with open(args.output_file, 'w') as file:
    for line in lines:
        line = line.strip()
        if line.startswith('--top-module'):
            print(f"INFO: top module {line[len('--top-module'):].strip()}")
            file.write(line + '\n')  # Write the unmodified line to the output file
        if line.startswith('+incdir+'):
            # Remove +incdir+ from the beginning of the line
            relative_path = line[len('+incdir+'):].strip()  # Get the remaining path
            # Convert to an absolute path based on the base_dir
            absolute_path = os.path.abspath(os.path.join(base_dir, relative_path))
            # Write the new line with +incdir+ and the absolute path
            file.write(f"+incdir+{absolute_path}\n")
            file.write(f"-CFLAGS -I{absolute_path}\n")
            continue
        # Skip lines that start with '--' 
        if line.startswith('--')  or line.startswith('-CFLAGS'):
            continue
        if line.startswith('-'):
            file.write(line + '\n')  # Write the  unmodified line to the output file
            continue
        # Check if the line starts with a relative path (not starting with '/' or not empty)
        if line and not line.startswith('/'):
            # Convert relative paths to absolute paths
            line = os.path.abspath(os.path.join(base_dir, line))
        
        file.write(line + '\n')  # Write the modified or unmodified line to the output file

print(f"Filtered and modified content written to {args.output_file}.")
