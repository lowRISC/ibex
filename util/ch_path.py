#!/usr/bin/env python3

import os

# Read from environment variables
fusesoc_build_root = os.environ.get("FUSESOC_BUILD_ROOT")
root_dir = os.environ.get("ROOT_DIR")

# Validate environment variables
if not fusesoc_build_root or not root_dir:
    raise EnvironmentError("FUSESOC_BUILD_ROOT or ROOT_DIR is not set in environment.")

# Define replacement base paths
relative_prefix = "../../../../../"
generated_prefix = "generated/"
incdir_prefix = "+incdir+"

base_path = os.path.join(root_dir, "")
generated_path = os.path.join(fusesoc_build_root, "sim-vcs/generated/")

# Construct file paths
input_file = os.path.join(fusesoc_build_root, "sim-vcs/isolde_ibex_lca_dm_system_0.scr")
output_file = os.path.join(root_dir, "isolde/lca_system/ibex_fusesoc.flist")

def replace_paths_in_file(input_path, output_path):
    with open(input_path, 'r') as infile, open(output_path, 'w') as outfile:
        for line in infile:
            original_line = line.rstrip()  # Remove only trailing newline

            # Handle +incdir+ lines
            if original_line.startswith(incdir_prefix):
                path_part = original_line[len(incdir_prefix):]
                if path_part.startswith(relative_prefix):
                    path_part = path_part.replace(relative_prefix, base_path)
                elif path_part.startswith(generated_prefix):
                    path_part = path_part.replace(generated_prefix, generated_path)
                original_line = incdir_prefix + path_part

            # Handle normal relative paths
            elif original_line.startswith(relative_prefix):
                original_line = original_line.replace(relative_prefix, base_path)

            # Handle generated paths
            elif original_line.startswith(generated_prefix):
                original_line = original_line.replace(generated_prefix, generated_path)

            outfile.write(original_line + '\n')

    print(f"✅ Finished. Output written to: {output_file}")

# Run the function
replace_paths_in_file(input_file, output_file)

