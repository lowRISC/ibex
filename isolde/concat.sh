#!/bin/bash

# Create an associative array to store paths of CSV files by their filename
declare -A csv_files

# Find all CSV files in subdirectories
while IFS= read -r file; do
    filename=$(basename "$file")
    csv_files[$filename]+="$file "
done < <(find . -type f -name "*.csv")

# Concatenate files with the same name
for filename in "${!csv_files[@]}"; do
    output_file="./$filename"
    echo "Processing: $filename"
    
    # Get the first file and extract its header
    first_file=$(echo ${csv_files[$filename]} | awk '{print $1}')
    head -n 1 "$first_file" > "$output_file"
    
    # Concatenate all files with the same name, skipping headers
    for file in ${csv_files[$filename]}; do
        tail -n +2 "$file" >> "$output_file"
    done
    echo "Merged: $filename -> $output_file"
done

echo "All CSV files with the same name have been concatenated."