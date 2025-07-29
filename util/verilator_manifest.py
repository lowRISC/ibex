#!/usr/bin/env python3

import sys
import yaml
import argparse
from pathlib import Path

def parse_args():
    parser = argparse.ArgumentParser(description="Extract Verilator C++ sources from Bender.yml.")
    parser.add_argument("bender_file", type=Path, help="Path to Bender.yml")
    parser.add_argument("-t", "--target", required=True, help="Target name in cpp_sources")
    parser.add_argument("-o", "--output", type=Path, required=True, help="File to append output to")
    return parser.parse_args()

def get_cpp_sources(bender_yaml_path, target):
    with open(bender_yaml_path, "r") as f:
        bender_data = yaml.safe_load(f)

    cpp_sources = bender_data.get("sources", {})
    return cpp_sources.get(target, [])

def main():
    args = parse_args()
    bender_file = args.bender_file.resolve()
    target = args.target
    output_file = args.output.resolve()
    bender_dir = bender_file.parent

    cpp_files = get_cpp_sources(bender_file, target)

    with open(output_file, "a") as f:
        for rel_path in cpp_files:
            abs_path = (bender_dir / rel_path).resolve()
            f.write(f"{abs_path}\n")

if __name__ == "__main__":
    main()
