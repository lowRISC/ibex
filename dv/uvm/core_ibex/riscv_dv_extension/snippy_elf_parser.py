#!/usr/bin/env python3
"""
Convert ELF PT_LOAD segments into manifests.

The script can generate:
1. a JSON manifest for debugging;
2. a simple SystemVerilog-friendly text manifest for UVM loading.

Requires pyelftools.

Examples:
    python3 snippy_elf_parser.py test.elf --json-out test.json
    python3 snippy_elf_parser.py test.elf --sv-out test.svload
    python3 snippy_elf_parser.py test.elf --json-out test.json --sv-out test.svload
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from elftools.elf.elffile import ELFFile


def flags_to_string(p_flags: int) -> str:
    chars = [
        "R" if (p_flags & 0x4) else "-",
        "W" if (p_flags & 0x2) else "-",
        "X" if (p_flags & 0x1) else "-",
    ]
    return "".join(chars)


def choose_load_addr(segment: Any, prefer_paddr: bool = True) -> int:
    p_paddr = int(segment["p_paddr"])
    p_vaddr = int(segment["p_vaddr"])
    if prefer_paddr and p_paddr != 0:
        return p_paddr
    return p_vaddr


def section_in_segment(section: Any, segment: Any) -> bool:
    sec_size = int(section["sh_size"])
    sec_addr = int(section["sh_addr"])

    if sec_size == 0:
        return False

    seg_addr = int(segment["p_vaddr"])
    seg_memsz = int(segment["p_memsz"])

    if seg_memsz == 0:
        return False

    seg_end = seg_addr + seg_memsz
    sec_end = sec_addr + sec_size

    return sec_addr >= seg_addr and sec_end <= seg_end


def collect_section_names(elf: ELFFile, segment: Any) -> list[str]:
    names: list[str] = []
    for section in elf.iter_sections():
        flags = int(section["sh_flags"])
        shf_alloc = 0x2  # SHF_ALLOC
        if not (flags & shf_alloc):
            continue
        if section_in_segment(section, segment):
            names.append(section.name)
    return names


def parse_elf(elf_path: Path, prefer_paddr: bool = True) -> dict[str, Any]:
    with elf_path.open("rb") as f:
        elf = ELFFile(f)

        manifest: dict[str, Any] = {
            "format_version": 1,
            "elf_path": str(elf_path),
            "elf_class": elf.elfclass,
            "little_endian": elf.little_endian,
            "machine": elf["e_machine"],
            "entry": int(elf.header["e_entry"]),
            "segments": [],
        }

        for idx, segment in enumerate(elf.iter_segments()):
            if segment["p_type"] != "PT_LOAD":
                continue

            file_size = int(segment["p_filesz"])
            mem_size = int(segment["p_memsz"])
            load_addr = choose_load_addr(segment, prefer_paddr=prefer_paddr)
            data = segment.data()

            if len(data) != file_size:
                raise ValueError(
                    f"Segment {idx}: segment.data() length {len(data)} != p_filesz {file_size}"
                )
            if mem_size < file_size:
                raise ValueError(
                    f"Segment {idx}: invalid ELF, p_memsz ({mem_size}) < p_filesz ({file_size})"
                )

            seg_info = {
                "index": idx,
                "load_addr": load_addr,
                "vaddr": int(segment["p_vaddr"]),
                "paddr": int(segment["p_paddr"]),
                "offset": int(segment["p_offset"]),
                "file_size": file_size,
                "mem_size": mem_size,
                "zero_fill": mem_size - file_size,
                "align": int(segment["p_align"]),
                "flags": flags_to_string(int(segment["p_flags"])),
                "section_names": collect_section_names(elf, segment),
                "data_hex": data.hex(),
            }
            manifest["segments"].append(seg_info)

        return manifest


def print_summary(manifest: dict[str, Any]) -> None:
    print(f"ELF file      : {manifest['elf_path']}")
    print(f"Machine       : {manifest['machine']}")
    print(f"ELF class     : ELF{manifest['elf_class']}")
    print(f"Little endian : {manifest['little_endian']}")
    print(f"Entry point   : 0x{manifest['entry']:08x}")
    print()

    segments = manifest["segments"]
    if not segments:
        print("No PT_LOAD segments found.")
        return

    print("Loadable segments:")
    for seg in segments:
        print(f"  Segment #{seg['index']}")
        print(f"    load_addr    : 0x{seg['load_addr']:08x}")
        print(f"    vaddr        : 0x{seg['vaddr']:08x}")
        print(f"    paddr        : 0x{seg['paddr']:08x}")
        print(f"    offset       : 0x{seg['offset']:08x}")
        print(f"    file_size    : {seg['file_size']}")
        print(f"    mem_size     : {seg['mem_size']}")
        print(f"    zero_fill    : {seg['zero_fill']}")
        print(f"    flags        : {seg['flags']}")
        print(f"    align        : {seg['align']}")
        print(f"    sections     : {', '.join(seg['section_names']) if seg['section_names'] else '-'}")

        preview_len = min(16, seg["file_size"])
        preview_hex = seg["data_hex"][: preview_len * 2]
        print(f"    data preview : {preview_hex}")
        print()


def write_json_manifest(manifest: dict[str, Any], out_path: Path) -> None:
    out_path.write_text(json.dumps(manifest, indent=2))
    print(f"JSON manifest written to: {out_path}")


def write_sv_manifest(manifest: dict[str, Any], out_path: Path) -> None:
    """
    Write a line-oriented manifest for the SystemVerilog loader.

    Format:
        ENTRY,0x80000000
        SEGMENT,<load_addr>,<file_size>,<mem_size>,<flags>
        SECTION,<name>
        BYTE,0xNN
        BYTE,0xNN
        ...
        ZERO,0x00000010

    Semantics:
    - SEGMENT starts a new loadable segment.
    - SECTION records section names for debug messages.
    - BYTE lines are written sequentially from the current segment load address.
    - ZERO appends N zero bytes after the file-backed segment data.
    """
    with out_path.open("w", encoding="utf-8") as f:
        f.write(f"ENTRY,0x{manifest['entry']:08x}\n")

        for seg in manifest["segments"]:
            f.write(
                f"SEGMENT,0x{seg['load_addr']:08x},"
                f"0x{seg['file_size']:08x},"
                f"0x{seg['mem_size']:08x},"
                f"{seg['flags']}\n"
            )

            for sec_name in seg["section_names"]:
                f.write(f"SECTION,{sec_name}\n")

            data_hex = seg["data_hex"]
            for i in range(0, len(data_hex), 2):
                byte_hex = data_hex[i:i + 2]
                f.write(f"BYTE,0x{byte_hex}\n")

            if seg["zero_fill"] > 0:
                f.write(f"ZERO,0x{seg['zero_fill']:08x}\n")

    print(f"SV manifest written to: {out_path}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Convert ELF PT_LOAD segments into JSON and/or SV-friendly manifest"
    )
    parser.add_argument("elf", type=Path, help="Input ELF file")
    parser.add_argument("--json-out", type=Path, default=None, help="Output JSON manifest path")
    parser.add_argument("--sv-out", type=Path, default=None, help="Output SV text manifest path")
    parser.add_argument(
        "--prefer-vaddr",
        action="store_true",
        help="Use p_vaddr for load_addr even if p_paddr is non-zero",
    )
    args = parser.parse_args()

    if not args.elf.is_file():
        print(f"Error: ELF file not found: {args.elf}", file=sys.stderr)
        return 2

    if args.json_out is None and args.sv_out is None:
        print("Error: specify at least one of --json-out or --sv-out", file=sys.stderr)
        return 2

    try:
        manifest = parse_elf(args.elf, prefer_paddr=not args.prefer_vaddr)
    except Exception as exc:
        print(f"Error while parsing ELF: {exc}", file=sys.stderr)
        return 1

    print_summary(manifest)

    if args.json_out is not None:
        write_json_manifest(manifest, args.json_out)

    if args.sv_out is not None:
        write_sv_manifest(manifest, args.sv_out)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
