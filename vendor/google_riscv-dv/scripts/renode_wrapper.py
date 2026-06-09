#!/usr/bin/env python3
import argparse
import subprocess
import os
import tempfile

# =============================================================================

REPL_TEMPLATE = """
memory: Memory.MappedMemory @ sysbus 0x80000000
    size: {mem}

cpu: CPU.{cpu_type} @ sysbus
    cpuType: "{isa}"
    timeProvider: clint
    hartId: 0
    {priv_levels}
    {additional_cpu_parameters}

clint: IRQControllers.CoreLevelInterruptor  @ sysbus 0x02000000
    [0,1] -> cpu@[3,7]
    frequency: 1000000
"""

RESC_TEMPLATE = """
using sysbus
mach create "riscv"
machine LoadPlatformDescription @{repl}

sysbus LoadELF @{elf}

cpu MaximumBlockSize 1
cpu SetHookAtBlockEnd "print('REGDUMP:' + ','.join(self.GetRegistersValues()))"
cpu InstallCustomInstructionHandlerFromString "00000000000000000000000001110011" "print('ECALL:');"

emulation RunFor "0.001"

quit
"""

# =============================================================================


def main():
    """
    The entry point
    """

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--renode",
        type=str,
        default="renode",
        help="Path to Renode binary",
    )
    parser.add_argument(
        "--log",
        type=str,
        default=None,
        help="Output log file",
    )
    parser.add_argument(
        "--isa",
        type=str,
        default="rv32i",
        help="RISC-V ISA specification string",
    )
    parser.add_argument(
        "--elf",
        type=str,
        required=True,
        help="ELF file to run",
    )
    parser.add_argument(
        "--mem-size",
        type=str,
        default="0x100000",
        help="Memory size",
    )
    parser.add_argument(
        "--cpu-type",
        type=str,
        default="Riscv32",
        help="Renode CPU type",
    )
    parser.add_argument(
        "--priv",
        type=str,
        default="",
        help="Supported privilege levels",
    )
    # Some CPUs might not expose these parameters as configurable
    # allow the testing software to ignore/override them if needed
    parser.add_argument(
        "--additional-cpu-parameters",
        type=str,
        default="allowUnalignedAccesses: true",
        help="Additional CPU parameters",
    )

    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as tmpdir:

        repl = os.path.join(tmpdir, "riscv.repl")
        resc = os.path.join(tmpdir, "riscv.resc")

        priv_levels = ""
        if args.priv:
            priv_levels += "privilegeLevels: PrivilegeLevels."
            if "m" in args.priv:
                priv_levels += "Machine"
            if "s" in args.priv:
                priv_levels += "Supervisor"
            if "u" in args.priv:
                priv_levels += "User"

        params = {
            "renode": args.renode,
            "isa":  args.isa,
            "elf":  args.elf,
            "repl": repl,
            "resc": resc,
            "log":  args.log,
            "mem":  args.mem_size,
            "cpu_type": args.cpu_type,
            "priv_levels": priv_levels,
            "additional_cpu_parameters": args.additional_cpu_parameters,
        }

        # Render REPL template
        with open(repl, "w") as fp:
            fp.write(REPL_TEMPLATE.format(**params))

        # Render RESC template
        with open(resc, "w") as fp:
            fp.write(RESC_TEMPLATE.format(**params))

        # Launch Renode, capture output
        cmd = "{renode} --console -p {resc}".format(**params)
        if args.log is not None:
            cmd += " &>{log}".format(**params)

        subprocess.call(cmd, shell=True)


if __name__ == "__main__":
    main()
