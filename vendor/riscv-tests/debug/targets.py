import importlib
import os.path
import re
import sys
import tempfile

import testlib

class Hart:
    # XLEN of the hart. May be overridden with --32 or --64 command line
    # options.
    xlen = 0

    # Will be autodetected (by running ExamineTarget) if left unset. Set to
    # save a little time.
    misa = None

    # Path to linker script relative to the .py file where the target is
    # defined. Defaults to <name>.lds.
    link_script_path = None

    # Implements dmode in tdata1 as described in the spec. Harts that need
    # this value set to False are not compliant with the spec (but still usable
    # as long as running code doesn't try to mess with triggers set by an
    # external debugger).
    honors_tdata1_hmode = True

    # Address where a r/w/x block of RAM starts, together with its size.
    ram = None
    ram_size = None

    # Address where we expect memory accesses to fail, usually because there is
    # no device mapped to that location.
    bad_address = None

    # Number of instruction triggers the hart supports.
    instruction_hardware_breakpoint_count = 0

    # Defaults to target-<index>
    name = None

    # When reset, the PC must be at one of the values listed here.
    # This is a list because on some boards the reset vector depends on
    # jumpers.
    reset_vectors = []

    # system is set to an identifier of the system this hart belongs to.  Harts
    # within the same system are assumed to share memory, and to have unique
    # hartids within that system.  So for most cases the default value of None
    # is fine.
    system = None

    # Supports the cease instruction, which causes a hart to become unavailable.
    support_cease = False

    def __init__(self, misa=None, system=None, link_script_path=None):
        if misa:
            self.misa = misa
        if system:
            self.system = system
        if link_script_path:
            self.link_script_path = link_script_path

    def extensionSupported(self, letter):
        # target.misa is set by testlib.ExamineTarget
        if self.misa:
            return self.misa & (1 << (ord(letter.upper()) - ord('A')))
        return False

class Target:
    # pylint: disable=too-many-instance-attributes

    # List of Hart object instances, one for each hart in the target.
    harts = []

    # Name of the target. Defaults to the name of the class.
    name = None

    # GDB remotetimeout setting.
    timeout_sec = 2

    # Timeout waiting for the server to start up. This is different than the
    # GDB timeout, which is how long GDB waits for commands to execute.
    # The server_timeout is how long this script waits for the server to be
    # ready for GDB connections.
    server_timeout_sec = 60

    # Path to OpenOCD configuration file relative to the .py file where the
    # target is defined. Defaults to <name>.cfg.
    openocd_config_path = None

    # List of commands that should be executed in gdb after connecting but
    # before starting the test.
    gdb_setup = []

    # Supports mtime at 0x2004000
    supports_clint_mtime = True

    # Implements custom debug registers like spike does. It seems unlikely any
    # hardware will every do that.
    implements_custom_test = False

    # When true it indicates that reading invalid memory doesn't return an error
    invalid_memory_returns_zero = False

    # Supports simultaneous resume through hasel.
    support_hasel = True

    # Tests whose names are mentioned in this list will be skipped and marked
    # as not applicable. This is a crude mechanism that can be handy, but in
    # general it's better to define some property like those above that
    # describe behavior of this target, and tests can use that to decide
    # whether they are applicable or not.
    skip_tests = []

    # Set False if semihosting should not be tested in this configuration,
    # because it doesn't work and isn't expected to work.
    test_semihosting = True

    # Set False if manual hwbps (breakpoints set by directly writing tdata*)
    # isn't supposed to work.
    support_manual_hwbp = True

    # Set False if memory sampling is not supported due to OpenOCD
    # limitation/hardware support.
    support_memory_sampling = True

    # Relative path to a FreeRTOS binary compiled from the spike demo project
    # in https://github.com/FreeRTOS/FreeRTOS.
    freertos_binary = None

    # Internal variables:
    directory = None
    temporary_files = []

    def __init__(self, path, parsed):
        # Path to module.
        self.path = path
        self.directory = os.path.dirname(path)
        self.server_cmd = parsed.server_cmd
        self.sim_cmd = parsed.sim_cmd
        self.debug_server = parsed.debug_server
        self.temporary_binary = None
        self.compiler_supports_v = True
        Target.isolate = parsed.isolate
        if not self.name:
            self.name = type(self).__name__
        # Default OpenOCD config file to <name>.cfg
        if not self.openocd_config_path:
            self.openocd_config_path = f"{self.name}.cfg"
        self.openocd_config_path = os.path.join(self.directory,
                self.openocd_config_path)
        for i, hart in enumerate(self.harts):
            hart.index = i
            if not hasattr(hart, 'id'):
                hart.id = i
            if not hart.name:
                hart.name = f"{self.name}-{i}"
            # Default link script to <name>.lds
            if not hart.link_script_path:
                hart.link_script_path = f"{self.name}.lds"
            hart.link_script_path = os.path.join(self.directory,
                    hart.link_script_path)

    def create(self):
        """Create the target out of thin air, eg. start a simulator."""

    def server(self, test):
        """Start the debug server that gdb connects to, eg. OpenOCD."""
        return testlib.Openocd(server_cmd=self.server_cmd,
                config=self.openocd_config_path,
                timeout=self.server_timeout_sec,
                freertos=test.freertos(),
                debug_openocd=self.debug_server)

    def do_compile(self, hart, *sources):
        binary_name = (
                self.name + "_" +
                os.path.basename(os.path.splitext(sources[0])[0]) + "-" +
                f"{hart.misa:x}")
        if Target.isolate:
            # pylint: disable-next=consider-using-with
            self.temporary_binary = tempfile.NamedTemporaryFile(
                    prefix=binary_name + "_")
            binary_name = self.temporary_binary.name
            Target.temporary_files.append(self.temporary_binary)

        args = list(sources) + [
                "programs/entry.S", "programs/init.c",
                f"-DNHARTS={len(self.harts)}",
                "-I", "../env",
                "-T", hart.link_script_path,
                "-nostartfiles",
                "-mcmodel=medany",
                f"-DXLEN={hart.xlen}",
                "-o", binary_name]

        if hart.extensionSupported('e'):
            args.append("-march=rv32e")
            args.append("-mabi=ilp32e")
            args.append("-DRV32E")
        else:
            march = f"rv{hart.xlen}ima"
            for letter in "fdc":
                if hart.extensionSupported(letter):
                    march += letter
            if hart.extensionSupported("v") and self.compiler_supports_v:
                march += "v"
            args.append(f"-march={march}")
            if hart.xlen == 32:
                args.append("-mabi=ilp32")
            else:
                args.append(f"-mabi=lp{hart.xlen}")

        testlib.compile(args)
        return binary_name

    def compile(self, hart, *sources):
        for _ in range(2):
            try:
                return self.do_compile(hart, *sources)
            except testlib.CompileError as e:
                # If the compiler doesn't support V, disable it from the
                # current configuration. Eventually all gcc branches will
                # support V, but we're not there yet.
                m = re.search(r"Error: cannot find default versions of the "
                        r"ISA extension `(\w)'", e.stderr.decode())
                if m and m.group(1) in "v":
                    extension = m.group(1)
                    print(f"Disabling extension {extension!r} because the "
                            "compiler doesn't support it.")
                    self.compiler_supports_v = False
                else:
                    raise
        return None

def add_target_options(parser):
    parser.add_argument("target", help=".py file that contains definition for "
            "the target to test with.")
    parser.add_argument("--sim_cmd",
            help="The command to use to start the actual target (e.g. "
            "simulation)", default="spike")
    parser.add_argument("--server_cmd",
            help="The command to use to start the debug server (e.g. OpenOCD)")
    parser.add_argument("--debug_server", action="store_true",
            help="Open gdb in a separate terminal on the debug server")

    xlen_group = parser.add_mutually_exclusive_group()
    xlen_group.add_argument("--32", action="store_const", const=32,
            dest="xlen", default=0, help="Force the target to be 32-bit.")
    xlen_group.add_argument("--64", action="store_const", const=64,
            dest="xlen", default=0, help="Force the target to be 64-bit.")

    parser.add_argument("--isolate", action="store_true",
            help="Try to run in such a way that multiple instances can run at "
            "the same time. This may make it harder to debug a failure if it "
            "does occur.")

def target(parsed):
    directory = os.path.dirname(parsed.target)
    filename = os.path.basename(parsed.target)
    module_name = os.path.splitext(filename)[0]

    sys.path.append(directory)
    module = importlib.import_module(module_name)
    found = []
    for name in dir(module):
        definition = getattr(module, name)
        if isinstance(definition, type) and issubclass(definition, Target):
            found.append(definition)
    assert len(found) == 1, (f"{parsed.target} does not define exactly one "
                             "subclass of targets.Target")

    t = found[0](parsed.target, parsed)
    assert t.harts, f"{t.name} doesn't have any harts defined!"
    if parsed.xlen > 0:
        for h in t.harts:
            if h.xlen == 0:
                h.xlen = parsed.xlen
            elif h.xlen != parsed.xlen:
                raise Exception("The target hart specified an XLEN of "
                        f"{h.xlen}, but the command line specified an XLEN of "
                        f"{parsed.xlen}. They must match.")

    return t
