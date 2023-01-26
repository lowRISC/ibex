import collections
import os
import os.path
import random
import re
import shlex
import subprocess
import sys
import tempfile
import time
import traceback
import pipes

import pexpect

print_log_names = False
real_stdout = sys.stdout

# Note that gdb comes with its own testsuite. I was unable to figure out how to
# run that testsuite against the spike simulator.

def find_file(path):
    for directory in (os.getcwd(), os.path.dirname(__file__)):
        fullpath = os.path.join(directory, path)
        relpath = os.path.relpath(fullpath)
        if len(relpath) >= len(fullpath):
            relpath = fullpath
        if os.path.exists(relpath):
            return relpath
    return None

class CompileError(Exception):
    def __init__(self, stdout, stderr):
        super().__init__()
        self.stdout = stdout
        self.stderr = stderr

gcc_cmd = None
def compile(args): # pylint: disable=redefined-builtin
    if gcc_cmd:
        cmd = [gcc_cmd]
    else:
        cmd = ["riscv64-unknown-elf-gcc"]
    cmd.append("-g")
    for arg in args:
        found = find_file(arg)
        if found:
            cmd.append(found)
        else:
            cmd.append(arg)
    header("Compile")
    print("+", " ".join(cmd))
    with subprocess.Popen(cmd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE) as process:
        stdout, stderr = process.communicate()
        if process.returncode:
            print(stdout.decode('ascii'), end=" ")
            print(stderr.decode('ascii'), end=" ")
            header("")
            raise CompileError(stdout, stderr)

class Spike:
    # pylint: disable=too-many-instance-attributes
    # pylint: disable=too-many-locals
    def __init__(self, target, halted=False, timeout=None, with_jtag_gdb=True,
            isa=None, progbufsize=None, dmi_rti=None, abstract_rti=None,
            support_hasel=True, support_abstract_csr=True,
            support_abstract_fpr=False,
            support_haltgroups=True, vlen=128, elen=64, harts=None):
        """Launch spike. Return tuple of its process and the port it's running
        on."""
        self.process = None
        self.isa = isa
        self.progbufsize = progbufsize
        self.dmi_rti = dmi_rti
        self.abstract_rti = abstract_rti
        self.support_abstract_csr = support_abstract_csr
        self.support_abstract_fpr = support_abstract_fpr
        self.support_hasel = support_hasel
        self.support_haltgroups = support_haltgroups
        self.vlen = vlen
        self.elen = elen

        self.harts = harts or target.harts or [target]

        cmd = self.command(target, halted, timeout, with_jtag_gdb)
        self.infinite_loop = target.compile(self.harts[0],
                "programs/checksum.c", "programs/tiny-malloc.c",
                "programs/infinite_loop.S", "-DDEFINE_MALLOC", "-DDEFINE_FREE")
        cmd.append(self.infinite_loop)
        # pylint: disable-next=consider-using-with
        self.logfile = tempfile.NamedTemporaryFile(prefix="spike-",
                suffix=".log")
        logname = self.logfile.name
        self.lognames = [logname]
        if print_log_names:
            real_stdout.write("Temporary spike log: {logname}\n")
        self.logfile.write(("+ " + " ".join(cmd) + "\n").encode())
        self.logfile.flush()
        # pylint: disable-next=consider-using-with
        self.process = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                stdout=self.logfile, stderr=self.logfile)

        if with_jtag_gdb:
            self.port = None
            for _ in range(30):
                with open(logname, encoding='utf-8') as fd:
                    m = re.search(r"Listening for remote bitbang connection on "
                            r"port (\d+).", fd.read())
                if m:
                    self.port = int(m.group(1))
                    os.environ['REMOTE_BITBANG_PORT'] = m.group(1)
                    break
                time.sleep(0.11)
            if not self.port:
                print_log(logname)
                raise Exception("Didn't get spike message about bitbang "
                        "connection")

    # pylint: disable=too-many-branches
    def command(self, target, halted, timeout, with_jtag_gdb):
        # pylint: disable=no-self-use
        if target.sim_cmd:
            cmd = shlex.split(target.sim_cmd)
        else:
            cmd = ["spike"]

        cmd += [f"-p{len(self.harts)}"]

        assert len(set(t.xlen for t in self.harts)) == 1, \
                "All spike harts must have the same XLEN"

        if self.isa:
            isa = self.isa
        else:
            isa = f"RV{self.harts[0].xlen}G"

        cmd += ["--isa", isa]
        cmd += ["--dm-auth"]

        if not self.progbufsize is None:
            cmd += ["--dm-progsize", str(self.progbufsize)]
            cmd += ["--dm-sba", "64"]

        if not self.dmi_rti is None:
            cmd += ["--dmi-rti", str(self.dmi_rti)]

        if not self.abstract_rti is None:
            cmd += ["--dm-abstract-rti", str(self.abstract_rti)]

        if not self.support_abstract_csr:
            cmd.append("--dm-no-abstract-csr")

        if not self.support_abstract_fpr:
            cmd.append("--dm-no-abstract-fpr")

        if not self.support_hasel:
            cmd.append("--dm-no-hasel")

        if not self.support_haltgroups:
            cmd.append("--dm-no-halt-groups")

        if 'V' in isa[2:]:
            cmd.append(f"--varch=vlen:{self.vlen},elen:{self.elen}")

        assert len(set(t.ram for t in self.harts)) == 1, \
                "All spike harts must have the same RAM layout"
        assert len(set(t.ram_size for t in self.harts)) == 1, \
                "All spike harts must have the same RAM layout"
        os.environ['WORK_AREA'] = f'0x{self.harts[0].ram:x}'
        cmd += [f"-m0x{self.harts[0].ram:x}:0x{self.harts[0].ram_size:x}"]

        if timeout:
            cmd = ["timeout", str(timeout)] + cmd

        if halted:
            cmd.append('-H')
        if with_jtag_gdb:
            cmd += ['--rbb-port', '0']
            os.environ['REMOTE_BITBANG_HOST'] = 'localhost'

        return cmd

    def __del__(self):
        if self.process:
            try:
                self.process.kill()
                self.process.wait()
            except OSError:
                pass

    def wait(self, *args, **kwargs):
        return self.process.wait(*args, **kwargs)

class MultiSpike:
    def __init__(self, spikes):
        self.process = None

        self.spikes = spikes
        self.lognames = sum((spike.lognames for spike in spikes), [])
        # pylint: disable-next=consider-using-with
        self.logfile = tempfile.NamedTemporaryFile(prefix="daisychain-",
                suffix=".log")
        self.lognames.append(self.logfile.name)

        # Now create the daisy-chain process.
        cmd = ["./rbb_daisychain.py", "0"] + \
            [str(spike.port) for spike in spikes]
        self.logfile.write(f"+ {cmd}\n".encode())
        self.logfile.flush()
        # pylint: disable-next=consider-using-with
        self.process = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                stdout=self.logfile, stderr=self.logfile)

        self.port = None
        for _ in range(30):
            with open(self.lognames[-1], encoding='utf=8') as fd:
                m = re.search(r"Listening on port (\d+).", fd.read())
            if m:
                self.port = int(m.group(1))
                break
            time.sleep(0.11)
        if not self.port:
            print_log(self.lognames[-1])
            raise Exception("Didn't get daisy chain message about which port "
                            "it's listening on.")

        os.environ['REMOTE_BITBANG_HOST'] = 'localhost'
        os.environ['REMOTE_BITBANG_PORT'] = str(self.port)

    def __del__(self):
        if self.process:
            try:
                self.process.kill()
                self.process.wait()
            except OSError:
                pass

class VcsSim:
    # pylint: disable-next=consider-using-with
    logfile = tempfile.NamedTemporaryFile(prefix='simv', suffix='.log')
    logname = logfile.name
    lognames = [logname]

    def __init__(self, sim_cmd=None, debug=False, timeout=300):
        if sim_cmd:
            cmd = shlex.split(sim_cmd)
        else:
            cmd = ["simv"]
        cmd += ["+jtag_vpi_enable"]
        if debug:
            cmd[0] = cmd[0] + "-debug"
            cmd += ["+vcdplusfile=output/gdbserver.vpd"]

        # pylint: disable-next=consider-using-with
        logfile = open(self.logname, "w", encoding='utf-8')
        if print_log_names:
            real_stdout.write(f"Temporary VCS log: {self.logname}\n")
        logfile.write("+ " + " ".join(cmd) + "\n")
        logfile.flush()

        with open(self.logname, "r", encoding='utf-8') as listenfile:
            listenfile.seek(0, 2)
            # pylint: disable-next=consider-using-with
            self.process = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                    stdout=logfile, stderr=logfile)
            done = False
            start = time.time()
            while not done:
                # Fail if VCS exits early
                exit_code = self.process.poll()
                if exit_code is not None:
                    raise RuntimeError(
                        f'VCS simulator exited early with status {exit_code}')

                line = listenfile.readline()
                if not line:
                    time.sleep(1)
                match = re.match(r"^Listening on port (\d+)$", line)
                if match:
                    done = True
                    self.port = int(match.group(1))
                    os.environ['JTAG_VPI_PORT'] = str(self.port)

                if (time.time() - start) > timeout:
                    raise Exception(
                        "Timed out waiting for VCS to listen for JTAG vpi")

    def __del__(self):
        try:
            self.process.kill()
            self.process.wait()
        except OSError:
            pass

class Openocd:
    # pylint: disable-next=consider-using-with
    logfile = tempfile.NamedTemporaryFile(prefix='openocd', suffix='.log')
    logname = logfile.name

    def __init__(self, server_cmd=None, config=None, debug=False, timeout=60,
                 freertos=False, debug_openocd=False):
        self.timeout = timeout
        self.debug_openocd = debug_openocd

        if server_cmd:
            cmd = shlex.split(server_cmd)
        else:
            cmd = ["openocd"]
            if debug:
                cmd.append("-d")

        # This command needs to come before any config scripts on the command
        # line, since they are executed in order.
        cmd += [
            # Tell OpenOCD to bind gdb to an unused, ephemeral port.
            "--command",
            "gdb_port 0",
            # Disable tcl and telnet servers, since they are unused and because
            # the port numbers will conflict if multiple OpenOCD processes are
            # running on the same server.
            "--command",
            "tcl_port disabled",
            "--command",
            "telnet_port disabled",
        ]

        if config:
            self.config_file = find_file(config)
            if self.config_file is None:
                print("Unable to read file", config)
                sys.exit(1)

            cmd += ["-f", self.config_file]
        if debug:
            cmd.append("-d")

        extra_env = {}
        if freertos:
            extra_env['USE_FREERTOS'] = "1"
        else:
            extra_env['USE_FREERTOS'] = "0"

        # pylint: disable-next=consider-using-with
        raw_logfile = open(Openocd.logname, "wb")
        try:
            # pylint: disable-next=consider-using-with
            spike_dasm = subprocess.Popen("spike-dasm", stdin=subprocess.PIPE,
                    stdout=raw_logfile, stderr=raw_logfile)
            logfile = spike_dasm.stdin
        except FileNotFoundError:
            logfile = raw_logfile
        if print_log_names:
            real_stdout.write(f"Temporary OpenOCD log: {Openocd.logname}\n")
        env_entries = ("REMOTE_BITBANG_HOST", "REMOTE_BITBANG_PORT",
                "WORK_AREA")
        env_entries = [key for key in env_entries if key in os.environ]
        parts = [
            " ".join(f"{key}={os.environ[key]}" for key in env_entries),
            " ".join(f"{k}={v}" for k, v in extra_env.items()),
            " ".join(map(pipes.quote, cmd))
        ]
        logfile.write(("+ " + " ".join(parts) + "\n").encode())
        logfile.flush()

        self.gdb_ports = []
        self.process = self.start(cmd, logfile, extra_env)

    def start(self, cmd, logfile, extra_env):
        combined_env = {**os.environ, **extra_env}
        # pylint: disable-next=consider-using-with
        process = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                stdout=logfile, stderr=logfile, env=combined_env)

        try:
            # Wait for OpenOCD to have made it through riscv_examine(). When
            # using OpenOCD to communicate with a simulator this may take a
            # long time, and gdb will time out when trying to connect if we
            # attempt too early.
            start = time.time()
            messaged = False
            with open(Openocd.logname, "r", encoding='utf-8') as fd:
                while True:
                    line = fd.readline()
                    if not line:
                        if not process.poll() is None:
                            raise Exception("OpenOCD exited early.")
                        time.sleep(0.1)
                        continue

                    m = re.search(
                        r"Listening on port (\d+) for gdb connections", line)
                    if m:
                        self.gdb_ports.append(int(m.group(1)))

                    if "telnet server disabled" in line:
                        break

                    if not messaged and time.time() - start > 1:
                        messaged = True
                        print("Waiting for OpenOCD to start...")
                    if (time.time() - start) > self.timeout:
                        raise Exception("Timed out waiting for OpenOCD to "
                                "listen for gdb")

            if self.debug_openocd:
                # pylint: disable=consider-using-with
                self.debugger = subprocess.Popen(["gnome-terminal", "-e",
                                                  f"gdb --pid={process.pid}"])
            return process

        except Exception:
            print_log(Openocd.logname)
            raise

    def __del__(self):
        try:
            self.process.terminate()
            start = time.time()
            while time.time() < start + 10:
                if self.process.poll():
                    break
            else:
                self.process.kill()
        except (OSError, AttributeError):
            pass

    def smp(self):
        """Return true iff OpenOCD internally sees the harts as part of an SMP
        group."""
        with open(self.config_file, "r", encoding='utf-8') as handle:
            for line in handle:
                if "target smp" in line:
                    return True
        return False

class OpenocdCli:
    def __init__(self, port=4444):
        self.child = pexpect.spawn(
                f"sh -c 'telnet localhost {port} | tee openocd-cli.log'")
        self.child.expect("> ")

    def command(self, cmd):
        self.child.sendline(cmd)
        self.child.expect(cmd)
        self.child.expect("\n")
        self.child.expect("> ")
        return self.child.before.strip("\t\r\n \0").decode("utf-8")

    def reg(self, reg=''):
        output = self.command(f"reg {reg}")
        matches = re.findall(r"(\w+) \(/\d+\): (0x[0-9A-F]+)", output)
        values = {r: int(v, 0) for r, v in matches}
        if reg:
            return values[reg]
        return values

    def load_image(self, image):
        output = self.command(f"load_image {image}")
        if 'invalid ELF file, only 32bits files are supported' in output:
            raise TestNotApplicable(output)

class CannotAccess(Exception):
    def __init__(self, address):
        Exception.__init__(self)
        self.address = address

class CannotInsertBreakpoint(Exception):
    def __init__(self, number):
        Exception.__init__(self)
        self.number = number

class CouldNotFetch(Exception):
    def __init__(self, regname, explanation):
        Exception.__init__(self)
        self.regname = regname
        self.explanation = explanation

class CouldNotReadRegisters(Exception):
    def __init__(self, explanation):
        Exception.__init__(self)
        self.explanation = explanation

class NoSymbol(Exception):
    def __init__(self, symbol):
        Exception.__init__(self)
        self.symbol = symbol

    def __repr__(self):
        return f"NoSymbol({self.symbol!r})"

class UnknownThread(Exception):
    def __init__(self, explanation):
        Exception.__init__(self, explanation)

Thread = collections.namedtuple('Thread', ('id', 'description', 'target_id',
    'name', 'frame'))

class Repeat:
    def __init__(self, count):
        self.count = count

def tokenize(text):
    index = 0
    while index < len(text):
        for regex, fn in (
                (r"[\s]+", lambda m: None),
                (r"[,{}=]", lambda m: m.group(0)),
                (r"0x[\da-fA-F]+", lambda m: int(m.group(0)[2:], 16)),
                (r"-?\d*\.\d+(e[-+]\d+)?", lambda m: float(m.group(0))),
                (r"-?\d+", lambda m: int(m.group(0))),
                (r"-?nan\(0x[a-f0-9]+\)", lambda m: float("nan")),
                (r"<repeats (\d+) times>", lambda m: Repeat(int(m.group(1)))),
                (r"Could not fetch register \"(\w+)\"; (.*)$",
                    lambda m: CouldNotFetch(m.group(1), m.group(2))),
                (r"Could not read registers; (.*)$",
                    lambda m: CouldNotReadRegisters(m.group(1))),
                (r"Cannot access memory at address (0x[0-9a-f]+)",
                    lambda m: CannotAccess(int(m.group(1), 0))),
                (r"Cannot insert breakpoint (\d+).",
                    lambda m: CannotInsertBreakpoint(int(m.group(1)))),
                (r'No symbol "(\w+)" in current context.',
                    lambda m: NoSymbol(m.group(1))),
                (r'"([^"]*)"', lambda m: m.group(1)),
                (r"[a-zA-Z][a-zA-Z\d]*", lambda m: m.group(0)),
                ):
            m = re.match(regex, text[index:])
            if m:
                index += len(m.group(0))
                token = fn(m)
                if not token is None:
                    yield token
                break
        else:
            raise Exception(repr(text[index:]))

def parse_dict(tokens):
    assert tokens[0] == "{"
    tokens.pop(0)
    result = {}
    while True:
        key = tokens.pop(0)
        assert tokens.pop(0) == "="
        value = parse_tokens(tokens)
        result[key] = value
        token = tokens.pop(0)
        if token == "}":
            return result
        assert token == ","

def parse_list(tokens):
    assert tokens[0] == "{"
    tokens.pop(0)
    result = []
    while True:
        result.append(tokens.pop(0))
        token = tokens.pop(0)
        if isinstance(token, Repeat):
            result += [result[-1]] * (token.count - 1)
            token = tokens.pop(0)
        if token == "}":
            return result
        assert token == ","

def parse_dict_or_list(tokens):
    assert tokens[0] == "{"
    if tokens[2] == "=":
        return parse_dict(tokens)
    else:
        return parse_list(tokens)

def parse_tokens(tokens):
    if isinstance(tokens[0], Exception):
        raise tokens[0]
    if isinstance(tokens[0], (float, int)):
        return tokens.pop(0)
    if tokens[0] == "{":
        return parse_dict_or_list(tokens)
    if isinstance(tokens[0], str):
        return tokens.pop(0)
    raise Exception(f"Unsupported tokens: {tokens!r}")

def parse_rhs(text):
    tokens = list(tokenize(text))
    result = parse_tokens(tokens)
    if tokens:
        raise Exception(f"Unexpected input: {tokens!r}")
    return result

class Gdb:
    """A single gdb class which can interact with one or more gdb instances."""

    # pylint: disable=too-many-public-methods
    # pylint: disable=too-many-instance-attributes

    reset_delays = (127, 181, 17, 13, 83, 151, 31, 67, 131, 167, 23, 41, 61,
            11, 149, 107, 163, 73, 47, 43, 173, 7, 109, 101, 103, 191, 2, 139,
            97, 193, 157, 3, 29, 79, 113, 5, 89, 19, 37, 71, 179, 59, 137, 53)

    def __init__(self, target, ports, cmd=None, timeout=60, binaries=None):
        assert ports

        self.target = target
        self.ports = ports
        self.cmd = cmd or "riscv64-unknown-elf-gdb"
        self.timeout = timeout
        self.binaries = binaries or [None] * len(ports)

        self.reset_delay_index = 0
        self.stack = []
        self.harts = {}

        self.logfiles = []
        self.children = []
        for port in ports:
            # pylint: disable-next=consider-using-with
            logfile = tempfile.NamedTemporaryFile(prefix=f"gdb@{port}-",
                                                  suffix=".log")
            self.logfiles.append(logfile)
            if print_log_names:
                real_stdout.write(f"Temporary gdb log: {logfile.name}\n")
            child = pexpect.spawn(self.cmd)
            child.logfile = logfile
            child.logfile.write(f"+ {self.cmd}\n".encode())
            self.children.append(child)
            self.select_child(child)
            self.wait()
            self.command("set style enabled off", reset_delays=None)
            self.command("set confirm off", reset_delays=None)
            self.command("set width 0", reset_delays=None)
            self.command("set height 0", reset_delays=None)
            # Force consistency.
            self.command("set print entry-values no", reset_delays=None)
            self.command(f"set remotetimeout {self.timeout}", reset_delays=None)
            self.command(f"set remotetimeout {self.target.timeout_sec}")
        self.active_child = self.children[0]

    def connect(self):
        with PrivateState(self):
            for port, child, binary in zip(self.ports, self.children,
                                        self.binaries):
                self.select_child(child)
                self.command(f"target extended-remote localhost:{port}",
                        ops=10, reset_delays=None)
                if binary:
                    output = self.command(f"file {binary}")
                    assertIn("Reading symbols", output)
                threads = self.threads()
                for t in threads:
                    hartid = None
                    if t.name:
                        m = re.search(r"Hart (\d+)", t.name)
                        if m:
                            hartid = int(m.group(1))
                    if hartid is None:
                        if self.harts:
                            hartid = max(self.harts) + 1
                        else:
                            hartid = 0
                    # solo: True iff this is the only thread on this child
                    self.harts[hartid] = {'child': child,
                            'thread': t,
                            'solo': len(threads) == 1}

    def disconnect(self):
        with PrivateState(self):
            for child in self.children:
                self.select_child(child)
                self.command("disconnect")

    def __del__(self):
        for child in self.children:
            del child

    def one_hart_per_gdb(self):
        return all(h['solo'] for h in self.harts.values())

    def lognames(self):
        return [logfile.name for logfile in self.logfiles]

    def select_child(self, child):
        self.active_child = child

    def select_hart(self, hart):
        h = self.harts[hart.id]
        self.select_child(h['child'])
        if not h['solo']:
            output = self.command(f"thread {h['thread'].id}", ops=5)
            if "Unknown" in output:
                raise UnknownThread(output)

    def push_state(self):
        self.stack.append({
            'active_child': self.active_child
            })

    def pop_state(self):
        state = self.stack.pop()
        self.active_child = state['active_child']

    def wait(self):
        """Wait for prompt."""
        self.active_child.expect(r"\(gdb\)")

    def command(self, command, ops=1, reset_delays=0):
        """ops is the estimated number of operations gdb will have to perform
        to perform this command. It is used to compute a timeout based on
        self.timeout."""
        if not reset_delays is None:
            if reset_delays == 0:
                reset_delays = self.reset_delays[self.reset_delay_index]
                self.reset_delay_index = (self.reset_delay_index + 1) % \
                        len(self.reset_delays)
            self.command(f"monitor riscv reset_delays {reset_delays}",
                    reset_delays=None)
        timeout = max(1, ops) * self.timeout
        self.active_child.sendline(command)
        self.active_child.expect("\n", timeout=timeout)
        self.active_child.expect(r"\(gdb\)", timeout=timeout)
        output = self.active_child.before.decode("utf-8", errors="ignore")
        ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
        return ansi_escape.sub('', output).strip()

    def interact(self):
        """Call this from a test at a point where you just want to interact with
        gdb directly. This is useful when you're debugging a problem and just
        want to take over at a certain point in the test."""
        saved_stdout = sys.stdout
        sys.stdout = real_stdout
        try:
            print()
            print("Interact with the gdb instance created by the test.")
            print("This is not a true gdb prompt, so things like tab ")
            print("completion won't work.")
            while True:
                command = input("(gdb) ")
                print(self.command(command))
        finally:
            sys.stdout = saved_stdout


    def global_command(self, command):
        """Execute this command on every gdb that we control."""
        with PrivateState(self):
            for child in self.children:
                self.select_child(child)
                self.command(command)

    def system_command(self, command, ops=20):
        """Execute this command on every unique system that we control."""
        done = set()
        output = ""
        with PrivateState(self):
            for i, child in enumerate(self.children):
                self.select_child(child)
                if self.target.harts[i].system in done:
                    self.command("set $pc=_start")
                else:
                    output += self.command(command, ops=ops)
                    done.add(self.target.harts[i].system)
        return output

    def c(self, wait=True, sync=True, checkOutput=True, ops=20):
        """
        Dumb c command.
        In RTOS mode, gdb will resume all harts.
        In multi-gdb mode, this command will just go to the current gdb, so
        will only resume one hart.
        """
        if sync:
            sync = ""
        else:
            sync = "&"
        if wait:
            output = self.command(f"c{sync}", ops=ops)
            if checkOutput:
                assert "Continuing" in output
                assert "Could not insert hardware" not in output
            return output
        else:
            self.active_child.sendline(f"c{sync}")
            self.active_child.expect("Continuing", timeout=ops * self.timeout)
            return ""

    def c_all(self, wait=True):
        """
        Resume every hart.

        This function works fine when using multiple gdb sessions, but the
        caller must be careful when using it nonetheless. gdb's behavior is to
        not set breakpoints until just before the hart is resumed, and then
        clears them as soon as the hart halts. That means that you can't set
        one software breakpoint, and expect multiple harts to hit it. It's
        possible that the first hart completes set/run/halt/clear before the
        second hart even gets to resume, so it will never hit the breakpoint.
        """
        with PrivateState(self):
            for child in self.children:
                child.sendline("c")
                child.expect("Continuing")

            if wait:
                for child in self.children:
                    child.expect(r"\(gdb\)")

    def interrupt(self, ops=None):
        if not ops:
            ops = len(self.harts)
        self.active_child.send("\003")
        self.active_child.expect(r"\(gdb\)", timeout=self.timeout * ops)
        return self.active_child.before.strip().decode()

    def interrupt_all(self):
        for child in self.children:
            self.select_child(child)
            self.interrupt()

    def x(self, address, size='w', count=1):
        output = self.command(f"x/{count}{size} {address}", ops=count / 16)
        values = []
        for line in output.splitlines():
            for value in line.split(':')[1].strip().split():
                values.append(int(value, 0))
        if len(values) == 1:
            return values[0]
        return values

    def p_raw(self, obj):
        output = self.command(f"p {obj}")
        m = re.search("Cannot access memory at address (0x[0-9a-f]+)", output)
        if m:
            raise CannotAccess(int(m.group(1), 0))
        return output.split('=', 1)[-1].strip()

    def p(self, obj, fmt="/x", ops=1):
        output = self.command(f"p{fmt} {obj}", ops=ops).splitlines()[-1]
        rhs = output.split('=', 1)[-1]
        return parse_rhs(rhs)

    def p_fpr(self, obj, ops=1):
        result = self.p(obj, fmt="", ops=ops)
        if isinstance(result, dict):
            return result['double']
        return result

    def p_string(self, obj):
        output = self.command(f"p {obj}")
        value = shlex.split(output.split('=')[-1].strip())[1]
        return value

    def info_registers(self, group="", ops=5):
        output = self.command(f"info registers {group}", ops=ops)
        result = {}
        for line in output.splitlines():
            m = re.match(r"(\w+)\s+({.*})(?:\s+(\(.*\)))?", line)
            if m:
                parts = m.groups()
            else:
                parts = line.split()
            name = parts[0]
            if "Could not fetch" in line:
                result[name] = " ".join(parts[1:])
            else:
                result[name] = parse_rhs(parts[1])
        return result

    def stepi(self, wait=True):
        if wait:
            return self.command("stepi", ops=10)
        else:
            self.active_child.sendline("stepi")
            self.active_child.expect("stepi", timeout=self.timeout)
            return ""

    def expect(self, text, ops=1):
        return self.active_child.expect(text, timeout=ops * self.timeout)

    def load(self):
        output = self.system_command("load", ops=1000)
        assert "failed" not in  output
        assert "Transfer rate" in output
        output = self.system_command("compare-sections", ops=1000)
        assert "matched" in output
        assert "MIS" not in output

    def b(self, location):
        output = self.command(f"b {location}", ops=5)
        assert "not defined" not in output
        assert "Breakpoint" in output
        m = re.search(r"Breakpoint (\d+),? ", output)
        assert m, output
        return int(m.group(1))

    def hbreak(self, location):
        output = self.command(f"hbreak {location}", ops=5)
        assert "not defined" not in output
        assert "Hardware assisted breakpoint" in output
        return output

    def watch(self, expr):
        output = self.command(f"watch {expr}", ops=5)
        assert "not defined" not in output
        assert "atchpoint" in output
        return output

    def swatch(self, expr):
        self.command("show can-use-hw-watchpoints")
        self.command("set can-use-hw-watchpoints 0")
        output = self.command(f"watch {expr}", ops=5)
        assert "not defined" not in output
        assert "atchpoint" in output
        self.command("set can-use-hw-watchpoints 1")
        return output

    def threads(self):
        output = self.command("info threads", ops=100)
        threads = []
        for line in output.splitlines():
            m = re.match(
                    r"[\s\*]*(\d+)\s*"
                    r'(Remote target'
                    r'|Thread (\d+)\s*(?:".*?")?\s*\(Name: ([^\)]+))'
                    r"\s*(.*)", line)
            if m:
                threads.append(Thread(*m.groups()))
        assert threads
        return threads

    def thread(self, thread):
        return self.command(f"thread {thread.id}")

    def where(self):
        return self.command("where 1")

class PrivateState:
    def __init__(self, gdb):
        self.gdb = gdb

    def __enter__(self):
        self.gdb.push_state()

    def __exit__(self, _type, _value, _traceback):
        self.gdb.pop_state()

def run_all_tests(module, target, parsed):
    todo = []
    for name in dir(module):
        definition = getattr(module, name)
        if isinstance(definition, type) and hasattr(definition, 'test') and \
                (not parsed.test or any(test in name for test in parsed.test)):
            todo.append((name, definition, None))

    if parsed.list_tests:
        for name, definition, hart in todo:
            print(name)
        return 0

    try:
        os.makedirs(parsed.logs)
    except OSError:
        # There's a race where multiple instances of the test program might
        # decide to create the logs directory at the same time.
        pass

    overall_start = time.time()

    global gdb_cmd  # pylint: disable=global-statement
    gdb_cmd = parsed.gdb
    global gcc_cmd  # pylint: disable=global-statement
    gcc_cmd = parsed.gcc

    examine_added = False
    for hart in target.harts:
        if parsed.misaval:
            hart.misa = int(parsed.misaval, 16)
            print(f"Using $misa from command line: 0x{hart.misa:x}")
        elif hart.misa:
            print(f"Using $misa from hart definition: 0x{hart.misa:x}")
        elif not examine_added:
            todo.insert(0, ("ExamineTarget", ExamineTarget, None))
            examine_added = True

    results, count = run_tests(parsed, target, todo)

    header(f"ran {count} tests in {time.time() - overall_start:.0f}s", dash=':')

    return print_results(results)

good_results = set(('pass', 'not_applicable'))
def run_tests(parsed, target, todo):
    results = {}
    count = 0

    for name, definition, hart in todo:
        timestamp = time.strftime("%Y%m%d-%H%M%S")
        log_name = os.path.join(parsed.logs,
                                f"{timestamp}-"
                                f"{type(target).__name__}-{name}.log")
        # pylint: disable-next=consider-using-with
        log_fd = open(log_name, 'w', encoding='utf-8')
        print(f"[{name}] Starting > {log_name}")
        instance = definition(target, hart)
        sys.stdout.flush()
        log_fd.write(f"Test: {name}\n")
        log_fd.write(f"Target: {type(target).__name__}\n")
        start = time.time()
        global real_stdout  # pylint: disable=global-statement
        real_stdout = sys.stdout
        sys.stdout = log_fd
        try:
            result = instance.run()
            log_fd.write(f"Result: {result}\n")
            log_fd.write(f"Logfile: {log_name}\n")
            log_fd.write(f"Reproduce: {sys.argv[0]} {parsed.target} {name}\n")
        finally:
            sys.stdout = real_stdout
            log_fd.write(f"Time elapsed: {time.time() - start:.2f}s\n")
            log_fd.flush()
        print(f"[{name}] {result} in {time.time() - start:.2f}s")
        if result not in good_results and parsed.print_failures:
            with open(log_name, encoding='utf-8') as handle:
                sys.stdout.write(handle.read())
        sys.stdout.flush()
        results.setdefault(result, []).append((name, log_name))
        count += 1
        if result not in good_results and parsed.fail_fast:
            break

    return results, count

def print_results(results):
    result = 0
    for key, value in results.items():
        print(f"{len(value)} tests returned {key}")
        if key not in good_results:
            result = 1
            for name, log_name in value:
                print(f"   {name} > {log_name}")

    return result

def add_test_run_options(parser):
    parser.add_argument("--logs", default="logs",
            help="Store logs in the specified directory.")
    parser.add_argument("--fail-fast", "-f", action="store_true",
            help="Exit as soon as any test fails.")
    parser.add_argument("--print-failures", action="store_true",
            help="When a test fails, print the log file to stdout.")
    parser.add_argument("--print-log-names", "--pln", action="store_true",
            help="Print names of temporary log files as soon as they are "
            "created.")
    parser.add_argument("--list-tests", action="store_true",
            help="Print out a list of tests, and exit immediately.")
    parser.add_argument("test", nargs='*',
            help="Run only tests that are named here.")
    parser.add_argument("--gcc",
            help="The command to use to start gcc.")
    parser.add_argument("--gdb",
            help="The command to use to start gdb.")
    parser.add_argument("--misaval",
            help="Don't run ExamineTarget, just assume the misa value which is "
            "specified.")

def header(title, dash='-', length=78):
    if title:
        dashes = dash * (length - 4 - len(title))
        before = dashes[:len(dashes)//2]
        after = dashes[len(dashes)//2:]
        print(f"{before}[ {title} ]{after}")
    else:
        print(dash * length)

def print_log_handle(name, handle):
    header(name)
    for l in handle:
        sys.stdout.write(l)
    print()

def print_log(path):
    with open(path, "r", errors='ignore', encoding='utf-8') as handle:
        print_log_handle(path, handle)

class BaseTest:
    # pylint: disable=too-many-instance-attributes
    compiled = {}

    def __init__(self, target, hart=None):
        self.target = target
        if hart:
            self.hart = hart
        else:
            self.hart = random.choice(target.harts)
        self.server = None
        self.target_process = None
        self.binary = None
        self.start = 0
        self.logs = []
        self.binaries = []

    def early_applicable(self):
        """Return a false value if the test has determined it cannot run
        without ever needing to talk to the target or server."""
        # pylint: disable=no-self-use
        return True

    def freertos(self):
        """Return a true value if the test is running a FreeRTOS binary where
        the debugger should expose FreeRTOS threads to gdb."""
        # pylint: disable=no-self-use
        return False

    def setup(self):
        pass

    def compile(self):
        compile_args = getattr(self, 'compile_args', None)
        self.binaries = []
        if compile_args:
            for hart in self.target.harts:
                key = (compile_args, hart.misa)
                if key not in BaseTest.compiled:
                    BaseTest.compiled[key] = \
                            self.target.compile(hart, *compile_args)
                self.binaries.append(BaseTest.compiled.get(key))

    def classSetup(self):
        self.compile()
        self.target_process = self.target.create()
        if self.target_process:
            self.logs += self.target_process.lognames
        try:
            self.server = self.target.server(self)
            self.logs.append(self.server.logname)
        except Exception:
            for log in self.logs:
                print_log(log)
            raise

    def classTeardown(self):
        del self.server
        del self.target_process

    def postMortem(self):
        pass

    def run(self):
        """
        If compile_args is set, compile a program and set self.binaries.

        Call setup().

        Then call test() and return the result, displaying relevant information
        if an exception is raised.
        """

        sys.stdout.flush()

        if self.__class__.__name__ in self.target.skip_tests or \
                not self.early_applicable():
            return "not_applicable"

        self.start = time.time()

        try:
            self.classSetup()
            self.setup()
            result = self.test()    # pylint: disable=no-member
        except TestNotApplicable:
            result = "not_applicable"
        except Exception as e: # pylint: disable=broad-except
            if isinstance(e, TestFailed):
                result = "fail"
            else:
                result = "exception"
            if isinstance(e, TestFailed):
                # pylint: disable=no-member
                header("Message")
                print(e.message)
            header("Traceback")
            traceback.print_exc(file=sys.stdout)
            try:
                self.postMortem()
            except Exception as e:  # pylint: disable=broad-except
                header("postMortem Exception")
                print(e)
                traceback.print_exc(file=sys.stdout)
            return result

        finally:
            # Get handles to logs before the files are deleted.
            logs = []
            for log in self.logs:
                # pylint: disable=consider-using-with
                logs.append((log,
                             open(log, "r", errors='ignore', encoding='utf-8')))

            self.classTeardown()
            for name, handle in logs:
                print_log_handle(name, handle)
            header("End of logs")

        if not result:
            result = 'pass'
        return result

gdb_cmd = None
class GdbTest(BaseTest):
    def __init__(self, target, hart=None):
        BaseTest.__init__(self, target, hart=hart)
        self.gdb = None

    def write_nop_program(self, count):
        for i in range(count):
            # 0x13 is nop
            self.gdb.command(f"p *((int*) 0x{self.hart.ram + i * 4:x})=0x13")
        self.gdb.p(f"$pc=0x{self.hart.ram:x}")

    def classSetup(self):
        BaseTest.classSetup(self)

        self.gdb = Gdb(self.target, self.server.gdb_ports, cmd=gdb_cmd,
                       timeout=self.target.timeout_sec, binaries=self.binaries)

        self.logs += self.gdb.lognames()
        self.gdb.connect()

        for cmd in self.target.gdb_setup:
            self.gdb.command(cmd)

        self.gdb.select_hart(self.hart)

        # FIXME: OpenOCD doesn't handle PRIV now
        #self.gdb.p("$priv=3")

    def postMortem(self):
        if not self.gdb:
            return
        self.gdb.interrupt()
        self.gdb.command("info breakpoints", reset_delays=None)
        self.gdb.command("x/20i $pc", ops=20, reset_delays=None)
        self.gdb.command("info registers all", ops=20, reset_delays=None)
        self.gdb.command("maintenance flush register-cache", reset_delays=None)
        self.gdb.command("info threads", ops=20, reset_delays=None)

    def classTeardown(self):
        del self.gdb
        BaseTest.classTeardown(self)

    def parkOtherHarts(self, symbol=None):
        """Park harts besides the currently selected one in loop_forever()."""
        for hart in self.target.harts:
            # Park all harts that we're not using in a safe place.
            if hart != self.hart:
                self.gdb.select_hart(hart)
                if symbol is None:
                    if hart.support_cease:
                        self.gdb.p("$pc=cease")
                    else:
                        self.gdb.p("$pc=loop_forever")
                else:
                    self.gdb.p(f"$pc={symbol}")

        self.gdb.select_hart(self.hart)

    def disable_pmp(self):
        # Disable physical memory protection by allowing U mode access to all
        # memory.
        try:
            self.gdb.p("$pmpcfg0=0xf")  # TOR, R, W, X
            if self.gdb.p("$pmpcfg0") != 0xf:
                # TOR is unsupported (detected via WARL) so use NAPOT instead
                self.gdb.p("$pmpcfg0=0x1f") # NAPOT, R, W, X
                self.gdb.p("$pmpaddr0=0x" + "f" * (self.hart.xlen // 4))
            else:
                # pmcfg0 readback matches write, so TOR is supported.
                self.gdb.p("$pmpaddr0="
                           f"0x{(self.hart.ram + self.hart.ram_size) >> 2:x}")
        except CouldNotFetch:
            # PMP registers are optional
            pass

    def exit(self, expected_result=10):
        self.gdb.command("delete")
        self.gdb.b("_exit")
        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("_exit", output)
        assertEqual(self.gdb.p("status"), expected_result)
        return output

class GdbSingleHartTest(GdbTest):
    def classSetup(self):
        GdbTest.classSetup(self)
        self.parkOtherHarts()

class ExamineTarget(GdbTest):
    def test(self):
        for hart in self.target.harts:
            self.gdb.select_hart(hart)

            hart.misa = self.gdb.p("$misa")

            txt = "RV"
            misa_xlen = 0
            if ((hart.misa & 0xFFFFFFFF) >> 30) == 1:
                misa_xlen = 32
            elif ((hart.misa & 0xFFFFFFFFFFFFFFFF) >> 62) == 2:
                misa_xlen = 64
            elif ((hart.misa & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) >> 126) == 3:
                misa_xlen = 128
            else:
                raise TestFailed("Couldn't determine XLEN from $misa "
                                 f"(0x{self.hart.misa:x})")

            if misa_xlen != hart.xlen:
                raise TestFailed(f"MISA reported XLEN of {misa_xlen} but we "
                        f"were expecting XLEN of {hart.xlen}\n")

            txt += f"{misa_xlen}"

            for i in range(26):
                if hart.misa & (1<<i):
                    txt += chr(i + ord('A'))
            print(txt, end=" ")

class TestFailed(Exception):
    def __init__(self, message, comment=None):
        Exception.__init__(self)
        self.message = message
        if comment:
            self.message += f": {comment}"

class TestNotApplicable(Exception):
    def __init__(self, message=""):
        Exception.__init__(self)
        self.message = message

def assertEqual(a, b, comment=None):
    if a != b:
        raise TestFailed(f"{a!r} != {b!r}", comment)

def assertNotEqual(a, b, comment=None):
    if a == b:
        raise TestFailed(f"{a!r} == {b!r}", comment)

def assertIn(a, b):
    if a not in b:
        raise TestFailed(f"{a!r} not in {b!r}")

def assertNotIn(a, b, comment=None):
    if a in b:
        raise TestFailed(f"{a!r} in {b!r}", comment)

def assertGreater(a, b):
    if not a > b:
        raise TestFailed(f"{a!r} not greater than {b!r}")

def assertLess(a, b, comment=None):
    if not a < b:
        raise TestFailed(f"{a!r} not less than {b!r}", comment)

def assertTrue(a):
    if not a:
        raise TestFailed(f"{a!r} is not True", a)

def assertRegex(text, regexp):
    if not re.search(regexp, text):
        raise TestFailed(f"can't find {regexp!r} in {text!r}")
