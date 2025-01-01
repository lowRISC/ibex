#!/usr/bin/env python3

import argparse
import binascii
import random
import struct
import sys
import tempfile
import time
import os
import re

import targets
import testlib
from testlib import assertEqual, assertNotEqual
from testlib import assertIn, assertNotIn
from testlib import assertGreater, assertRegex, assertLess
from testlib import GdbTest, GdbSingleHartTest, TestFailed
from testlib import TestNotApplicable, CompileError
from testlib import UnknownThread
from testlib import CouldNotReadRegisters

MSTATUS_UIE = 0x00000001
MSTATUS_SIE = 0x00000002
MSTATUS_HIE = 0x00000004
MSTATUS_MIE = 0x00000008
MSTATUS_UPIE = 0x00000010
MSTATUS_SPIE = 0x00000020
MSTATUS_HPIE = 0x00000040
MSTATUS_MPIE = 0x00000080
MSTATUS_SPP = 0x00000100
MSTATUS_HPP = 0x00000600
MSTATUS_MPP = 0x00001800
MSTATUS_FS = 0x00006000
MSTATUS_XS = 0x00018000
MSTATUS_MPRV = 0x00020000
MSTATUS_PUM = 0x00040000
MSTATUS_MXR = 0x00080000
MSTATUS_VM = 0x1F000000
MSTATUS32_SD = 0x80000000
MSTATUS64_SD = 0x8000000000000000

# pylint: disable=abstract-method

def ihex_line(address, record_type, data):
    assert len(data) < 128
    line = f":{len(data):02X}{address:04X}{record_type:02X}"
    check = len(data)
    check += address % 256
    check += address >> 8
    check += record_type
    for char in data:
        value = ord(char)
        check += value
        line += f"{value:02X}"
    line += f"{(256 - check) % 256:02X}\n"
    return line

def srec_parse(line):
    assert line.startswith(b'S')
    typ = line[:2]
    count = int(line[2:4], 16)
    data = ""
    if typ == b'S0':
        # header
        return 0, 0, 0
    elif typ == b'S3':
        # data with 32-bit address
        # Any higher bits were chopped off.
        address = int(line[4:12], 16)
        for i in range(6, count+1):
            data += f"{int(line[2 * i:2 * i + 2], 16):c}"
        # Ignore the checksum.
        return 3, address, data
    elif typ == b'S7':
        # ignore execution start field
        return 7, 0, 0
    else:
        raise TestFailed(f"Unsupported SREC type {typ!r}.")

def readable_binary_string(s):
    return "".join(f"{ord(c):02x}" for c in s)

class InfoTest(GdbTest):
    def test(self):
        output = self.gdb.command("monitor riscv info")
        info = {}
        for line in output.splitlines():
            if re.search(r"Found \d+ triggers", line):
                continue
            if re.search(r"Disabling abstract command writes to CSRs.", line):
                continue
            if re.search(
                    r"keep_alive.. was not invoked in the \d+ ms timelimit.",
                    line):
                continue
            k, v = line.strip().split()
            info[k] = v
        assertEqual(int(info.get("hart.xlen")), self.hart.xlen)

class SimpleRegisterTest(GdbTest):
    def check_reg(self, name, alias):
        a = random.randrange(1<<self.hart.xlen)
        b = random.randrange(1<<self.hart.xlen)
        self.gdb.p(f"${name}=0x{a:x}")
        assertEqual(self.gdb.p(f"${alias}"), a)
        self.gdb.stepi()
        assertEqual(self.gdb.p(f"${name}"), a)
        assertEqual(self.gdb.p(f"${alias}"), a)
        self.gdb.p(f"${alias}=0x{b:x}")
        assertEqual(self.gdb.p(f"${name}"), b)
        self.gdb.stepi()
        assertEqual(self.gdb.p(f"${name}"), b)
        assertEqual(self.gdb.p(f"${alias}"), b)

    def setup(self):
        self.write_nop_program(5)

class SimpleS0Test(SimpleRegisterTest):
    def test(self):
        self.check_reg("s0", "x8")

class SimpleS1Test(SimpleRegisterTest):
    def test(self):
        self.check_reg("s1", "x9")

class SimpleT0Test(SimpleRegisterTest):
    def test(self):
        self.check_reg("t0", "x5")

class SimpleT1Test(SimpleRegisterTest):
    def test(self):
        self.check_reg("t1", "x6")

class SimpleV13Test(SimpleRegisterTest):
    def test(self):
        if self.hart.extensionSupported('V'):
            vlenb = self.gdb.p("$vlenb")
            # Can't write quadwords, because gdb won't parse a 128-bit hex
            # value.
            written = {}
            for name, byte_count in (('b', 1), ('s', 2), ('w', 4), ('l', 8)):
                written[name] = {}
                for i in range(vlenb // byte_count):
                    written[name][i] = random.randrange(256 ** byte_count)
                    self.gdb.p(f"$v13.{name}[{i}]=0x{written[name][i]:x}")
                self.gdb.stepi()
                self.gdb.p("$v13")
                for i in range(vlenb // byte_count):
                    assertEqual(self.gdb.p(f"$v13.{name}[{i}]"),
                            written[name][i])
        else:
            output = self.gdb.p_raw("$v13")
            assertRegex(output, r"void|Could not fetch register.*")

class SimpleF18Test(SimpleRegisterTest):
    def check_reg(self, name, alias):
        if self.hart.extensionSupported('F'):
            mstatus_fs = 0x00006000
            self.gdb.p(f"$mstatus=$mstatus|0x{mstatus_fs:x}")
            self.gdb.stepi()
            a = random.random()
            b = random.random()
            self.gdb.p_fpr(f"${name}={a:f}")
            assertLess(abs((self.gdb.p_fpr(f"${alias}")) - a), .001)
            self.gdb.stepi()
            assertLess(abs((self.gdb.p_fpr(f"${name}")) - a), .001)
            assertLess(abs((self.gdb.p_fpr(f"${alias}")) - a), .001)
            self.gdb.p_fpr(f"${alias}={b:f}")
            assertLess(abs((self.gdb.p_fpr(f"${name}")) - b), .001)
            self.gdb.stepi()
            assertLess(abs((self.gdb.p_fpr(f"${name}")) - b), .001)
            assertLess(abs((self.gdb.p_fpr(f"${alias}")) - b), .001)

            size = self.gdb.p(f"sizeof(${name})")
            if self.hart.extensionSupported('D'):
                assertEqual(size, 8)
            else:
                assertEqual(size, 4)
        else:
            output = self.gdb.p_raw("$" + name)
            assertRegex(output, r"void|Could not fetch register.*")
            output = self.gdb.p_raw("$" + alias)
            assertRegex(output, r"void|Could not fetch register.*")

    def test(self):
        self.check_reg("f18", "fs2")

class CustomRegisterTest(SimpleRegisterTest):
    def early_applicable(self):
        return self.target.implements_custom_test

    def check_custom(self, magic):
        regs = {k: v for k, v in self.gdb.info_registers("all", ops=20).items()
                if k.startswith("custom")}
        assertEqual(set(regs.keys()),
                set(("custom1",
                    "custom12345",
                    "custom12346",
                    "custom12347",
                    "custom12348")))
        for name, value in regs.items():
            number = int(name[6:])
            if number % 2:
                expect = number + magic
                assertIn(value, (expect, expect + (1<<32)))
            else:
                assertIn("Could not fetch register", value)

    def test(self):
        self.check_custom(0)

        # Now test writing
        magic = 6667
        self.gdb.p(f"$custom12345={12345 + magic}")
        self.gdb.stepi()

        self.check_custom(magic)

class SimpleNoExistTest(GdbTest):
    def test(self):
        try:
            self.gdb.p("$csr2288")
            assert False, "Reading csr2288 should have failed"
        except testlib.CouldNotFetch:
            pass
        try:
            self.gdb.p("$csr2288=5")
            assert False, "Writing csr2288 should have failed"
        except testlib.CouldNotFetch:
            pass

class SimpleMemoryTest(GdbTest):
    def access_test(self, size, data_type):
        assertEqual(self.gdb.p(f"sizeof({data_type})"), size)
        a = 0x86753095555aaaa & ((1<<(size*8))-1)
        b = 0xdeadbeef12345678 & ((1<<(size*8))-1)
        addrA = self.hart.ram
        addrB = self.hart.ram + self.hart.ram_size - size
        self.gdb.p(f"*(({data_type}*)0x{addrA:x}) = 0x{a:x}")
        self.gdb.p(f"*(({data_type}*)0x{addrB:x}) = 0x{b:x}")
        assertEqual(self.gdb.p(f"*(({data_type}*)0x{addrA:x})"), a)
        assertEqual(self.gdb.p(f"*(({data_type}*)0x{addrB:x})"), b)

class MemTest8(SimpleMemoryTest):
    def test(self):
        self.access_test(1, 'char')

class MemTest16(SimpleMemoryTest):
    def test(self):
        self.access_test(2, 'short')

class MemTest32(SimpleMemoryTest):
    def test(self):
        self.access_test(4, 'int')

class MemTest64(SimpleMemoryTest):
    def test(self):
        self.access_test(8, 'long long')

class MemTestReadInvalid(SimpleMemoryTest):
    def test(self):
        bad_address = self.hart.bad_address
        good_address = self.hart.ram + 0x80

        self.write_nop_program(2)
        self.gdb.p("$s0=0x12345678")
        self.gdb.p(f"*((int*)0x{good_address:x})=0xabcdef")
        # This test relies on 'gdb_report_data_abort enable' being executed in
        # the openocd.cfg file.
        try:
            self.gdb.p(f"*((int*)0x{bad_address:x})")
            assert False, "Read should have failed."
        except testlib.CannotAccess as e:
            assertEqual(e.address, bad_address)
        self.gdb.stepi()    # Don't let gdb cache register read
        assertEqual(self.gdb.p(f"*((int*)0x{good_address:x})"), 0xabcdef)
        assertEqual(self.gdb.p("$s0"), 0x12345678)

#class MemTestWriteInvalid(SimpleMemoryTest):
#    def test(self):
#        # This test relies on 'gdb_report_data_abort enable' being executed in
#        # the openocd.cfg file.
#        try:
#            self.gdb.p("*((int*)0xdeadbeef)=8675309")
#            assert False, "Write should have failed."
#        except testlib.CannotAccess as e:
#            assertEqual(e.address, 0xdeadbeef)
#        self.gdb.p("*((int*)0x%x)=6874742" % self.hart.ram)

class MemTestBlockReadInvalid(GdbTest):
    zero_values = "00 00 00 00 00 00 00 00"
    real_values = "EF BE AD DE 78 56 34 12"

    def early_applicable(self):
        return self.target.invalid_memory_returns_zero

    def test(self):
        self.gdb.p(f"*((int*)0x{self.hart.ram + 0:x}) = 0xdeadbeef")
        self.gdb.p(f"*((int*)0x{self.hart.ram + 4:x}) = 0x12345678")

        # read before start of memory
        self.memory_test(self.hart.ram - 8,
                         self.hart.ram,
                         self.zero_values)

        # read across start of memory
        self.memory_test(self.hart.ram - 8,
                         self.hart.ram + 8,
                         self.zero_values + " " + self.real_values)

        # read after start of memory
        self.memory_test(self.hart.ram,
                         self.hart.ram + 8,
                         self.real_values)

        self.gdb.p(f"*((int*)0x{self.hart.ram + self.hart.ram_size - 8:x}) = "
                   "0xdeadbeef")
        self.gdb.p(f"*((int*)0x{self.hart.ram + self.hart.ram_size - 4:x}) = "
                   "0x12345678")

        # read before end of memory
        self.memory_test(self.hart.ram + self.hart.ram_size - 8,
                         self.hart.ram + self.hart.ram_size,
                         self.real_values)

        # read across end of memory
        self.memory_test(self.hart.ram + self.hart.ram_size - 8,
                         self.hart.ram + self.hart.ram_size + 8,
                         self.real_values + " " + self.zero_values)

        # read after end of memory
        self.memory_test(self.hart.ram + self.hart.ram_size,
                         self.hart.ram + self.hart.ram_size + 8,
                         self.zero_values)

    def memory_test(self, start_addr, end_addr, expected_values):
        with tempfile.NamedTemporaryFile(suffix=".simdata") as dump:
            self.gdb.command(f"dump verilog memory {dump.name} "
                             f"0x{start_addr:x} 0x{end_addr:x}")
            self.gdb.command(f"shell cat {dump.name}")
            line = dump.readline()
            line = dump.readline()
        assertEqual(line.strip(), expected_values)

class MemTestBlock(GdbTest):
    length = 1024
    line_length = 16

    def write(self, temporary_file):
        data = ""
        for i in range(self.length // self.line_length):
            line_data = "".join([f"{random.randrange(256):c}"
                for _ in range(self.line_length)])
            data += line_data
            temporary_file.write(ihex_line(i * self.line_length, 0,
                line_data).encode())
        temporary_file.flush()
        return data

    def spot_check_memory(self, data):
        increment = 19 * 4
        for offset in list(range(0, self.length, increment)) + [self.length-4]:
            value = self.gdb.p(f"*((int*)0x{self.hart.ram + offset:x})")
            written = ord(data[offset]) | \
                    (ord(data[offset+1]) << 8) | \
                    (ord(data[offset+2]) << 16) | \
                    (ord(data[offset+3]) << 24)
            assertEqual(value, written)

    def test_block(self, extra_delay):
        with tempfile.NamedTemporaryFile(suffix=".ihex") as a:
            data = self.write(a)

            self.gdb.command(f"shell cat {a.name}")
            self.gdb.command(f"restore {a.name} 0x{self.hart.ram:x}",
                    reset_delays=50 + extra_delay)
        self.spot_check_memory(data)

        with tempfile.NamedTemporaryFile(suffix=".srec") as b:
            self.gdb.command(f"dump srec memory {b.name} 0x{self.hart.ram:x} "
                             f"0x{self.hart.ram + self.length:x}",
                             ops=self.length / 32,
                             reset_delays=100 + extra_delay)
            self.gdb.command(f"shell cat {b.name}")
            highest_seen = 0
            for line in b:
                record_type, address, line_data = srec_parse(line)
                if record_type == 3:
                    offset = address - (self.hart.ram & 0xffffffff)
                    written_data = data[offset:offset+len(line_data)]
                    highest_seen += len(line_data)
                    if line_data != written_data:
                        raise TestFailed(
                            f"Data mismatch at 0x{self.hart.ram + offset:x} "
                            f"(offset 0x{offset:x}); "
                            f"wrote {readable_binary_string(written_data)} but "
                            f"read {readable_binary_string(line_data)}")
        assertEqual(highest_seen, self.length)

# Run memory block tests with different reset delays, so hopefully we hit busy
# at every possible relevant time.
class MemTestBlock0(MemTestBlock):
    def test(self):
        return self.test_block(0)

class MemTestBlock1(MemTestBlock):
    def test(self):
        return self.test_block(1)

class MemTestBlock2(MemTestBlock):
    def test(self):
        return self.test_block(2)

class DisconnectTest(GdbTest):
    def test(self):
        old_values = self.gdb.info_registers("all", ops=20)
        self.gdb.disconnect()
        self.gdb.connect()
        self.gdb.select_hart(self.hart)
        new_values = self.gdb.info_registers("all", ops=20)

        regnames = set(old_values.keys()).union(set(new_values.keys()))
        for regname in regnames:
            if regname in ("mcycle", "minstret", "instret", "cycle", "mip",
                    "time"):
                continue
            assertEqual(old_values[regname], new_values[regname],
                    f"Register {regname} didn't match")

class InstantHaltTest(GdbTest):
    def test(self):
        """Assert that reset is really resetting what it should."""
        self.gdb.command("monitor reset halt")
        self.gdb.command("flushregs")
        threads = self.gdb.threads()
        pcs = []
        for t in threads:
            self.gdb.thread(t)
            pcs.append(self.gdb.p("$pc"))
        for pc in pcs:
            assertIn(pc, self.hart.reset_vectors)
        # mcycle and minstret have no defined reset value.
        mstatus = self.gdb.p("$mstatus")
        assertEqual(mstatus & (MSTATUS_MIE | MSTATUS_MPRV |
            MSTATUS_VM), 0)

class InstantChangePc(GdbTest):
    def test(self):
        """Change the PC right as we come out of reset."""
        # 0x13 is nop
        self.gdb.command("monitor reset halt")
        self.gdb.command("flushregs")
        self.gdb.command(f"p *((int*) 0x{self.hart.ram:x})=0x13")
        self.gdb.command(f"p *((int*) 0x{self.hart.ram + 4:x})=0x13")
        self.gdb.command(f"p *((int*) 0x{self.hart.ram + 8:x})=0x13")
        self.gdb.p(f"$pc=0x{self.hart.ram:x}")
        self.gdb.stepi()
        assertEqual((self.hart.ram + 4), self.gdb.p("$pc"))
        self.gdb.stepi()
        assertEqual((self.hart.ram + 8), self.gdb.p("$pc"))

class ProgramTest(GdbSingleHartTest):
    # Include malloc so that gdb can make function calls. I suspect this malloc
    # will silently blow through the memory set aside for it, so be careful.
    compile_args = ("programs/counting_loop.c", "-DDEFINE_MALLOC",
            "-DDEFINE_FREE")

    def setup(self):
        self.gdb.load()

class ProgramHwWatchpoint(ProgramTest):
    def test(self):
        mainbp = self.gdb.b("main")
        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("main", output)
        self.gdb.command(f"delete {mainbp}")
        self.gdb.watch("counter == 5")
        # Watchpoint hits when counter becomes 5.
        output = self.gdb.c()
        assertEqual(self.gdb.p("counter"), 5)
        # Watchpoint hits when counter no longer is 5.
        output = self.gdb.c()
        assertEqual(self.gdb.p("counter"), 6)
        # The watchpoint is going out of scope
        output = self.gdb.c()
        assertIn("Watchpoint", output)
        assertIn("deleted", output)
        self.exit()

class ProgramSwWatchpoint(ProgramTest):
    def test(self):
        self.gdb.b("main")
        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("main", output)
        self.gdb.swatch("counter == 5")
        # The watchpoint is triggered when the expression changes
        output = self.gdb.c()
        assertIn("Watchpoint", output)
        assertIn("counter == 5", output)
        output = self.gdb.p_raw("counter")
        assertIn("5", output)
        output = self.gdb.c()
        assertIn("Watchpoint", output)
        assertIn("counter == 5", output)
        output = self.gdb.p_raw("counter")
        assertIn("6", output)
        output = self.gdb.c()
        # The watchpoint is going out of scope
        assertIn("Watchpoint", output)
        assertIn("deleted", output)
        self.exit()

class DebugTest(GdbSingleHartTest):
    # Include malloc so that gdb can make function calls. I suspect this malloc
    # will silently blow through the memory set aside for it, so be careful.
    compile_args = ("programs/debug.c", "programs/checksum.c",
            "programs/tiny-malloc.c", "-DDEFINE_MALLOC", "-DDEFINE_FREE")

    def setup(self):
        self.gdb.load()
        self.gdb.b("_exit")

    def exit(self, expected_result=0xc86455d4):
        super().exit(expected_result)

class DebugCompareSections(DebugTest):
    def test(self):
        output = self.gdb.command("compare-sections", ops=10)
        matched = 0
        for line in output.splitlines():
            if line.startswith("Section"):
                assert line.endswith("matched.")
                matched += 1
        assertGreater(matched, 1)

class DebugFunctionCall(DebugTest):
    def test(self):
        self.gdb.b("main:start")
        self.gdb.c()
        assertEqual(self.gdb.p('fib(6)', ops=10), 8)
        assertEqual(self.gdb.p('fib(7)', ops=10), 13)
        self.exit()

class DebugChangeString(DebugTest):
    def test(self):
        text = "This little piggy went to the market."
        self.gdb.b("main:start")
        self.gdb.c()
        self.gdb.p(f'fox = "{text}"')
        self.exit(0x43b497b8)

class DebugTurbostep(DebugTest):
    def test(self):
        """Single step a bunch of times."""
        self.gdb.b("main:start")
        self.gdb.c()
        self.gdb.command("p i=0")
        last_pc = None
        advances = 0
        jumps = 0
        start = time.time()
        count = 10
        for _ in range(count):
            self.gdb.stepi()
            pc = self.gdb.p("$pc")
            assertNotEqual(last_pc, pc)
            if last_pc and pc > last_pc and pc - last_pc <= 4:
                advances += 1
            else:
                jumps += 1
            last_pc = pc
        end = time.time()
        print(f"{(end - start) / count:.2f} seconds/step")
        # Some basic sanity that we're not running between breakpoints or
        # something.
        assertGreater(jumps, 1)
        assertGreater(advances, 5)

class DebugExit(DebugTest):
    def test(self):
        self.exit()

class DebugSymbols(DebugTest):
    def test(self):
        bp = self.gdb.b("main")
        output = self.gdb.c()
        assertIn(", main ", output)
        self.gdb.command(f"delete {bp}")
        bp = self.gdb.b("rot13")
        output = self.gdb.c()
        assertIn(", rot13 ", output)
        self.gdb.command(f"delete {bp}")

class DebugBreakpoint(DebugTest):
    def test(self):
        self.gdb.b("rot13")
        # The breakpoint should be hit exactly 2 times.
        for _ in range(2):
            output = self.gdb.c()
            self.gdb.p("$pc")
            assertIn("Breakpoint ", output)
            assertIn("rot13 ", output)
        self.exit()

class Hwbp1(DebugTest):
    def early_applicable(self):
        return self.hart.instruction_hardware_breakpoint_count > 0

    def test(self):
        if not self.hart.honors_tdata1_hmode:
            # Run to main before setting the breakpoint, because startup code
            # will otherwise clear the trigger that we set.
            self.gdb.b("main")
            self.gdb.c()

        self.gdb.command("delete")
        self.gdb.hbreak("rot13")
        # The breakpoint should be hit exactly 2 times.
        for _ in range(2):
            output = self.gdb.c()
            self.gdb.p("$pc")
            assertRegex(output, r"[bB]reakpoint")
            assertIn("rot13 ", output)
        self.gdb.b("_exit")
        self.exit()

def MCONTROL_TYPE(xlen):
    return 0xf<<((xlen)-4)
def MCONTROL_DMODE(xlen):
    return 1<<((xlen)-5)
def MCONTROL_MASKMAX(xlen):
    return 0x3<<((xlen)-11)

MCONTROL_SELECT = (1<<19)
MCONTROL_TIMING = (1<<18)
MCONTROL_ACTION = (0x3f<<12)
MCONTROL_CHAIN = (1<<11)
MCONTROL_MATCH = (0xf<<7)
MCONTROL_M = (1<<6)
MCONTROL_H = (1<<5)
MCONTROL_S = (1<<4)
MCONTROL_U = (1<<3)
MCONTROL_EXECUTE = (1<<2)
MCONTROL_STORE = (1<<1)
MCONTROL_LOAD = (1<<0)

MCONTROL_TYPE_NONE = 0
MCONTROL_TYPE_MATCH = 2

MCONTROL_ACTION_DEBUG_EXCEPTION = 0
MCONTROL_ACTION_DEBUG_MODE = 1
MCONTROL_ACTION_TRACE_START = 2
MCONTROL_ACTION_TRACE_STOP = 3
MCONTROL_ACTION_TRACE_EMIT = 4

MCONTROL_MATCH_EQUAL = 0
MCONTROL_MATCH_NAPOT = 1
MCONTROL_MATCH_GE = 2
MCONTROL_MATCH_LT = 3
MCONTROL_MATCH_MASK_LOW = 4
MCONTROL_MATCH_MASK_HIGH = 5

def set_field(reg, mask, val):
    return ((reg) & ~(mask)) | (((val) * ((mask) & ~((mask) << 1))) & (mask))

class HwbpManual(DebugTest):
    """Make sure OpenOCD behaves "normal" when the user sets a trigger by
    writing the trigger registers themselves directly."""
    def early_applicable(self):
        return self.target.support_manual_hwbp and \
            self.hart.instruction_hardware_breakpoint_count >= 1

    def test(self):
        if not self.hart.honors_tdata1_hmode:
            # Run to main before setting the breakpoint, because startup code
            # will otherwise clear the trigger that we set.
            self.gdb.b("main")
            self.gdb.c()

        self.gdb.command("delete")
        #self.gdb.hbreak("rot13")
        tdata1 = MCONTROL_DMODE(self.hart.xlen)
        tdata1 = set_field(tdata1, MCONTROL_ACTION, MCONTROL_ACTION_DEBUG_MODE)
        tdata1 = set_field(tdata1, MCONTROL_MATCH, MCONTROL_MATCH_EQUAL)
        tdata1 |= MCONTROL_M | MCONTROL_S | MCONTROL_U | MCONTROL_EXECUTE

        tselect = 0
        while True:
            self.gdb.p(f"$tselect={tselect}")
            value = self.gdb.p("$tselect")
            if value != tselect:
                raise TestNotApplicable
            self.gdb.p(f"$tdata1=0x{tdata1:x}")
            value = self.gdb.p("$tselect")
            if value == tdata1:
                break
            self.gdb.p("$tdata1=0")
            tselect += 1

        self.gdb.p("$tdata2=&rot13")
        # The breakpoint should be hit exactly 2 times.
        for _ in range(2):
            output = self.gdb.c(ops=2)
            self.gdb.p("$pc")
            assertRegex(output, r"[bB]reakpoint")
            assertIn("rot13 ", output)
        self.gdb.p("$tdata2=&crc32a")
        self.gdb.c()
        before = self.gdb.p("$pc")
        assertEqual(before, self.gdb.p("&crc32a"))
        self.gdb.stepi()
        after = self.gdb.p("$pc")
        assertNotEqual(before, after)

        self.gdb.b("_exit")
        self.exit()


class Hwbp2(DebugTest):
    def early_applicable(self):
        return self.hart.instruction_hardware_breakpoint_count >= 2

    def test(self):
        self.gdb.command("delete")
        self.gdb.hbreak("main")
        self.gdb.hbreak("rot13")
        # We should hit 3 breakpoints.
        for expected in ("main", "rot13", "rot13"):
            output = self.gdb.c()
            self.gdb.p("$pc")
            assertRegex(output, r"[bB]reakpoint")
            assertIn(f"{expected} ", output)
        self.gdb.command("delete")
        self.gdb.b("_exit")
        self.exit()

class TooManyHwbp(DebugTest):
    def test(self):
        for i in range(30):
            self.gdb.hbreak(f"*rot13 + {i * 4}")

        output = self.gdb.c(checkOutput=False)
        assertIn("Cannot insert hardware breakpoint", output)
        # There used to be a bug where this would fail if done twice in a row.
        output = self.gdb.c(checkOutput=False)
        assertIn("Cannot insert hardware breakpoint", output)
        # Clean up, otherwise the hardware breakpoints stay set and future
        # tests may fail.
        self.gdb.command("delete")
        self.gdb.b("_exit")
        self.exit()

class Registers(DebugTest):
    def test(self):
        # Get to a point in the code where some registers have actually been
        # used.
        self.gdb.b("rot13")
        self.gdb.c()
        self.gdb.c()
        # Try both forms to test gdb.
        for cmd in ("info all-registers", "info registers all"):
            output = self.gdb.command(cmd, ops=20)
            for reg in ('zero', 'ra', 'sp', 'gp', 'tp'):
                assertIn(reg, output)
            for line in output.splitlines():
                assertRegex(line, r"^\S")

        #TODO
        # mcpuid is one of the few registers that should have the high bit set
        # (for rv64).
        # Leave this commented out until gdb and spike agree on the encoding of
        # mcpuid (which is going to be renamed to misa in any case).
        #assertRegex(output, ".*mcpuid *0x80")

        #TODO:
        # The instret register should always be changing.
        #last_instret = None
        #for _ in range(5):
        #    instret = self.gdb.p("$instret")
        #    assertNotEqual(instret, last_instret)
        #    last_instret = instret
        #    self.gdb.stepi()

        self.exit()

class UserInterrupt(DebugTest):
    def test(self):
        """Sending gdb ^C while the program is running should cause it to
        halt."""
        self.gdb.b("main:start")
        self.gdb.c()
        self.gdb.p("i=123")
        self.gdb.c(wait=False)
        time.sleep(2)
        output = self.gdb.interrupt()
        assert "main" in output
        assertGreater(self.gdb.p("j"), 10)
        self.gdb.p("i=0")
        self.exit()

class MemorySampleTest(DebugTest):
    def early_applicable(self):
        return self.target.support_memory_sampling

    def setup(self):
        DebugTest.setup(self)
        self.gdb.b("main:start")
        self.gdb.c()
        self.gdb.p("i=123")

    @staticmethod
    def check_incrementing_samples(raw_samples, check_addr,
                                   tolerance=0x200000):
        first_timestamp = None
        end = None
        total_samples = 0
        previous_value = None
        for line in raw_samples.splitlines():
            m = re.match(r"^timestamp \w+: (\d+)", line)
            if m:
                timestamp = int(m.group(1))
                if not first_timestamp:
                    first_timestamp = timestamp
                else:
                    end = (timestamp, total_samples)
            else:
                assertRegex(line, r"^0x[0-f]+: 0x[0-f]+$")
                address, value = line.split(': ')
                address = int(address, 16)
                if address == check_addr:
                    value = int(value, 16)
                    if not previous_value is None:
                        # TODO: what if the counter wraps?
                        assertGreater(value, previous_value)
                        assertLess(value, previous_value + tolerance)
                    previous_value = value
                total_samples += 1
        if end and total_samples > 0:
            samples_per_second = 1000 * end[1] / (end[0] - first_timestamp)
            print(f"{samples_per_second} samples/second")
        else:
            raise Exception("No samples collected.")

    @staticmethod
    def check_samples_equal(raw_samples, check_addr, check_value):
        total_samples = 0
        for line in raw_samples.splitlines():
            if not line.startswith("timestamp "):
                address, value = line.split(': ')
                address = int(address, 16)
                if address == check_addr:
                    value = int(value, 16)
                    assertEqual(value, check_value)
                    total_samples += 1
        assertGreater(total_samples, 0)

    def collect_samples(self):
        self.gdb.c(wait=False)
        time.sleep(5)
        output = self.gdb.interrupt()
        assert "main" in output
        return self.gdb.command("monitor riscv dump_sample_buf", ops=5)

class MemorySampleSingle(MemorySampleTest):
    def test(self):
        addr = self.gdb.p("&j")
        sizeof_j = self.gdb.p("sizeof(j)")
        self.gdb.command(f"monitor riscv memory_sample 0 0x{addr:x} {sizeof_j}")

        raw_samples = self.collect_samples()
        self.check_incrementing_samples(raw_samples, addr, tolerance=0x500000)

        # Buffer should have been emptied by dumping.
        raw_samples = self.gdb.command("monitor riscv dump_sample_buf", ops=5)
        assertEqual(len(raw_samples), 0)

class MemorySampleMixed(MemorySampleTest):
    def test(self):
        addr = {}
        test_vars = ["j", "i32"]
        if self.hart.xlen >= 64:
            test_vars.append("i64")
        for i, name in enumerate(test_vars):
            addr[name] = self.gdb.p(f"&{name}")
            sizeof = self.gdb.p(f"sizeof({name})")
            self.gdb.command(f"monitor riscv memory_sample {i} "
                             f"0x{addr[name]:x} {sizeof}")

        raw_samples = self.collect_samples()
        self.check_incrementing_samples(raw_samples, addr["j"],
                                        tolerance=0x500000)
        self.check_samples_equal(raw_samples, addr["i32"], 0xdeadbeef)
        if self.hart.xlen >= 64:
            self.check_samples_equal(raw_samples, addr["i64"],
                                     0x1122334455667788)

class RepeatReadTest(DebugTest):
    def early_applicable(self):
        return self.target.supports_clint_mtime

    def test(self):
        self.gdb.b("main:start")
        self.gdb.c()
        mtime_addr = 0x02000000 + 0xbff8
        count = 1024
        output = self.gdb.command(
            f"monitor riscv repeat_read {count} 0x{mtime_addr:x} 4")
        values = []
        for line in output.splitlines():
            # Ignore warnings
            if line.startswith("Batch memory"):
                continue
            for v in line.split():
                values.append(int(v, 16))

        assertEqual(len(values), count)
        # mtime should only ever increase, unless it wraps
        slop = 0x100000
        for i in range(1, len(values)):
            if values[i] < values[i-1]:
                # wrapped
                assertLess(values[i], slop)
            else:
                assertGreater(values[i], values[i-1])
                assertLess(values[i], values[i-1] + slop)

        output = self.gdb.command(
            f"monitor riscv repeat_read 0 0x{mtime_addr:x} 4")
        assertEqual(output, "")

class Semihosting(GdbSingleHartTest):
    # Include malloc so that gdb can assign a string.
    compile_args = ("programs/semihosting.c", "programs/tiny-malloc.c",
                    "-DDEFINE_MALLOC", "-DDEFINE_FREE")

    def early_applicable(self):
        return self.target.test_semihosting

    def setup(self):
        self.gdb.load()
        self.parkOtherHarts()
        self.gdb.b("_exit")

    def test(self):
        with tempfile.NamedTemporaryFile(suffix=".data") as temp:
            self.gdb.b("main:begin")
            self.gdb.c()
            self.gdb.p(f'filename="{temp.name}"', ops=3)
            self.exit()

            with open(temp.name, "r", encoding='utf-8') as fd:
                contents = fd.readlines()

        assertIn("Hello, world!\n", contents)

        # stdout should end up in the OpenOCD log
        with open(self.server.logname, "r", encoding='utf-8') as fd:
            log = fd.read()
        assertIn("Do re mi fa so la ti do!", log)

class SemihostingFileio(Semihosting):
    def early_applicable(self):
        # Semihosting file i/o doesn't work right when there are multiple harts
        # in SMP mode, and the semihosting call comes from a hart other than the
        # first one.
        # The problem is that semihosting_common_fileio_info() is called only
        # for the first target in an SMP list. Either the caller needs to be
        # made aware of SMP targets, or that function needs to walk the list
        # itself. (Or maybe we need to make a separate function just for RISC-V
        # that does that.)
        return len(self.target.harts) == 1

    def setup(self):
        self.gdb.command("monitor foreach t [target names] { "
            "targets $t; arm semihosting_fileio enable }")
        super().setup()

    def test(self):
        with tempfile.NamedTemporaryFile(suffix=".data") as temp:
            self.gdb.b("main:begin")
            self.gdb.c()
            self.gdb.p(f'filename="{temp.name}"', ops=3)
            output = self.exit()
            # stdout should end up in gdb's CLI
            assertIn("Do re mi fa so la ti do!", output)

            with open(temp.name, "r", encoding='utf-8') as fd:
                contents = fd.readlines()
        assertIn("Hello, world!\n", contents)

class InterruptTest(GdbSingleHartTest):
    compile_args = ("programs/interrupt.c",)

    def early_applicable(self):
        return self.target.supports_clint_mtime

    def setup(self):
        self.gdb.load()

    def test(self):
        self.gdb.b("main")
        output = self.gdb.c()
        assertIn(" main ", output)
        self.gdb.b("trap_entry")
        output = self.gdb.c()
        assertIn(" trap_entry ", output)
        assertEqual(self.gdb.p("$mip") & 0x80, 0x80)
        assertEqual(self.gdb.p("interrupt_count"), 0)
        # You'd expect local to still be 0, but it looks like spike doesn't
        # jump to the interrupt handler immediately after the write to
        # mtimecmp.
        assertLess(self.gdb.p("local"), 1000)
        self.gdb.command("delete breakpoints")
        for _ in range(10):
            self.gdb.c(wait=False)
            time.sleep(2)
            self.gdb.interrupt()
            interrupt_count = self.gdb.p("interrupt_count")
            local = self.gdb.p("local")
            if interrupt_count > 1000 and \
                    local > 1000:
                return

        assertGreater(interrupt_count, 1000)
        assertGreater(local, 1000)

    def postMortem(self):
        GdbSingleHartTest.postMortem(self)
        self.gdb.p("*((long long*) 0x200bff8)")
        self.gdb.p("*((long long*) 0x2004000)")
        self.gdb.p("interrupt_count")
        self.gdb.p("local")

class MulticoreRegTest(GdbTest):
    compile_args = ("programs/infinite_loop.S", "-DMULTICORE")

    def early_applicable(self):
        return len(self.target.harts) > 1

    def setup(self):
        self.gdb.load()
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            self.gdb.p("$pc=_start")

    def test(self):
        # We use time instead of breakpoints, because otherwise we can't
        # guarantee that every hart runs all the way through the loop. (The
        # problem is that we can't guarantee resuming at the same time, so the
        # first hart that is resumed will hit a breakpoint at the end of the
        # loop before another hart has executed the whole loop.)

        # Run through the whole loop.
        self.gdb.c_all(wait=False)
        time.sleep(1)
        self.gdb.interrupt_all()

        hart_ids = set()
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            assertIn("main_end", self.gdb.where())
            # Check register values.
            x1 = self.gdb.p("$x1")
            hart_id = self.gdb.p("$mhartid")
            assertEqual(x1, hart_id << 8)
            assertNotIn((hart.system, hart_id), hart_ids)
            hart_ids.add((hart.system, hart_id))
            for n in range(2, 32):
                value = self.gdb.p(f"$x{n}")
                assertEqual(value, (hart_id << 8) + n - 1)

        # Confirmed that we read different register values for different harts.
        # Write a new value to x1, and run through the add sequence again.

        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            self.gdb.p(f"$x1=0x{hart.index * 4096:x}")
            self.gdb.p("$pc=main_post_csrr")

        # Run through the whole loop.
        self.gdb.c_all(wait=False)
        time.sleep(1)
        self.gdb.interrupt_all()

        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            assertIn("main_end", self.gdb.where())
            # Check register values.
            for n in range(1, 32):
                value = self.gdb.p(f"$x{n}")
                assertEqual(value, hart.index * 0x1000 + n - 1)

#class MulticoreRunHaltStepiTest(GdbTest):
#    compile_args = ("programs/multicore.c", "-DMULTICORE")
#
#    def early_applicable(self):
#        return len(self.target.harts) > 1
#
#    def setup(self):
#        self.gdb.load()
#        for hart in self.target.harts:
#            self.gdb.select_hart(hart)
#            self.gdb.p("$mhartid")
#            self.gdb.p("$pc=_start")
#
#    def test(self):
#        previous_hart_count = [0 for h in self.target.harts]
#        previous_interrupt_count = [0 for h in self.target.harts]
#        # Check 10 times
#        for i in range(10):
#            # 3 attempts for each time we want the check to pass
#            for attempt in range(3):
#                self.gdb.global_command("echo round %d attempt %d\\n" % (i,
#                    attempt))
#                self.gdb.c_all(wait=False)
#                time.sleep(2)
#                self.gdb.interrupt_all()
#                hart_count = self.gdb.p("hart_count")
#                interrupt_count = self.gdb.p("interrupt_count")
#                ok = True
#                for i, h in enumerate(self.target.harts):
#                    if hart_count[i] <= previous_hart_count[i]:
#                        ok = False
#                        break
#                    if interrupt_count[i] <= previous_interrupt_count[i]:
#                        ok = False
#                        break
#                    self.gdb.p("$mie")
#                    self.gdb.p("$mip")
#                    self.gdb.p("$mstatus")
#                    self.gdb.p("$priv")
#                    self.gdb.p("buf", fmt="")
#                    self.gdb.select_hart(h)
#                    pc = self.gdb.p("$pc")
#                    self.gdb.stepi()
#                    stepped_pc = self.gdb.p("$pc")
#                    assertNotEqual(pc, stepped_pc)
#                previous_hart_count = hart_count
#                previous_interrupt_count = interrupt_count
#                if ok:
#                    break
#            else:
#                assert False, \
#                        "hart count or interrupt didn't increment as expected"

class MulticoreRunAllHaltOne(GdbTest):
    compile_args = ("programs/multicore.c", "-DMULTICORE")

    def early_applicable(self):
        return len(self.target.harts) > 1

    def setup(self):
        self.gdb.select_hart(self.target.harts[0])
        self.gdb.load()
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            self.gdb.p("$pc=_start")

    def test(self):
        if not self.gdb.one_hart_per_gdb():
            raise TestNotApplicable

        # Run harts in reverse order
        for h in reversed(self.target.harts):
            self.gdb.select_hart(h)
            self.gdb.c(wait=False)

        self.gdb.interrupt()
        # Give OpenOCD time to call poll() on both harts, which is what causes
        # the bug.
        time.sleep(1)
        self.gdb.p("buf", fmt="")

class MulticoreRtosSwitchActiveHartTest(GdbTest):
    compile_args = ("programs/multicore.c", "-DMULTICORE")

    def early_applicable(self):
        return len(self.target.harts) > 1

    def setup(self):
        self.gdb.select_hart(self.target.harts[0])
        self.gdb.load()
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            self.gdb.p("$pc=_start")

    def test(self):
        if self.gdb.one_hart_per_gdb():
            raise TestNotApplicable

        # Set breakpoint near '_start' label to increase the chances of a
        # situation when all harts hit breakpoint immediately and
        # simultaneously.
        self.gdb.b("set_trap_handler")

        # Check that all harts hit breakpoint one by one.
        for _ in range(len(self.target.harts)):
            output = self.gdb.c()
            assertIn("hit Breakpoint", output)
            assertIn("set_trap_handler", output)
            assertNotIn("received signal SIGTRAP", output)

class SmpSimultaneousRunHalt(GdbTest):
    compile_args = ("programs/run_halt_timing.S", "-DMULTICORE")

    def early_applicable(self):
        return len(self.target.harts) > 1 and self.target.support_hasel

    def setup(self):
        self.gdb.select_hart(self.target.harts[0])
        self.gdb.load()
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            self.gdb.p("$pc=_start")

    def test(self):
        if self.gdb.one_hart_per_gdb() or not self.server.smp():
            raise TestNotApplicable

        old_mtime = set()
        for _ in range(5):
            self.gdb.c_all(wait=False)
            time.sleep(2)
            self.gdb.interrupt_all()

            mtime_value = []
            counter = []
            for hart in self.target.harts:
                self.gdb.select_hart(hart)
                mv = self.gdb.p("$s2")
                assertNotIn(mv, old_mtime,
                        "mtime doesn't appear to be changing at all")
                mtime_value.append(mv)
                c = self.gdb.p("$s0")
                assertNotEqual(c, 0,
                        "counter didn't increment; code didn't run?")
                counter.append(c)
                # Reset the counter for the next round.
                self.gdb.p("$s0=0")

            old_mtime.update(mtime_value)

            mtime_spread = max(mtime_value) - min(mtime_value)
            print("mtime_spread:", mtime_spread)
            counter_spread = max(counter) - min(counter)
            print("counter_spread:", counter_spread)

            assertLess(mtime_spread, 101 * (len(self.target.harts) - 1),
                    "Harts don't halt around the same time.")
            # spike executes normal code 5000 instructions at a time, so we
            # expect 5k instructions to be executed on one hart before the
            # other gets to go. Our loop (unoptimized) is quite a few
            # instructions, but allow for 5k anyway.
            assertLess(counter_spread, 5001 * (len(self.target.harts) - 1),
                    "Harts don't resume around the same time.")

class StepTest(GdbSingleHartTest):
    compile_args = ("programs/step.S", )

    def setup(self):
        self.gdb.load()
        self.gdb.b("main")
        self.gdb.c()

    def test(self):
        main_address = self.gdb.p("$pc")
        if self.hart.extensionSupported("c"):
            sequence = (4, 8, 0xc, 0xe, 0x14, 0x18, 0x22, 0x1c, 0x24, 0x24)
        else:
            sequence = (4, 8, 0xc, 0x10, 0x18, 0x1c, 0x28, 0x20, 0x2c, 0x2c)
        for expected in sequence:
            self.gdb.stepi()
            pc = self.gdb.p("$pc")
            assertEqual(f"{pc - main_address:x}", f"{expected:x}")

class JumpHbreak(GdbSingleHartTest):
    """'jump' resumes execution at location. Execution stops again immediately
    if there is a breakpoint there.
    That second line can be trouble."""
    compile_args = ("programs/trigger.S", )

    def early_applicable(self):
        return self.hart.instruction_hardware_breakpoint_count >= 1

    def setup(self):
        self.gdb.load()
        self.gdb.hbreak("main")
        self.gdb.c()
        self.gdb.command("delete 1")

    def test(self):
        self.gdb.b("read_loop")
        self.gdb.command("hbreak just_before_read_loop")
        output = self.gdb.command("jump just_before_read_loop")
        assertRegex(output, r"Breakpoint \d, just_before_read_loop ")
        output = self.gdb.c()
        assertRegex(output, r"Breakpoint \d, read_loop ")

class TriggerTest(GdbSingleHartTest):
    compile_args = ("programs/trigger.S", )
    def setup(self):
        self.gdb.load()
        self.gdb.b("main")
        self.gdb.c()
        self.gdb.command("delete")

class TriggerExecuteInstant(TriggerTest):
    """Test an execute breakpoint on the first instruction executed out of
    debug mode."""
    def test(self):
        main_address = self.gdb.p("$pc")
        self.gdb.command(f"hbreak *0x{main_address + 4:x}")
        self.gdb.c()
        assertEqual(self.gdb.p("$pc"), main_address+4)

# FIXME: Triggers aren't quite working yet
#class TriggerLoadAddress(TriggerTest):
#    def test(self):
#        self.gdb.command("rwatch *((&data)+1)")
#        output = self.gdb.c()
#        assertIn("read_loop", output)
#        assertEqual(self.gdb.p("$a0"),
#                self.gdb.p("(&data)+1"))
#        self.exit()

class TriggerLoadAddressInstant(TriggerTest):
    """Test a load address breakpoint on the first instruction executed out of
    debug mode."""
    def test(self):
        self.gdb.command("b just_before_read_loop")
        self.gdb.c()
        read_loop = self.gdb.p("&read_loop")
        read_again = self.gdb.p("&read_again")
        data = self.gdb.p("&data")
        self.gdb.command(f"rwatch *0x{data:x}")
        self.gdb.c()
        # Accept hitting the breakpoint before or after the load instruction.
        assertIn(self.gdb.p("$pc"), [read_loop, read_loop + 4])
        assertEqual(self.gdb.p("$a0"), self.gdb.p("&data"))

        self.gdb.c()
        assertIn(self.gdb.p("$pc"), [read_again, read_again + 4])
        assertEqual(self.gdb.p("$a0"), self.gdb.p("&data"))

# FIXME: Triggers aren't quite working yet
#class TriggerStoreAddress(TriggerTest):
#    def test(self):
#        self.gdb.command("watch *((&data)+3)")
#        output = self.gdb.c()
#        assertIn("write_loop", output)
#        assertEqual(self.gdb.p("$a0"),
#                self.gdb.p("(&data)+3"))
#        self.exit()

class TriggerStoreAddressInstant(TriggerTest):
    def test(self):
        """Test a store address breakpoint on the first instruction executed out
        of debug mode."""
        self.gdb.command("b just_before_write_loop")
        self.gdb.c()
        write_loop = self.gdb.p("&write_loop")
        data = self.gdb.p("&data")
        self.gdb.command(f"watch *0x{data:x}")
        self.gdb.c()

        # Accept hitting the breakpoint before or after the store instruction.
        assertIn(self.gdb.p("$pc"), [write_loop, write_loop + 4])
        assertEqual(self.gdb.p("$a0"), self.gdb.p("&data"))

class TriggerDmode(TriggerTest):
    def early_applicable(self):
        return self.hart.honors_tdata1_hmode and \
                self.hart.instruction_hardware_breakpoint_count > 0

    def check_triggers(self, tdata1_lsbs, tdata2):
        dmode = 1 << (self.hart.xlen-5)

        triggers = []

        if self.hart.xlen == 32:
            xlen_type = 'int'
        elif self.hart.xlen == 64:
            xlen_type = 'long long'
        else:
            raise NotImplementedError

        dmode_count = 0
        i = 0
        for i in range(16):
            tdata1 = self.gdb.p(f"(({xlen_type} *)&data)[{2*i}]")
            if tdata1 == 0:
                break
            tdata2 = self.gdb.p(f"(({xlen_type} *)&data)[{2*i+1}]")

            if tdata1 & dmode:
                dmode_count += 1
            else:
                assertEqual(tdata1 & 0xffff, tdata1_lsbs)
                assertEqual(tdata2, tdata2)

        assertGreater(i, 1)
        assertEqual(dmode_count, 1)

        return triggers

    def test(self):
        # If we want this test to run from flash, we can't have any software
        # breakpoints set.

        self.gdb.command("hbreak write_load_trigger")
        self.gdb.p("$pc=write_store_trigger")
        output = self.gdb.c()
        assertIn("write_load_trigger", output)
        self.check_triggers((1<<6) | (1<<1), 0xdeadbee0)
        self.gdb.command("delete")
        self.gdb.command("hbreak clear_triggers")
        output = self.gdb.c()
        assertIn("clear_triggers", output)
        self.check_triggers((1<<6) | (1<<0), 0xfeedac00)
        self.gdb.command("delete")
        self.exit()

class RegsTest(GdbSingleHartTest):
    compile_args = ("programs/regs.S", )
    def setup(self):
        self.gdb.load()
        main_bp = self.gdb.b("main")
        output = self.gdb.c()
        assertIn("Breakpoint ", output)
        assertIn("main", output)
        self.gdb.command(f"delete {main_bp}")
        self.gdb.b("handle_trap")

class WriteGprs(RegsTest):
    def test(self):
        if self.hart.extensionSupported('E'):
            regs = [(f"x{n}") for n in range(2, 16)]
        else:
            regs = [(f"x{n}") for n in range(2, 32)]

        self.gdb.p("$pc=write_regs")
        for i, r in enumerate(regs):
            self.gdb.p(f"${r}={(0xdeadbeef<<i)+17}")
        self.gdb.p("$x1=&data")
        self.gdb.command("b all_done")
        output = self.gdb.c()
        assertIn("Breakpoint ", output)

        # Just to get this data in the log.
        self.gdb.command("x/30gx &data")
        self.gdb.command("info registers")
        for n in range(len(regs)):
            assertEqual(self.gdb.x(f"(char*)(&data)+{8*n}", 'g'),
                    ((0xdeadbeef<<n)+17) & ((1<<self.hart.xlen)-1))

class WriteCsrs(RegsTest):
    def test(self):
        # As much a test of gdb as of the simulator.
        self.gdb.p("$mscratch=0")
        self.gdb.stepi()
        assertEqual(self.gdb.p("$mscratch"), 0)
        self.gdb.p("$mscratch=123")
        self.gdb.stepi()
        assertEqual(self.gdb.p("$mscratch"), 123)

        self.gdb.p("$pc=write_regs")
        self.gdb.p("$x1=&data")
        self.gdb.command("b all_done")
        self.gdb.command("c")

        assertEqual(123, self.gdb.p("$mscratch"))
        assertEqual(123, self.gdb.p("$x1"))
        assertEqual(123, self.gdb.p("$csr832"))

class DownloadTest(GdbTest):
    compile_args = ("programs/infinite_loop.S", )

    def setup(self):
        # pylint: disable=attribute-defined-outside-init
        length = min(2**18, max(2**10, self.hart.ram_size - 2048))
        # TODO: remove the next line so we get a bit more code to download. The
        # line above that allows for more data runs into some error I don't
        # have time to track down right now.
        #length = min(2**14, max(2**10, self.hart.ram_size - 2048))
        # pylint: disable-next=consider-using-with
        self.download_c = tempfile.NamedTemporaryFile(prefix="download_",
                suffix=".c", delete=False)
        self.download_c.write(b"#include <stdint.h>\n")
        self.download_c.write(
                b"unsigned int crc32a(uint8_t *message, unsigned int size);\n")
        self.download_c.write(b"const uint32_t length = %d;\n" % length)
        self.download_c.write(b"const uint8_t d[%d] = {\n" % length)
        self.crc = 0
        assert length % 16 == 0
        for i in range(length // 16):
            self.download_c.write(f"  /* 0x{i * 16:04x} */ ".encode())
            for _ in range(16):
                value = random.randrange(1<<8)
                self.download_c.write(f"0x{value:02x}, ".encode())
                self.crc = binascii.crc32(struct.pack("B", value), self.crc)
            self.download_c.write(b"\n")
        self.download_c.write(b"};\n")
        self.download_c.write(b"uint8_t *data = &d[0];\n")
        self.download_c.write(
                b"uint32_t main() { return crc32a(data, length); }\n")
        self.download_c.flush()

        if self.crc < 0:
            self.crc += 2**32

        compiled = {}
        for hart in self.target.harts:
            key = hart.system
            if key not in compiled:
                compiled[key] = self.target.compile(hart, self.download_c.name,
                        "programs/checksum.c")
            self.gdb.select_hart(hart)
            self.gdb.command(f"file {compiled.get(key)}")

        self.gdb.select_hart(self.hart)

    def test(self):
        self.gdb.load()
        self.parkOtherHarts()
        self.gdb.command("b _exit")
        #self.gdb.c(ops=100)
        self.gdb.c()
        assertEqual(self.gdb.p("status"), self.crc)
        os.unlink(self.download_c.name)

#class MprvTest(GdbSingleHartTest):
#    compile_args = ("programs/mprv.S", )
#    def setup(self):
#        self.gdb.load()
#
#    def test(self):
#        """Test that the debugger can access memory when MPRV is set."""
#        self.gdb.c(wait=False)
#        time.sleep(0.5)
#        self.gdb.interrupt()
#        output = self.gdb.command("p/x *(int*)(((char*)&data)-0x80000000)")
#        assertIn("0xbead", output)

class PrivTest(GdbSingleHartTest):
    compile_args = ("programs/priv.S", )
    def setup(self):
        # pylint: disable=attribute-defined-outside-init
        self.gdb.load()

        misa = self.hart.misa
        self.supported = set()
        if misa & (1<<20):
            self.supported.add(0)
        if misa & (1<<18):
            self.supported.add(1)
        if misa & (1<<7):
            self.supported.add(2)
        self.supported.add(3)

        self.disable_pmp()

        # Ensure Virtual Memory is disabled if applicable (SATP register is not
        # reset)
        try:
            self.gdb.p("$satp=0")
        except testlib.CouldNotFetch:
            # SATP only exists if you have S mode.
            pass

class PrivRw(PrivTest):
    def test(self):
        """Test reading/writing priv."""
        self.write_nop_program(4)
        for privilege in range(4):
            self.gdb.p(f"$priv={privilege}")
            self.gdb.stepi()
            actual = self.gdb.p("$priv")
            assertIn(actual, self.supported)
            if privilege in self.supported:
                assertEqual(actual, privilege)

class PrivChange(PrivTest):
    def test(self):
        """Test that the core's privilege level actually changes."""

        if 0 not in self.supported:
            raise TestNotApplicable

        self.gdb.b("main")
        self.gdb.c()

        # Machine mode
        self.gdb.p("$priv=3")
        main_address = self.gdb.p("$pc")
        self.gdb.stepi()
        assertEqual(f"{self.gdb.p('$pc'):x}", f"{main_address + 4:x}")

        # User mode
        self.gdb.p("$priv=0")
        self.gdb.stepi()
        # Should have taken an exception, so be at trap_entry
        pc = self.gdb.p("$pc")
        trap_entry = self.gdb.p("&trap_entry")
        assertEqual(pc, trap_entry)

class CheckMisa(GdbTest):
    """Make sure the misa we're using is actually what the target exposes."""
    def test(self):
        for hart in self.target.harts:
            self.gdb.select_hart(hart)
            misa = self.gdb.p("$misa")
            assertEqual(misa, hart.misa)

class TranslateTest(GdbSingleHartTest):
    compile_args = ("programs/translate.c", )

    def early_applicable(self):
        return self.hart.ram_size >= 32 * 1024

    def setup(self):
        self.disable_pmp()

        self.gdb.load()
        self.gdb.b("main")
        output = self.gdb.c()
        assertRegex(output, r"\bmain\b")

    def check_satp(self, mode):
        if self.hart.xlen == 32:
            satp = mode << 31
        else:
            satp = mode << 60
        try:
            self.gdb.p(f"$satp=0x{satp:x}")
        except testlib.CouldNotFetch as cnf:
            raise TestNotApplicable from cnf
        readback = self.gdb.p("$satp")
        self.gdb.p("$satp=0")
        if readback != satp:
            raise TestNotApplicable

    def test_translation(self):
        self.gdb.b("error")
        self.gdb.b("handle_trap")
        self.gdb.b("main:active")

        output = self.gdb.c()
        assertRegex(output, r"\bmain\b")
        assertEqual(0xdeadbeef, self.gdb.p("physical[0]"))
        assertEqual(0x55667788, self.gdb.p("physical[1]"))
        assertEqual(0xdeadbeef, self.gdb.p("virtual[0]"))
        assertEqual(0x55667788, self.gdb.p("virtual[1]"))

SATP_MODE_OFF = 0
SATP_MODE_SV32 = 1
SATP_MODE_SV39 = 8
SATP_MODE_SV48 = 9
SATP_MODE_SV57 = 10
SATP_MODE_SV64 = 11

class Sv32Test(TranslateTest):
    def early_applicable(self):
        return TranslateTest.early_applicable(self) and self.hart.xlen == 32

    def test(self):
        self.check_satp(SATP_MODE_SV32)
        self.gdb.p("vms=&sv32")
        self.test_translation()

class Sv39Test(TranslateTest):
    def early_applicable(self):
        return TranslateTest.early_applicable(self) and self.hart.xlen > 32

    def test(self):
        self.check_satp(SATP_MODE_SV39)
        self.gdb.p("vms=&sv39")
        self.test_translation()

class Sv48Test(TranslateTest):
    def early_applicable(self):
        return TranslateTest.early_applicable(self) and self.hart.xlen > 32

    def test(self):
        self.check_satp(SATP_MODE_SV48)
        self.gdb.p("vms=&sv48")
        self.test_translation()

class VectorTest(GdbSingleHartTest):
    compile_args = ("programs/vectors.S", )

    def early_applicable(self):
        if not self.hart.extensionSupported('V'):
            return False
        # If the compiler can't build this test, say it's not applicable. At
        # some time all compilers will support the V extension, but we're not
        # there yet.
        try:
            self.compile()
        except CompileError as e:
            if b"Error: unknown CSR `vlenb'" in e.stderr:
                return False
        return True

    def setup(self):
        self.gdb.load()
        self.gdb.b("main")
        self.gdb.c()

    def test(self):
        vlenb = self.gdb.p("$vlenb")
        self.gdb.command("delete")
        self.gdb.b("_exit")
        self.gdb.b("trap_entry")

        self.gdb.b("test0")

        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("test0", output)

        # I'm not convinced that writing 0 is supported on every vector
        # implementation. If this test fails, that might be why.
        for regname in ('$vl', '$vtype'):
            value = self.gdb.p(regname)
            assertNotEqual(value, 0)
            self.gdb.p(f"{regname}=0")
            self.gdb.command("flushregs")
            assertEqual(self.gdb.p(regname), 0)
            self.gdb.p(f"{regname}=0x{value:x}")
            self.gdb.command("flushregs")
            assertEqual(self.gdb.p(regname), value)

        assertEqual(self.gdb.p("$a0"), 0)
        a = self.gdb.x("&a", 'b', vlenb)
        b = self.gdb.x("&b", 'b', vlenb)
        v4 = self.gdb.p("$v4")
        assertEqual(a, b)
        assertEqual(b, v4["b"])
        assertEqual(0, self.gdb.p("$a0"))

        self.gdb.b("test1")

        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("test1", output)

        assertEqual(self.gdb.p("$a0"), 0)
        b = self.gdb.x("&b", 'b', vlenb)
        c = self.gdb.x("&c", 'b', vlenb)
        v4 = self.gdb.p("$v4")
        assertEqual(b, c)
        assertEqual(c, v4["b"])
        assertEqual(0, self.gdb.p("$a0"))

        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("_exit", output)
        assertEqual(self.gdb.p("status"), 0)

class EbreakTest(GdbSingleHartTest):
    """Test that we work correctly when somebody puts an ebreak directly into
    their code."""
    compile_args = ("programs/ebreak.c", )

    def setup(self):
        self.gdb.load()
        self.gdb.b("_exit")

    def test(self):
        # Should hit ebreak in the code.
        output = self.gdb.c()
        assertIn("ebreak", output)
        ebreak_pc = self.gdb.p("$pc")

        # Simple resume, we should hit the same ebreak again.
        output = self.gdb.c()
        assertIn("ebreak", output)
        assertEqual(ebreak_pc, self.gdb.p("$pc"))

        # Test getting past the ebreak by changing the PC.
        for _ in range(2):
            self.gdb.p("$pc=$pc+4")
            output = self.gdb.c()
            assertIn("ebreak", output)
            assertEqual(ebreak_pc, self.gdb.p("$pc"))

        self.gdb.p("$pc=$pc+4")
        output = self.gdb.c()
        assertIn("_exit", output)

class CeaseMultiTest(GdbTest):
    """Test that we work correctly when a hart ceases to respond (e.g. because
    it's powered down)."""
    compile_args = ("programs/counting_loop.c", "-DDEFINE_MALLOC",
            "-DDEFINE_FREE")

    def early_applicable(self):
        return self.hart.support_cease and len(self.target.harts) > 1

    def setup(self):
        ProgramTest.setup(self)
        self.parkOtherHarts("precease")

    def test(self):
        # Run all the way to the infinite loop in exit
        self.gdb.c(wait=False)
        self.gdb.expect(r"\S+ became unavailable.")
        self.gdb.interrupt()

        for hart in self.target.harts:
            # Try to read misa on the ceased harts
            if hart != self.hart:
                try:
                    self.gdb.select_hart(hart)
                    self.gdb.p("$misa")
                    assert False, \
                        "Shouldn't be able to access unavailable hart."
                except UnknownThread:
                    pass

        # Check that the main hart can still be debugged.
        self.gdb.select_hart(self.hart)
        main_addr = self.gdb.p("$pc=main")
        self.gdb.stepi()
        # Assume the first instruction of main is not a jump.
        pc = self.gdb.p("$pc")
        assertGreater(pc, main_addr)
        assertLess(pc, main_addr + 8)

        self.gdb.p("$pc=_start")

        self.exit()
class CeaseStepiTest(ProgramTest):
    """Test that we work correctly when the hart we're debugging ceases to
    respond."""
    def early_applicable(self):
        return self.hart.support_cease

    def test(self):
        self.gdb.b("main")
        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("main", output)

        self.gdb.p("$pc=cease")
        self.gdb.stepi(wait=False)
        self.gdb.expect(r"\S+ became unavailable.")
        self.gdb.interrupt()
        try:
            self.gdb.p("$pc")
            assert False, ("Registers shouldn't be accessible when the hart is "
                           "unavailable.")
        except CouldNotReadRegisters:
            pass

class CeaseRunTest(ProgramTest):
    """Test that we work correctly when the hart we're debugging ceases to
    respond."""
    def early_applicable(self):
        return self.hart.support_cease

    def test(self):
        self.gdb.b("main")
        output = self.gdb.c()
        assertIn("Breakpoint", output)
        assertIn("main", output)

        self.gdb.p("$pc=precease")
        self.gdb.c(wait=False)
        self.gdb.expect(r"\S+ became unavailable.")
        self.gdb.interrupt()
        try:
            self.gdb.p("$pc")
            assert False, ("Registers shouldn't be accessible when the hart is "
                           "unavailable.")
        except CouldNotReadRegisters:
            pass

class FreeRtosTest(GdbTest):
    def early_applicable(self):
        return self.target.freertos_binary

    def freertos(self):
        return True

    def test(self):
        self.gdb.command(f"file {self.target.freertos_binary}")
        self.gdb.load()

        output = self.gdb.command("monitor riscv_freertos_stacking mainline")

        # Turn off htif, which doesn't work when the file is loaded into spike
        # through gdb. It only works when spike loads the ELF file itself.
        bp = self.gdb.b("main")
        self.gdb.c()
        self.gdb.command(f"delete {bp}")
        self.gdb.p("*((int*) &use_htif) = 0")
        # Need this, otherwise gdb complains that there is no current active
        # thread.
        self.gdb.threads()

        bp = self.gdb.b("prvQueueReceiveTask")

        self.gdb.c()
        self.gdb.command(f"delete {bp}")

        bp = self.gdb.b("prvQueueSendTask")
        self.gdb.c()
        self.gdb.command(f"delete {bp}")

        # Now we know for sure at least 2 threads have executed.

        threads = self.gdb.threads()
        assertGreater(len(threads), 1)

        values = {}
        for thread in threads:
            assertNotIn("No Name", thread[1])
            self.gdb.thread(thread)
            assertEqual(self.gdb.p("$zero"), 0)
            output = self.gdb.command("info reg sp")
            assertIn("ucHeap", output)
            self.gdb.command("info reg mstatus")
            values[thread.id] = self.gdb.p("$s11")
            self.gdb.p(f"$s11=0x{values[thread.id] ^ int(thread.id):x}")

        # Test that writing worked
        self.gdb.stepi()
        for thread in self.gdb.threads():
            self.gdb.thread(thread)
            assertEqual(self.gdb.p("$s11"), values[thread.id] ^ int(thread.id))

class StepThread2Test(GdbTest):
    # Check that we can do stepi on thread 2 without GDB switching to thread 1.
    # There was a bug where this could happen, because OpenOCD was mistakenly
    # omitting a thread ID in its stop reply.  This was addressed in OpenOCD,
    # but if there is a regression in the future, this test should catch it)

    def early_applicable(self):
        return len(self.target.harts) > 1

    def test(self):
        output = self.gdb.command("thread 2")
        if "Unknown thread" in output:
            raise TestNotApplicable
        before = self.gdb.command("thread")
        self.gdb.stepi()
        after = self.gdb.command("thread")
        # make sure that single-step doesn't alter
        # GDB's conception of the current thread
        assertEqual(before, after)

class EtriggerTest(DebugTest):
    def setup(self):
        DebugTest.setup(self)
        self.gdb.b("main:start")
        self.gdb.c()
        self.gdb.b("handle_trap")

    def test(self):
        # Set trigger on Load access fault
        self.gdb.command("monitor riscv etrigger set m 0x20")
        # Set fox to a null pointer so we'll get a load access exception later.
        self.gdb.p("fox=(char*)0")
        output = self.gdb.c()
        # We should not be at handle_trap
        assertNotIn("handle_trap", output)
        # Instead, we should have hit a breakpoint at trap_entry, which is the
        # actual exception handler.
        assertIn("breakpoint", output)
        assertIn("trap_entry", self.gdb.where())

class ItriggerTest(GdbSingleHartTest):
    compile_args = ("programs/interrupt.c",)

    def early_applicable(self):
        return self.target.supports_clint_mtime

    def setup(self):
        self.gdb.load()

    def test(self):
        self.gdb.command(f"monitor targets {self.hart.id}")
        output = self.gdb.command("monitor riscv itrigger set 0x80")
        assertIn("Doesn't make sense", output)
        output = self.gdb.command("monitor riscv itrigger set m 0")
        assertIn("Doesn't make sense", output)
        output = self.gdb.command("monitor riscv itrigger clear")
        assertIn("No itrigger is set", output)
        self.gdb.command("monitor riscv itrigger set m 0x80")

        self.gdb.c()
        assertIn("trap_entry", self.gdb.where())

        self.gdb.command("monitor riscv itrigger clear")
        self.gdb.p("keep_running=0")
        self.exit()

parsed = None
def main():
    parser = argparse.ArgumentParser(
            description="Test that gdb can talk to a RISC-V target.",
            epilog="""
            Example command line from the real world:
            Run all RegsTest cases against a physical FPGA, with custom openocd command:
            ./gdbserver.py --freedom-e300 --server_cmd "$HOME/SiFive/openocd/src/openocd -s $HOME/SiFive/openocd/tcl -d" Simple
            """)
    targets.add_target_options(parser)

    testlib.add_test_run_options(parser)

    # TODO: remove global
    global parsed   # pylint: disable=global-statement
    parsed = parser.parse_args()
    target = targets.target(parsed)
    testlib.print_log_names = parsed.print_log_names

    module = sys.modules[__name__]

    return testlib.run_all_tests(module, target, parsed)

# TROUBLESHOOTING TIPS
# If a particular test fails, run just that one test, eg.:
# ./gdbserver.py MprvTest.test_mprv
# Then inspect gdb.log and spike.log to see what happened in more detail.

if __name__ == '__main__':
    sys.exit(main())
