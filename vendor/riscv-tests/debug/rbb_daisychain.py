#!/usr/bin/python3

import argparse
import sys
import socket

# https://github.com/ntfreak/openocd/blob/master/doc/manual/jtag/drivers/remote_bitbang.txt

class Tap:
    def __init__(self, port):
        self.port = port
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.socket.connect(("localhost", port))

    def execute(self, commands):
        sent = self.socket.send(commands)
        assert len(commands) == sent
        read_count = 0
        for command in commands:
            if command == ord('R'):
                read_count += 1
        result = b""
        while len(result) < read_count:
            result += self.socket.recv(read_count - len(result))
        assert len(result) == read_count
        return result

class Chain:
    def __init__(self, debug=False):
        self.debug = debug
        self.taps = []

    def append(self, tap):
        self.taps.append(tap)

    def execute(self, commands):
        values = []
        for i, tap in enumerate(self.taps):
            tmp_commands = []
            for command in commands:
                if i > 0 and ord('0') <= command <= ord('7'):
                    # Replace TDI with the value from the previous TAP.
                    v = values.pop(0)
                    command &= 0xfe
                    if v == ord('1'):
                        command |= 1

                if i < len(self.taps) - 1:
                    if command != ord('R'):
                        tmp_commands.append(command)
                    if ord('0') <= command <= ord('7'):
                        # Read TDO before every scan.
                        tmp_commands.append(ord('R'))
                else:
                    tmp_commands.append(command)
            assert len(values) == 0
            values = list(tap.execute(bytes(tmp_commands)))
            if self.debug:
                sys.stdout.write(f"    {i} {bytes(tmp_commands)!r} -> "
                                 f"{bytes(values)!r}\n")
        return bytes(values)

def main():
    parser = argparse.ArgumentParser(
            description='Combine multiple remote_bitbang processes into a '
            'single scan-chain.')
    parser.add_argument("listen_port", type=int,
            help="port to listen on")
    parser.add_argument("tap_port", nargs="+", type=int,
            help="port of a remote_bitbang TAP to connect to")
    parser.add_argument("--debug", action='store_true',
                        help="Print out debug messages.")
    args = parser.parse_args()

    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.bind(("localhost", args.listen_port))
    server.listen(1)

    chain = Chain(args.debug)
    for port in args.tap_port:
        chain.append(Tap(port))

    sys.stdout.write(f"Listening on port {server.getsockname()[1]}.\n")
    sys.stdout.flush()

    while True:
        (client, _) = server.accept()

        while True:
            try:
                commands = client.recv(4096)
            except (ConnectionResetError, OSError):
                sys.stdout.write("Client disconnected due to exception.\n")
                break

            if len(commands) == 0:
                sys.stdout.write("Client disconnected.\n")
                break

            if args.debug:
                sys.stdout.write(f"{commands!r}\n")
            result = chain.execute(commands)
            if args.debug:
                sys.stdout.write(f"   -> {result!r}\n")
            client.send(result)

        client.close()
        sys.stdout.flush()

if __name__ == '__main__':
    sys.exit(main())
