# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Reads the first line that a NUCLEO-F767ZI sends through the serial port DEVICE, the virtual COM
port of its ST-LINK, at BAUD, 4,800 unless set, through serve_device of
tests/baremetal/uart_echo.py, and prints it.  The board runs an image whose startup code faults
before main, the echo built with GUARD_TEST or UNALIGNED_LDRD_TEST, and the fault handler reports
the fault in one line.  The script discards the bytes that the port holds when it opens it, so the
user resets the board after the script starts.  TIMEOUT bounds the wait in seconds.  The script
prints the line, or the cause of the failure, and exits with status 0 or 1.

Usage: uv run tests/baremetal/uart_report.py [--timeout TIMEOUT] --device DEVICE [--baud BAUD]
"""

import argparse
import sys

from uart_echo import Failure, serve_device


def read_line(conn):
    data = bytearray()
    while b"\n" not in data:
        try:
            chunk = conn.recv(256)
        except TimeoutError:
            raise Failure(f"no line within {conn.gettimeout()} s, only {bytes(data)!r}") from None
        if not chunk:
            raise Failure(f"the port closed after {bytes(data)!r}")
        data += chunk
    return data.split(b"\n")[0].decode("ascii", "replace")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--device", required=True)
    parser.add_argument("--baud", type=int, default=4800)
    args = parser.parse_args()
    line, error, _ = serve_device(args.device, args.baud, args.timeout,
                                  lambda conn, log: read_line(conn))
    if error:
        print(error)
        return 1
    print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
