# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500 for the CRC-32 step crcCmsdkTick
(tests/TestSupport/M7/Crc.lean), which answers each byte with the low byte of the CRC-32 of the
bytes received so far.

The script runs QEMU through serve of tests/baremetal/uart_echo.py, with UART0 on a Unix-domain
socket and the transmitter's waits in LOG, and then (a) sends MESSAGE one byte at a time, reading
each reply before it sends the next; (b) sends bursts of BURSTS bytes from a second thread while
it reads the replies; (c) sends HELD bytes from a second thread, reads nothing until LOG shows
that the transmitter waits, and then reads the replies; and (d) repeats (a).  The bytes of the
bursts come from a generator with a fixed seed.  Each reply must equal the low byte of
zlib.crc32 of every byte sent before it and the byte itself, so that a lost, repeated, or
reordered byte or reply changes every later reply.  The script prints one line, a summary or the
cause of the failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in seconds.

Usage: uv run tests/baremetal/uart_crc.py [--timeout TIMEOUT] LOG QEMU [ARG...]
"""

import argparse
import random
import sys
import threading
import time
import zlib

from uart_echo import Failure, receive, report, serve

MESSAGE = b"123456789" + bytes(range(256))
BURSTS = (2, 16, 1000, 65536)
HELD = 65536


class Crc:
    """The CRC-32 of the bytes sent so far, as zlib.crc32 computes it."""

    def __init__(self):
        self.crc = 0
        self.count = 0

    def replies(self, data):
        out = bytearray()
        for b in data:
            self.crc = zlib.crc32(bytes([b]), self.crc)
            out.append(self.crc & 0xFF)
        self.count += len(data)
        return bytes(out)


def check(what, first, expected, reply):
    for i, (e, r) in enumerate(zip(expected, reply)):
        if r != e:
            raise Failure(f"{what}: the reply to byte {first + i} is {r:#04x}, not {e:#04x}; "
                          f"replies {i} on: {reply[i:i + 32]!r}")


def lockstep(conn, crc):
    for b in MESSAGE:
        first = crc.count
        expected = crc.replies([b])
        conn.sendall(bytes([b]))
        check("lockstep", first, expected, receive(conn, 1))


def burst(conn, data, crc, log=None):
    """Sends data from a second thread and reads the replies.  With log, it reads nothing until
    the log shows the transmitter waiting, and it returns the number of waits."""
    first = crc.count
    expected = crc.replies(data)
    errors = []

    def send():
        try:
            conn.sendall(data)
        except OSError as e:
            errors.append(e)

    before = log.pending() if log is not None else 0
    sender = threading.Thread(target=send, daemon=True)
    sender.start()
    if log is not None:
        deadline = time.monotonic() + conn.gettimeout()
        while log.pending() == before:
            if errors:
                raise Failure(f"sending {len(data)} bytes failed: {errors[0]}")
            if time.monotonic() > deadline:
                raise Failure(f"the transmitter did not wait within {conn.gettimeout()} s of "
                              f"holding {len(data)} replies")
            time.sleep(0.01)
    reply = receive(conn, len(data))
    sender.join()
    if errors:
        raise Failure(f"sending {len(data)} bytes failed: {errors[0]}")
    check(f"burst of {len(data)}", first, expected, reply)
    return log.pending() - before if log is not None else 0


def exchange(conn, log):
    rng = random.Random(20261107)
    crc = Crc()
    lockstep(conn, crc)
    for n in BURSTS:
        burst(conn, rng.randbytes(n), crc)
    waits = burst(conn, rng.randbytes(HELD), crc, log)
    lockstep(conn, crc)
    return waits, crc


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("log")
    parser.add_argument("qemu", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.qemu:
        parser.error("QEMU is missing")
    result, error, elapsed, early, status = serve(args.qemu, args.log, args.timeout, exchange)
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    waits, crc = result
    print(f"{crc.count} bytes: {2 * len(MESSAGE)} in lockstep, bursts of "
          f"{', '.join(map(str, BURSTS))}, and {HELD} held, during which the transmitter waited "
          f"{waits} time{'' if waits == 1 else 's'}, each reply the low byte of zlib.crc32 of "
          f"the bytes so far, the last CRC {crc.crc:#010x}, in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
