# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500, or of USART3 of a NUCLEO-F767ZI, for the CRC-32
steps crcCmsdkTick and crcUsart3Tick (tests/TestSupport/M7/Crc.lean), which answer each byte with
the low byte of the CRC-32 of the bytes received so far.

The script runs QEMU through serve of tests/baremetal/uart_echo.py, with UART0 on a Unix-domain
socket and the transmitter's waits in LOG, and then (a) sends MESSAGE one byte at a time, reading
each reply before it sends the next; (b) sends bursts of BURSTS bytes from a second thread while
it reads the replies; (c) sends HELD bytes from a second thread, reads nothing until LOG shows
that the transmitter waits, and then reads the replies; and (d) repeats (a).  The bytes of the
bursts come from a generator with a fixed seed.  Each reply must equal the low byte of
zlib.crc32 of every byte sent before it and the byte itself, so that a lost, repeated, or
reordered byte or reply changes every later reply.

With --device DEVICE, the script runs no QEMU and talks through the serial port DEVICE, the
virtual COM port of a NUCLEO-F767ZI's ST-LINK or Renode's pseudo-terminal, with Serial of
uart_echo.py at BAUD, 4,800 unless set.  It runs (a), sends the bytes of each burst of BURSTS
with at most UNANSWERED of uart_echo.py, 2, of them unanswered, and runs (d), as uart_echo.py
does for the echo: USART3 holds one received byte and has no flow control, and the step reads a
byte only after it has written the reply to the one before.  The program must have received no
byte since reset before the script's first.  The script prints one line, a summary or the cause
of the failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in seconds.

Usage: uv run tests/baremetal/uart_crc.py [--timeout TIMEOUT] LOG QEMU [ARG...]
       uv run tests/baremetal/uart_crc.py [--timeout TIMEOUT] --device DEVICE [--baud BAUD]
"""

import argparse
import random
import sys
import threading
import time
import zlib

from uart_echo import UNANSWERED, Failure, receive, report, serve, serve_device

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


def window(conn, data, crc, unanswered):
    """Sends data with at most unanswered bytes unanswered and checks the replies."""
    first = crc.count
    expected = crc.replies(data)
    sent = 0
    reply = bytearray()
    while len(reply) < len(data):
        while sent < len(data) and sent - len(reply) < unanswered:
            conn.sendall(data[sent:sent + 1])
            sent += 1
        try:
            chunk = conn.recv(sent - len(reply))
        except TimeoutError:
            raise Failure(f"window of {len(data)}: {len(reply)} replies, then none for "
                          f"{conn.gettimeout()} s") from None
        if not chunk:
            raise Failure(f"window of {len(data)}: the port closed after {len(reply)} replies")
        reply += chunk
    check(f"window of {len(data)}", first, expected, bytes(reply))


def exchange(conn, log):
    rng = random.Random(20261107)
    crc = Crc()
    lockstep(conn, crc)
    for n in BURSTS:
        burst(conn, rng.randbytes(n), crc)
    waits = burst(conn, rng.randbytes(HELD), crc, log)
    lockstep(conn, crc)
    return waits, crc


def exchange_device(conn):
    rng = random.Random(20261107)
    crc = Crc()
    lockstep(conn, crc)
    for n in BURSTS:
        window(conn, rng.randbytes(n), crc, UNANSWERED)
    lockstep(conn, crc)
    return crc


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--device")
    parser.add_argument("--baud", type=int, default=4800)
    parser.add_argument("log", nargs="?")
    parser.add_argument("qemu", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.device:
        if args.log:
            parser.error("--device takes no LOG or QEMU")
        crc, error, elapsed = serve_device(args.device, args.baud, args.timeout,
                                           lambda conn, log: exchange_device(conn))
        if error:
            print(error)
            return 1
        print(f"{crc.count} bytes: {2 * len(MESSAGE)} in lockstep and bursts of "
              f"{', '.join(map(str, BURSTS))} with at most {UNANSWERED} unanswered on "
              f"{args.device} at {args.baud} baud, each reply the low byte of zlib.crc32 of "
              f"the bytes so far, the last CRC {crc.crc:#010x}, in {elapsed:.1f} s")
        return 0
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
