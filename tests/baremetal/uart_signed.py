# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500, or of USART3 of a NUCLEO-F767ZI, for the signed
steps sgCmsdkTick and sgUsart3Tick (tests/TestSupport/M7/Signed.lean), a leaky integrator of
signed bytes with saturation that answers each byte with the low byte of the integrator shifted
right arithmetically by 4.

The script follows tests/baremetal/uart_crc.py, whose burst and window it uses, with Integrator
in place of the CRC: (a) MESSAGE one byte at a time, (b) bursts of BURSTS bytes, (c) with QEMU,
HELD bytes held until the transmitter waits, and (d) MESSAGE again, or with --device DEVICE (a),
the bursts with at most UNANSWERED of uart_echo.py unanswered, and (d).  MESSAGE drives the
integrator to its upper bound with 0x7f bytes, to its lower bound with 0x80 bytes, through the 256
byte values, and back toward 0 with zero bytes, and the bursts come from a generator with a fixed
seed.  Each reply must equal Integrator's for every byte sent before it and the byte itself, so
that a lost, repeated, or reordered byte or reply changes the later replies.  The program must
have received no byte since reset before the script's first.  The script prints one line, a
summary or the cause of the failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in
seconds.

Usage: uv run tests/baremetal/uart_signed.py [--timeout TIMEOUT] LOG QEMU [ARG...]
       uv run tests/baremetal/uart_signed.py [--timeout TIMEOUT] --device DEVICE [--baud BAUD]
"""

import argparse
import random
import sys

from uart_crc import burst, check, window
from uart_echo import UNANSWERED, receive, report, serve, serve_device

MESSAGE = bytes([0x7F] * 40 + [0x80] * 40) + bytes(range(256)) + bytes(40)
BURSTS = (2, 16, 1000, 65536)
HELD = 65536


class Integrator:
    """The integrator of sgPhases over the bytes sent so far: for each byte read as a signed
    value x, acc - (acc >> 3) + x held in [-1000, 1000], with the reply the low byte of
    acc >> 4.  Python's >> on a negative integer rounds toward negative infinity, as Int64's
    arithmetic shift does."""

    def __init__(self):
        self.acc = 0
        self.count = 0
        self.low = 0
        self.high = 0

    def replies(self, data):
        out = bytearray()
        for b in data:
            x = b - 256 if b >= 128 else b
            t = self.acc - (self.acc >> 3) + x
            if t < -1000:
                self.acc = -1000
                self.low += 1
            elif t > 1000:
                self.acc = 1000
                self.high += 1
            else:
                self.acc = t
            out.append((self.acc >> 4) & 0xFF)
        self.count += len(data)
        return bytes(out)


def lockstep(conn, model):
    for b in MESSAGE:
        first = model.count
        expected = model.replies([b])
        conn.sendall(bytes([b]))
        check("lockstep", first, expected, receive(conn, 1))


def exchange(conn, log):
    rng = random.Random(20261108)
    model = Integrator()
    lockstep(conn, model)
    for n in BURSTS:
        burst(conn, rng.randbytes(n), model)
    waits = burst(conn, rng.randbytes(HELD), model, log)
    lockstep(conn, model)
    return waits, model


def exchange_device(conn):
    rng = random.Random(20261108)
    model = Integrator()
    lockstep(conn, model)
    for n in BURSTS:
        window(conn, rng.randbytes(n), model, UNANSWERED)
    lockstep(conn, model)
    return model


def bounds(model):
    return (f"the integrator held at -1000 {model.low} times and at 1000 {model.high} times, "
            f"the last integrator {model.acc}")


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
        model, error, elapsed = serve_device(args.device, args.baud, args.timeout,
                                             lambda conn, log: exchange_device(conn))
        if error:
            print(error)
            return 1
        print(f"{model.count} bytes: {2 * len(MESSAGE)} in lockstep and bursts of "
              f"{', '.join(map(str, BURSTS))} with at most {UNANSWERED} unanswered on "
              f"{args.device} at {args.baud} baud, each reply the integrator's, {bounds(model)}, "
              f"in {elapsed:.1f} s")
        return 0
    if not args.qemu:
        parser.error("QEMU is missing")
    result, error, elapsed, early, status = serve(args.qemu, args.log, args.timeout, exchange)
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    waits, model = result
    print(f"{model.count} bytes: {2 * len(MESSAGE)} in lockstep, bursts of "
          f"{', '.join(map(str, BURSTS))}, and {HELD} held, during which the transmitter waited "
          f"{waits} time{'' if waits == 1 else 's'}, each reply the integrator's, "
          f"{bounds(model)}, in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
