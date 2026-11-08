# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500, or of USART3 of a NUCLEO-F767ZI, for the SHA-256
steps shaCmsdkTick and shaUsart3Tick (tests/TestSupport/M7/Sha.lean), which answer each block of
64 bytes with the 32 bytes of the SHA-256 digest of every byte received so far.

The script runs QEMU through serve of tests/baremetal/uart_echo.py, with UART0 on a Unix-domain
socket and the transmitter's waits in LOG, and then (a) sends LOCKSTEP blocks one at a time, each
with one write, reading each answer before it sends the next block; (b) sends PIPELINED blocks
from a second thread while it reads the answers; (c) sends HELD blocks from a second thread, reads
nothing until LOG shows that the transmitter waits, and then reads the answers; and (d) repeats
(a).  The first block of (a) holds zero bytes, the second 0xff bytes, and every other block comes
from a generator with a fixed seed.  Each answer must equal hashlib.sha256 of every byte sent
before it, so that a lost, repeated, or reordered byte changes every later answer, and the
program must have received no byte since reset before the script's first.  QEMU's UART takes a byte only while
its receive buffer is empty, so (b) and (c) lose no byte although bytes wait while the step
computes.  On the board they would overrun USART3.  QEMU's transmitter waits after about 278
unread one-byte writes (uart_echo.py), so (c) must hold at least 9 blocks, whose answers take 288
bytes, before the log can show the wait, and HELD is 16.

With --device DEVICE, the script runs no QEMU and talks through the serial port DEVICE, the
virtual COM port of a NUCLEO-F767ZI's ST-LINK or Renode's pseudo-terminal, with Serial of
uart_echo.py at BAUD, 4,800 unless set, and it runs (a) alone.  The protocol of the step
requires that the host send a block only after it has read the whole answer to the block before:
USART3 holds one byte and has no flow control, and the step reads no byte while it computes a
block's two compressions or sends the block's answer.  The script prints one line, a summary or the cause of the
failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in seconds.

Usage: uv run tests/baremetal/uart_sha.py [--timeout TIMEOUT] LOG QEMU [ARG...]
       uv run tests/baremetal/uart_sha.py [--timeout TIMEOUT] --device DEVICE [--baud BAUD]
"""

import argparse
import hashlib
import random
import sys
import threading
import time

from uart_echo import Failure, receive, report, serve, serve_device

BLOCK = 64
ANSWER = 32
LOCKSTEP = 64
PIPELINED = 64
HELD = 16


class Sha:
    """The SHA-256 state of the bytes sent so far."""

    def __init__(self):
        self.h = hashlib.sha256()
        self.blocks = 0

    def answers(self, data):
        out = bytearray()
        for j in range(0, len(data), BLOCK):
            self.h.update(data[j:j + BLOCK])
            out += self.h.digest()
        self.blocks += len(data) // BLOCK
        return bytes(out)


def check(what, first, expected, reply):
    for i in range(0, len(expected), ANSWER):
        if reply[i:i + ANSWER] != expected[i:i + ANSWER]:
            raise Failure(f"{what}: the answer to block {first + i // ANSWER} is "
                          f"{reply[i:i + ANSWER].hex()}, not {expected[i:i + ANSWER].hex()}")


def lockstep(conn, sha, rng):
    for j in range(LOCKSTEP):
        data = bytes(BLOCK) if j == 0 else b"\xff" * BLOCK if j == 1 else rng.randbytes(BLOCK)
        first = sha.blocks
        expected = sha.answers(data)
        conn.sendall(data)
        check("lockstep", first, expected, receive(conn, ANSWER))


def burst(conn, data, sha, log=None):
    """Sends the blocks of data from a second thread and reads the answers.  With log, it reads
    nothing until the log shows the transmitter waiting, and it returns the number of waits."""
    first = sha.blocks
    expected = sha.answers(data)
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
                              f"holding {len(expected)} answer bytes")
            time.sleep(0.01)
    reply = receive(conn, len(expected))
    sender.join()
    if errors:
        raise Failure(f"sending {len(data)} bytes failed: {errors[0]}")
    check(f"{len(data) // BLOCK} blocks", first, expected, reply)
    return log.pending() - before if log is not None else 0


def exchange(conn, log):
    rng = random.Random(20261107)
    sha = Sha()
    lockstep(conn, sha, rng)
    burst(conn, rng.randbytes(PIPELINED * BLOCK), sha)
    waits = burst(conn, rng.randbytes(HELD * BLOCK), sha, log)
    lockstep(conn, sha, rng)
    return waits, sha


def exchange_device(conn):
    rng = random.Random(20261107)
    sha = Sha()
    lockstep(conn, sha, rng)
    return sha


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
        sha, error, elapsed = serve_device(args.device, args.baud, args.timeout,
                                           lambda conn, log: exchange_device(conn))
        if error:
            print(error)
            return 1
        print(f"{sha.blocks} blocks in lockstep on {args.device} at {args.baud} baud, each "
              f"answer the SHA-256 digest of the bytes sent so far, the last "
              f"{sha.h.hexdigest()}, in {elapsed:.1f} s")
        return 0
    if not args.qemu:
        parser.error("QEMU is missing")
    result, error, elapsed, early, status = serve(args.qemu, args.log, args.timeout, exchange)
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    waits, sha = result
    print(f"{sha.blocks} blocks: {2 * LOCKSTEP} in lockstep, {PIPELINED} pipelined, and {HELD} "
          f"held, during which the transmitter waited {waits} time{'' if waits == 1 else 's'}, "
          f"each answer the SHA-256 digest of the bytes sent so far, the last "
          f"{sha.h.hexdigest()}, in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
