# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500 for the program with records
(tests/TestSupport/Bare/Records.lean), whose record machine answers each record of three 64-bit
words with their sum modulo 2^64 and the number of records before it.

Each word travels as 8 bytes, most significant first.  The script runs QEMU through serve of
tests/baremetal/uart_echo.py, with UART0 on a Unix-domain socket and the transmitter's waits in
LOG, and then (a) sends RECORDS records one at a time, reading each answer before it sends the
next; (b) sends BURST records from a second thread while it reads the answers; (c) sends HELD
records from a second thread, reads nothing until LOG shows that the transmitter waits, and then
reads the answers; and (d) repeats (a).  A generator with a fixed seed draws the words, a tenth
of them from 0, 1, 2^64 - 2, and 2^64 - 1.  Each answer must hold the sum of its record's words
and the number of records sent before it, so that a lost, repeated, or reordered record or
answer shows as a wrong answer.  The script prints one line, a summary or the cause of the
failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in seconds.

Usage: uv run tests/baremetal/uart_records.py [--timeout TIMEOUT] LOG QEMU [ARG...]
"""

import argparse
import random
import sys
import threading
import time

from uart_echo import Failure, receive, report, serve

RECORDS = 100
BURST = 1000
HELD = 5000
MASK = 2**64 - 1
EDGES = (0, 1, MASK - 1, MASK)


def records(n, rng):
    return [[rng.choice(EDGES) if rng.random() < 0.1 else rng.getrandbits(64) for _ in range(3)]
            for _ in range(n)]


def encode(words):
    return b"".join(w.to_bytes(8, "big") for w in words)


class Machine:
    """The record machine of the program: the count of the records answered so far."""

    def __init__(self):
        self.count = 0

    def answers(self, recs):
        out = []
        for r in recs:
            out.append([sum(r) & MASK, self.count])
            self.count += 1
        return out


def check(what, expected, data):
    for i, answer in enumerate(expected):
        got = [int.from_bytes(data[16 * i + 8 * j:16 * i + 8 * j + 8], "big") for j in range(2)]
        if got != answer:
            raise Failure(f"{what}: answer {i} is {got}, not {answer}")


def lockstep(conn, rng, machine):
    for r in records(RECORDS, rng):
        conn.sendall(encode(r))
        check("lockstep", machine.answers([r]), receive(conn, 16))


def burst(conn, recs, machine, log=None):
    """Sends the records from a second thread and reads the answers.  With log, it reads nothing
    until the log shows the transmitter waiting, and it returns the number of waits."""
    expected = machine.answers(recs)
    data = b"".join(encode(r) for r in recs)
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
                raise Failure(f"sending {len(recs)} records failed: {errors[0]}")
            if time.monotonic() > deadline:
                raise Failure(f"the transmitter did not wait within {conn.gettimeout()} s of "
                              f"holding {len(recs)} answers")
            time.sleep(0.01)
    reply = receive(conn, 16 * len(recs))
    sender.join()
    if errors:
        raise Failure(f"sending {len(recs)} records failed: {errors[0]}")
    check(f"burst of {len(recs)}", expected, reply)
    return log.pending() - before if log is not None else 0


def exchange(conn, log):
    rng = random.Random(20261104)
    machine = Machine()
    lockstep(conn, rng, machine)
    burst(conn, records(BURST, rng), machine)
    waits = burst(conn, records(HELD, rng), machine, log)
    lockstep(conn, rng, machine)
    return waits, machine.count


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
    waits, count = result
    print(f"{count} records: {2 * RECORDS} in lockstep, a burst of {BURST}, and {HELD} held, "
          f"during which the transmitter waited {waits} time{'' if waits == 1 else 's'}, "
          f"in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
