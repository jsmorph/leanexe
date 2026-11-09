# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500, or of USART3 of a NUCLEO-F767ZI, for the echo of
records over the delimited framing, dlCmsdkTick and dlUsart3Tick
(tests/TestSupport/M7/Delim.lean).  The step answers each nonempty segment, the bytes between two
0x00 bytes, with the COBS encoding of a status byte, the low byte of a count of nonempty
segments, and the decoded record, followed by 0x00: status 0 with the record for a segment that
decodes, 1 for one that does not, and 2 for one longer than 36 bytes.  It ignores an empty
segment.

The script sends a session in lockstep: it sends a segment and its 0x00, reads one answer for
each nonempty segment that the bytes close, and only then sends the next.  The answers expected
come from the mirror of tests/baremetal/delim_frame.py, applied to every byte sent so far, so
that a lost, added, or reordered answer or byte changes the comparison.  The session holds a
startup 0x00, records of 0 to 35 bytes with random contents, zeros among them, and segments
changed by delim_frame.corrupt, which changes, drops, inserts, or zeroes a byte, truncates the
encoding, or replaces it with a run of nonzero bytes longer than 36.  It also holds empty
segments, a record of 35 bytes, whose segment of 36 bytes is the longest that decodes, a record
of 36 bytes, whose encoding is an overflow, and a segment of 37 nonzero bytes.  RECORDS sets the
number of random records, 300 unless given.

With --overrun, for a board, the script also sends a record and, without waiting for its answer,
a burst of BURST bytes ending with 0x00, which arrive while the step decodes and answers and so
overrun USART3's one received byte.  It reads the record's answer, sends a 0x00, reads the answers
that arrive within SETTLE seconds, and then requires that RECOVER records each get the exact
answer, with the count that follows the last answer read, which shows that the next 0x00
restored alignment.  The bytes lost in the overrun are unknown to the script, so the answers
between the burst and the recovery are counted and not compared.

The script prints one line, a summary or the cause of the failure, and exits with status 0 or 1.
TIMEOUT bounds each wait in seconds.  The program must have received no byte since reset before
the script's first.

Usage: uv run tests/baremetal/uart_delim.py [--timeout TIMEOUT] [--records RECORDS] LOG QEMU [ARG...]
       uv run tests/baremetal/uart_delim.py [--timeout TIMEOUT] [--records RECORDS] [--overrun]
         --device DEVICE [--baud BAUD]
"""

import argparse
import random
import sys
import time

from delim_frame import answer_list, cobs_decode, cobs_encode, corrupt, record
from uart_echo import Failure, report, serve, serve_device

BURST = 12
SETTLE = 1.0
RECOVER = 5


def read_answer(conn):
    """The bytes up to and including the next 0x00."""
    out = bytearray()
    while True:
        try:
            chunk = conn.recv(1)
        except TimeoutError:
            raise Failure(f"no 0x00 within {conn.gettimeout()} s after {bytes(out)!r}") from None
        if not chunk:
            raise Failure(f"the connection closed after {bytes(out)!r}")
        out += chunk
        if chunk == b"\x00":
            return bytes(out)


class Session:
    """The bytes sent so far, the count of nonempty segments, and the tallies of the answers."""

    def __init__(self, conn):
        self.conn = conn
        self.sent = bytearray()
        self.count = 0
        self.tally = {"segments": 0, "empty": 0, "records": 0, "decode": 0, "overflow": 0}

    def exchange(self, data, what):
        """Sends data and reads and checks the answers that its 0x00 bytes call for."""
        pending = bytes(self.sent[self.sent.rfind(b"\x00") + 1:]) if 0 in self.sent \
            else bytes(self.sent)
        expected, self.count = answer_list(pending + data, self.count)
        self.sent += data
        self.conn.sendall(data)
        for i, e in enumerate(expected):
            got = read_answer(self.conn)
            if got != e:
                raise Failure(f"{what}: answer {i} is {got.hex()}, not {e.hex()}")
            status = cobs_decode(e[:-1])[0]
            self.tally[("records", "decode", "overflow")[status]] += 1
        segs = data.count(0)
        self.tally["segments"] += segs
        self.tally["empty"] += segs - len(expected)


def session(conn, records, overrun):
    rng = random.Random(20261109)
    s = Session(conn)
    s.exchange(b"\x00", "the startup delimiter")
    s.exchange(cobs_encode(bytes(range(1, 36))) + b"\x00", "a record of 35 bytes")
    s.exchange(cobs_encode(bytes(range(1, 37))) + b"\x00", "a record of 36 bytes")
    s.exchange(bytes([9] * 37) + b"\x00", "a segment of 37 bytes")
    for i in range(records):
        enc = cobs_encode(record(rng, rng.randrange(0, 36)))
        k = rng.randrange(6)
        if k == 0:
            s.exchange(corrupt(rng, enc) + b"\x00", f"corrupted record {i}")
        elif k == 1:
            s.exchange(b"\x00" * rng.randrange(1, 4) + enc + b"\x00", f"record {i} after empty ones")
        else:
            s.exchange(enc + b"\x00", f"record {i}")
    if overrun:
        recover(conn, s, rng)
    return s


def recover(conn, s, rng):
    """Forces an overrun and requires the records after the next 0x00 to get their answers."""
    rec = record(rng, 30)
    expected, count = answer_list(cobs_encode(rec) + b"\x00", s.count)
    conn.sendall(cobs_encode(rec) + b"\x00" + bytes(rng.randrange(1, 256)
                                                    for _ in range(BURST - 1)) + b"\x00")
    got = read_answer(conn)
    if got != expected[0]:
        raise Failure(f"overrun: the answer to the record before the burst is {got.hex()}, "
                      f"not {expected[0].hex()}")
    last = cobs_decode(got[:-1])[1]
    conn.sendall(b"\x00")
    extra = 0
    deadline = time.monotonic() + SETTLE
    saved = conn.timeout if hasattr(conn, "timeout") else None
    while time.monotonic() < deadline:
        conn.timeout = max(deadline - time.monotonic(), 0.01)
        try:
            a = read_answer(conn)
        except Failure:
            break
        extra += 1
        last = cobs_decode(a[:-1])[1]
    if saved is not None:
        conn.timeout = saved
    for i in range(RECOVER):
        r = record(rng, 20)
        conn.sendall(cobs_encode(r) + b"\x00")
        last = (last + 1) & 0xFF
        e = cobs_encode(bytes([0, last]) + r) + b"\x00"
        got = read_answer(conn)
        if got != e:
            raise Failure(f"recovery record {i}: answer {got.hex()}, not {e.hex()}")
    s.tally["overrun"] = extra


def summary(s, elapsed):
    t = s.tally
    text = (f"{len(s.sent)} bytes in {t['segments']} segments, {t['empty']} empty, answered "
            f"with {t['records']} records, {t['decode']} decoding errors, and {t['overflow']} "
            f"overflows, each answer the mirror's")
    if "overrun" in t:
        text += (f", then an overrun burst of {BURST} bytes with {t['overrun']} answers before "
                 f"{RECOVER} records answered exactly")
    return text + f", in {elapsed:.1f} s"


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--records", type=int, default=300)
    parser.add_argument("--overrun", action="store_true")
    parser.add_argument("--device")
    parser.add_argument("--baud", type=int, default=4800)
    parser.add_argument("log", nargs="?")
    parser.add_argument("qemu", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.device:
        if args.log:
            parser.error("--device takes no LOG or QEMU")
        s, error, elapsed = serve_device(args.device, args.baud, args.timeout,
                                         lambda conn, log: session(conn, args.records,
                                                                   args.overrun))
        if error:
            print(error)
            return 1
        print(summary(s, elapsed) + f", on {args.device} at {args.baud} baud")
        return 0
    if args.overrun:
        parser.error("--overrun needs --device: QEMU's UART never overruns")
    if not args.qemu:
        parser.error("QEMU is missing")
    s, error, elapsed, early, status = serve(
        args.qemu, args.log, args.timeout, lambda conn, log: session(conn, args.records, False))
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    print(summary(s, elapsed))
    return 0


if __name__ == "__main__":
    sys.exit(main())
