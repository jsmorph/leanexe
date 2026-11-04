# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The plant, the inverter, ingestion, and the optimizer of the energy controller
(Demos/Energy/Loop.lean) at the far end of UART0 of QEMU's mps2-an500.

The script runs QEMU through serve of tests/baremetal/uart_echo.py and plays one tick a minute
from minute START of the minute series SERIES that tests/energy/replay.py prepare writes, for
TICKS ticks.  Each tick it sends the gateway an input record of 18 words, each as 8 bytes, most
significant first, and reads its output record of 6 words.  The clock is 60 s per tick from
CLOCK0.  The measurements are the battery power of the last minute, the minute's load and PV
(the last known values for a missing minute), and the energy interval of replay.py's nominal
plant, the simulated energy plus or minus 360,000 J.  The read-back is the inverter's state.
Every PROPOSE ticks the optimizer proposes the load and PV intervals of replay.py's interval rule
over the window, which uses the minute values ahead, and limits: alternately the widest limits
that replay.py's rule accepts for the snapshot and the full range of charge and discharge.
Every SPIKE ticks, from tick SPIKE / 2 on, the measured load exceeds the minute's load by
5,000 W, which the interval rule does not cover.

The inverter applies a command at once with the revert timeout of the output record, returns to
fallback when the timeout passes or when the gateway requests it, and, as replay.py's plant does
with its option follow, follows the net load within the limits, the floor, and the ceiling, or
within the fallback interval in fallback.  The battery is replay.py's nominal plant, from its
starting energy.  This inverter applies each change at the tick of the change, or at the first
tick after a command's expiry, so that it meets the device assumption of the gateway's design
with delays below a tick.

The script checks that each output record carries the input's sequence number, and that each
command is the decision of replay.py's authorize for the snapshot words that the record and the
read-back give, with the revert timeout equal to the expiry minus the clock.  It also checks the
gateway's monitoring: a tick requests fallback exactly when it is the first, or when it falls
before the end of the window of the last command, W after its snapshot, with no fallback request
since, and load or PV lies outside that snapshot's intervals or battery power outside the
window's interval of replay.py's power_bounds.  It writes the input
records to RECORDS.in and the output records to RECORDS.out, one record of decimal words per line,
for comparison with native Lean.  It prints one line, a summary or the cause of the failure, and
exits with status 0 or 1.

Usage: uv run tests/baremetal/uart_gateway.py [--timeout TIMEOUT] [--start START] [--ticks TICKS]
    [--propose PROPOSE] [--spike SPIKE] SERIES RECORDS LOG QEMU [ARG...]
"""

import argparse
import os
import sys
import time
from collections import Counter

from uart_echo import Failure, receive, report, serve

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "energy"))
import replay  # noqa: E402

OFFSET = 2**32
CLOCK0 = 1_400_000_000
P = replay.SITE
KINDS = ("nothing", "command", "fallback")


def word(x):
    return int(x) & (2**64 - 1)


def encode(words):
    return b"".join(word(w).to_bytes(8, "big") for w in words)


def decode(data):
    return [int.from_bytes(data[8 * j:8 * j + 8], "big") for j in range(len(data) // 8)]


class Inverter:
    """The applied state: None for fallback, or the limits and the expiry of a command."""

    def __init__(self):
        self.command = None

    def tick(self, clock):
        if self.command is not None and clock >= self.command[2]:
            self.command = None

    def read_back(self):
        if self.command is None:
            return 1, OFFSET, OFFSET
        return 0, self.command[0] + OFFSET, self.command[1] + OFFSET

    def target(self, net, energy):
        net = min(net, max(0.0, ((P.ceiling - energy) / 60 + replay.LOSS) / replay.ETA_CHARGE))
        net = max(net, min(0.0, ((P.floor - energy) / 60 + replay.LOSS) * replay.ETA_DISCHARGE))
        low, high = ((P.fallback_low, P.fallback_high) if self.command is None
                     else self.command[:2])
        return min(high, max(low, net))


def run(conn, args, series, iv):
    plant = replay.NOMINAL
    energy = float(replay.START_ENERGY)
    power = 0.0
    inverter = Inverter()
    load, pv = 0, 0
    counts = Counter()
    records_in, records_out = [], []
    window = None
    for n in range(args.ticks):
        k = args.start + n
        clock = CLOCK0 + 60 * n
        inverter.tick(clock)
        if series.load[k] is not None:
            load, pv = series.load[k], series.pv[k]
        e_low, e_high = plant.interval(energy)
        mode, read_low, read_high = inverter.read_back()
        proposal = [0] * 7
        bounds = iv.bounds[k] if k < len(iv.bounds) else None
        if n % args.propose == 0 and bounds is not None:
            held = None if mode == 1 else (read_low - OFFSET, read_high - OFFSET)
            q = replay.Snapshot(clock, e_low, e_high, held, *bounds)
            widest = replay.accepted_range(P, q)
            low, high = ((-P.discharge_max, P.charge_max)
                         if (n // args.propose) % 2 or widest is None else widest)
            proposal = [1, *bounds, low + OFFSET, high + OFFSET]
        measured = load + (5000 if n % args.spike == args.spike // 2 else 0)
        words = [n, clock, clock, round(power) + OFFSET, measured, pv, e_low, e_high, mode,
                 read_low, read_high, *proposal]
        conn.sendall(encode(words))
        out = decode(receive(conn, 48))
        records_in.append(words)
        records_out.append(out)
        if out[0] != n:
            raise Failure(f"tick {n}: the output carries the sequence number {out[0]}")
        if out[1] > 2:
            raise Failure(f"tick {n}: the output's kind is {out[1]}")
        counts[KINDS[out[1]]] += 1
        leaves = window is not None and clock < window[0] and not (
            window[3] <= measured <= window[4] and window[5] <= pv <= window[6]
            and window[1] <= round(power) <= window[2])
        if (out[1] == 2) != (n == 0 or leaves):
            raise Failure(f"tick {n}: the output's kind is {KINDS[out[1]]}, and the monitoring "
                          f"expects {'a fallback request' if n == 0 or leaves else 'none'}")
        counts["leaves"] += leaves
        if out[1] == 1:
            snapshot = [1, clock, e_low, e_high, mode, read_low, read_high, *proposal[1:]]
            status, low, high, expiry = replay.authorize(P, snapshot)
            if (status, low, high, expiry - clock) != ("accepted", out[2], out[3], out[4]):
                raise Failure(f"tick {n}: the command {out[2:5]} is not the decision "
                              f"{(status, low, high, expiry - clock)} of the snapshot {snapshot}")
            inverter.command = (low - OFFSET, high - OFFSET, clock + out[4])
            held = None if mode == 1 else (read_low - OFFSET, read_high - OFFSET)
            q = replay.Snapshot(clock, e_low, e_high, held, *proposal[1:5])
            window = (clock + P.window, *replay.power_bounds(P, q, low - OFFSET, high - OFFSET),
                      *proposal[1:5])
        elif out[1] == 2:
            inverter.command = None
            window = None
        net = (pv - load) if series.load[k] is not None else 0
        power, energy = plant.step(energy, inverter.target(net, energy))
    return counts, records_in, records_out


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--start", type=int, default=7 * 24 * 60)
    parser.add_argument("--ticks", type=int, default=7 * 24 * 60)
    parser.add_argument("--propose", type=int, default=5)
    parser.add_argument("--spike", type=int, default=360)
    parser.add_argument("series")
    parser.add_argument("records")
    parser.add_argument("log")
    parser.add_argument("qemu", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.qemu:
        parser.error("QEMU is missing")
    series = replay.load_series(args.series)
    iv = replay.intervals(series, P.window // 60, None)
    if args.start + args.ticks > len(series.load):
        parser.error(f"the series has {len(series.load)} minutes")
    result, error, elapsed, early, status = serve(
        args.qemu, args.log, args.timeout, lambda conn, log: run(conn, args, series, iv))
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    counts, records_in, records_out = result
    for suffix, records in (("in", records_in), ("out", records_out)):
        with open(f"{args.records}.{suffix}", "w") as f:
            for r in records:
                f.write(" ".join(str(word(w)) for w in r) + "\n")
    print(f"{args.ticks} ticks from minute {args.start}: {counts['command']} commands, "
          f"{counts['fallback']} fallback requests, {counts['leaves']} of them for measurements "
          f"outside a window, {counts['nothing']} ticks without output, in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
