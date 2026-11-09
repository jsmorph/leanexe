# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The bridge and pack simulator of the BMS protection demo (Demos/Bms/requirements.md) at the far
end of the board's UART, and its fault-injection schedule.

The bridge implements BR1 to BR6 of the requirements with T_ans 100 ms, T_lease 500 ms, T_sample
20 ms, and T_act 20 ms.  It samples a simulated pack of four lithium iron phosphate cells, two
temperature sensors, a current sensor, the pack and bus voltages, three relays with auxiliary
contacts, a precharge resistor and the bus capacitance, the stop circuit, the reset button, and
the supervisor's RUN bit, sends one scan record a scan, and drives the relays from the answers.
Demos/Bms/Host.md describes the bridge's rules, the models and their parameters, the scenarios,
and the files.

"mirror" runs the scenarios against the Python machine of tests/baremetal/bms_proto.py behind a
simulated channel with simulated time: the line at 4,800 baud, USART3's single receive register
with OVRDIS set, the long window, and the latency of the host.  The simulated bridge samples a
record STEP ms, 1 unless set and at most T_sample, after the previous exchange ends and sends its
first byte STEP ms after sampling.  "qemu" runs QEMU through serve of tests/baremetal/uart_echo.py
with UART0 on a Unix-domain socket and its trace in LOG, and paces the bridge's bytes at the line
time.  "device" talks to a board through the serial port DEVICE at BAUD, 4,800 unless set, with
Serial of the same script, and runs the command CMD to reset the board when a scenario needs a
board reset; without CMD those scenarios are skipped.  With --reopen, the script releases DEVICE
before CMD and opens it again after CMD, waiting up to 10 s for it, so that CMD may reset the
ST-LINK's USB, which removes the port and adds it again.  The board must run the image from reset,
with no byte received, when the script starts.  Each run checks every answer byte for byte against
the Python machine fed the bytes that the bridge wrote, and each scenario's answers against the
schedule.  It writes the bytes written to PREFIX.in, the bytes received to PREFIX.out, and the
events with their times to PREFIX.log, replays PREFIX.in through the Python machine, prints one
line for each scenario and a summary, and exits with status 0 when no scenario fails and the
bridge kept T_sample and T_act, and 1 otherwise.  "replay" replays PREFIX.in and compares the
answers with PREFIX.out.  "list" prints the scenarios.

Usage: uv run tests/baremetal/uart_bms.py mirror [--scenario NAME]... [--seed SEED] [--step STEP]
           PREFIX
       uv run tests/baremetal/uart_bms.py qemu [--scenario NAME]... [--seed SEED]
           [--timeout TIMEOUT] PREFIX LOG QEMU [ARG...]
       uv run tests/baremetal/uart_bms.py device [--scenario NAME]... [--seed SEED]
           [--timeout TIMEOUT] [--baud BAUD] [--reset-command CMD] [--reopen] DEVICE PREFIX
       uv run tests/baremetal/uart_bms.py replay PREFIX
       uv run tests/baremetal/uart_bms.py list
"""

import argparse
import math
import os
import random
import select
import shlex
import subprocess
import sys
import time
import zlib
from collections import deque
from dataclasses import dataclass

import bms_proto as bp
from bms_proto import FAULT, NORMAL, PRECHARGE, RESET_REQUIRED, STANDBY, UNANSWERED
from uart_echo import Failure, Serial, report, serve, serve_device

T_ANS, T_LEASE, T_SAMPLE, T_ACT = 0.100, 0.500, 0.020, 0.020
N_PC, D_EDM, TOL_PC = 10, 2, 500
SEQ0 = (1 << 32) - 2
BYTE_TIME = 10 / 4800
SIM_WINDOW = 0.010
SIM_LATENCY = 0.005
OTHER_LINK = b"LeanExe-BMS-0002"
RELAYS = ("NEG", "PRE", "POS")
NEG, POS = 0, 2

OCV = ((0.00, 2.500), (0.05, 3.000), (0.10, 3.200), (0.20, 3.250), (0.40, 3.285), (0.60, 3.305),
       (0.80, 3.330), (0.90, 3.340), (0.95, 3.360), (1.00, 3.450))
CAPACITY = (280.0, 275.8, 282.8, 278.6)
SOC0 = (0.50, 0.49, 0.51, 0.50)
R0 = 0.25e-3
R1 = 0.30e-3
TAU1 = 30.0
R_BUSBAR = 0.30e-3
C_TH = 10_440.0
R_TH = 0.5
AMBIENT = (25.0, 24.5)
C_BUS = 0.010
R_PRE = 10.0
R_BLEED = 1000.0
R_SHORT = 1.0
RELAY_TIMES = ((0.030, 0.015), (0.010, 0.005), (0.030, 0.015))
SLOW_RELEASE = 0.200
PROFILE = ((8.0, -100.0), (2.0, 0.0), (8.0, 50.0), (2.0, 0.0))
NOISE = dict(cell=2, temp=1, current=50, pack=10, bus=10)
SIM_DT = 0.002
REOPEN_WAIT = 10.0


class ScenarioFailure(Exception):
    pass


class Skip(Exception):
    pass


def ocv(soc):
    soc = min(1.0, max(0.0, soc))
    for (s0, v0), (s1, v1) in zip(OCV, OCV[1:]):
        if soc <= s1:
            return v0 + (v1 - v0) * (soc - s0) / (s1 - s0)
    return OCV[-1][1]


def profile(t):
    t %= sum(d for d, _ in PROFILE)
    for d, amps in PROFILE:
        if t < d:
            return amps
        t -= d
    return 0.0


class Relay:
    """A relay whose main and auxiliary contacts follow its coil after the operate or release
    time.  A weld keeps closed contacts closed, and a failure to close keeps open contacts open."""

    def __init__(self, operate, release):
        self.operate, self.release = operate, release
        self.coil = self.closed = self.weld = self.fail_close = False
        self.pending = None

    def contact(self, t):
        if self.pending is not None and t >= self.pending[0]:
            self.closed, self.pending = self.pending[1], None
        return self.closed

    def update(self, t):
        self.contact(t)
        target = self.coil and not (self.fail_close and not self.closed)
        target = target or (self.weld and self.closed)
        if target == self.closed:
            self.pending = None
        elif self.pending is None or self.pending[1] != target:
            self.pending = (t + (self.operate if target else self.release), target)


class World:
    """The pack, the relays, the bus, and the inputs, integrated in steps of SIM_DT up to the time
    of each sampling and each coil change."""

    def __init__(self, seed):
        self.t = 0.0
        self.soc = list(SOC0)
        self.v1 = [0.0] * 4
        self.temp = list(AMBIENT)
        self.bus = 0.0
        self.current = 0.0
        self.short = False
        self.relays = [Relay(*rt) for rt in RELAY_TIMES]
        self.stop_ok, self.reset, self.run = True, False, False
        self.rng = random.Random(seed)

    def contacts(self, t):
        return sum(1 << r for r, rel in enumerate(self.relays) if rel.contact(t))

    def pack_voltage(self):
        return sum(ocv(s) + self.current * R0 + v for s, v in zip(self.soc, self.v1)) + \
            self.current * R_BUSBAR

    def advance(self, t):
        while self.t < t:
            dt = min(SIM_DT, t - self.t)
            c = self.contacts(self.t)
            main = c & 0b101 == 0b101
            pre = c & 0b011 == 0b011 and not main
            open_v = sum(ocv(s) + v for s, v in zip(self.soc, self.v1))
            if main:
                self.current = profile(self.t)
            elif pre:
                self.current = -(open_v - self.bus) / (R_PRE + 4 * R0 + R_BUSBAR)
            else:
                self.current = 0.0
            i = self.current
            decay = 1 - math.exp(-dt / TAU1)
            for k in range(4):
                self.v1[k] += (i * R1 - self.v1[k]) * decay
                self.soc[k] += i * dt / (CAPACITY[k] * 3600)
            for k in range(2):
                heat = 2 * i * i * (R0 + R1) - (self.temp[k] - AMBIENT[k]) / R_TH
                self.temp[k] += heat * dt / C_TH
            if main:
                self.bus = self.pack_voltage()
            else:
                g = 1 / R_BLEED + (1 / R_SHORT if self.short else 0) + (1 / R_PRE if pre else 0)
                target = (open_v / R_PRE if pre else 0.0) / g
                self.bus = target + (self.bus - target) * math.exp(-dt * g / C_BUS)
            self.t += dt

    def set_coils(self, mask, t):
        self.advance(t)
        for r, rel in enumerate(self.relays):
            rel.coil = bool(mask >> r & 1)
            rel.update(t)

    def change(self, t, relay, **flags):
        self.advance(t)
        rel = self.relays[relay]
        for name, value in flags.items():
            setattr(rel, name, value)
        rel.update(t)

    def clear_faults(self, t):
        self.short = False
        for r in range(3):
            self.change(t, r, weld=False, fail_close=False, release=RELAY_TIMES[r][1])

    def sample(self, t):
        """The readings at t: cells and pack and bus voltages in mV, temperatures in tenths of a
        degree, current in mA, and the digital word."""
        self.advance(t)
        n = lambda k: self.rng.randint(-NOISE[k], NOISE[k])
        cells = [round(1000 * (ocv(s) + self.current * R0 + v)) + n("cell")
                 for s, v in zip(self.soc, self.v1)]
        digital = (self.contacts(t) | bp.STOP_OK * self.stop_ok | bp.RESET * self.reset
                   | bp.RUN * self.run)
        return dict(cells=cells, temps=[round(10 * x) + n("temp") for x in self.temp],
                    current=round(1000 * self.current) + n("current"),
                    pack=round(1000 * self.pack_voltage()) + n("pack"),
                    bus=max(0, round(1000 * self.bus) + n("bus")), digital=digital)


class SimBoard:
    """The board behind the simulated channel: bytes reach USART3 SIM_LATENCY after they leave
    the host and take BYTE_TIME each on the line.  The program reads a byte as it arrives, except
    from a delimiter that ends a non-empty segment until it has sent the answer: the long window
    takes SIM_WINDOW, and the answer's bytes then leave at the line rate.  A byte that arrives
    meanwhile waits in USART_RDR, and a later one replaces it, as with OVRDIS set."""

    def __init__(self):
        self.arrivals = deque()
        self.outbox = deque()
        self.start()
        self.lost = 0

    def start(self):
        self.board = bp.Board()
        self.busy_until = -math.inf
        self.held = None

    def deliver(self, t, b):
        frame = self.board.push(b)
        if frame:
            begin = t + SIM_WINDOW
            for j, x in enumerate(frame):
                sent = begin + (j + 1) * BYTE_TIME
                self.outbox.append((sent + SIM_LATENCY, sent, x))
            self.busy_until = begin + len(frame) * BYTE_TIME

    def next_event(self):
        a = self.arrivals[0][0] if self.arrivals else math.inf
        h = self.busy_until if self.held is not None else math.inf
        return min(a, h)

    def event(self):
        a = self.arrivals[0][0] if self.arrivals else math.inf
        if self.held is not None and self.busy_until <= a:
            b, self.held = self.held, None
            self.deliver(self.busy_until, b)
            return
        t, b = self.arrivals.popleft()
        if t < self.busy_until:
            self.lost += self.held is not None
            self.held = b
        else:
            self.deliver(t, b)

    def until(self, t):
        while self.next_event() <= t:
            self.event()

    def reset(self, t):
        self.until(t)
        self.outbox = deque(x for x in self.outbox if x[1] <= t)
        self.start()


class SimLink:
    """The simulated channel and clock.  The bridge samples a record step after the previous
    exchange ends and sends its first byte step after sampling."""

    can_reset = True
    start_delay = 0.0

    def __init__(self, step):
        self.step = step
        self.t = 0.0
        self.free = 0.0
        self.board = SimBoard()

    def now(self):
        return self.t

    def write(self, data, service):
        start = max(self.t, self.free)
        for i, b in enumerate(data):
            self.board.arrivals.append((start + (i + 1) * BYTE_TIME + SIM_LATENCY, b))
        self.free = start + len(data) * BYTE_TIME
        return self.free

    def read(self, deadline):
        while True:
            host = self.board.outbox[0][0] if self.board.outbox else math.inf
            if self.board.next_event() < min(host, deadline):
                self.board.event()
                continue
            if host <= deadline:
                t, _, b = self.board.outbox.popleft()
                self.t = max(self.t, t)
                return self.t, bytes([b])
            self.t = max(self.t, deadline)
            return None

    def reset_board(self, service):
        self.board.reset(self.t)


class RealLink:
    """QEMU's UART0 through a socket, or a board's USART3 through a serial port, on the host's
    clock.  A record's end is estimated as the time of the write plus the line time of its
    bytes, byte_time each.  With pace, the bytes leave one at a time at that rate.  With reopen,
    a board reset releases the serial port before the reset command, so that a USB reset of the
    ST-LINK in the command can enumerate the port again under its name, and then reopens it with
    reopen() under the same descriptor."""

    def __init__(self, conn, byte_time, pace, reset_command=None, reopen=None, start_delay=0.0):
        self.start_delay = start_delay
        self.conn = conn
        self.fd = conn.fd if hasattr(conn, "fd") else conn.fileno()
        self.byte_time = byte_time
        self.pace = pace
        self.reset_command = reset_command
        self.reopen = reopen
        self.can_reset = reset_command is not None
        self.step = 0
        self.t0 = time.monotonic()

    def now(self):
        return time.monotonic() - self.t0

    def write(self, data, service):
        start = self.now()
        if not self.pace:
            self.conn.sendall(data)
            return start + len(data) * self.byte_time
        for i, b in enumerate(data):
            while (wait := start + i * self.byte_time - self.now()) > 0:
                service()
                time.sleep(min(wait, 0.001))
            self.conn.sendall(bytes([b]))
        return start + len(data) * self.byte_time

    def read(self, deadline):
        ready, _, _ = select.select([self.fd], [], [], max(0.0, deadline - self.now()))
        if not ready:
            return None
        data = self.conn.recv(4096)
        if not data:
            raise Failure("the connection closed")
        return self.now(), data

    def reset_board(self, service):
        if self.reopen is not None:
            null = os.open(os.devnull, os.O_RDWR)
            os.dup2(null, self.fd)
            os.close(null)
        proc = subprocess.Popen(shlex.split(self.reset_command), stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        while proc.poll() is None:
            service()
            time.sleep(0.001)
        if proc.returncode:
            raise Failure(f"the reset command exited with status {proc.returncode}: "
                          f"{proc.stdout.read().decode(errors='replace')[-300:]}")
        if self.reopen is not None:
            port = self.reopen(service)
            os.dup2(port.fd, self.fd)
            os.close(port.fd)


class Log:
    """PREFIX.log, PREFIX.in, and PREFIX.out."""

    def __init__(self, prefix):
        os.makedirs(os.path.dirname(prefix) or ".", exist_ok=True)
        self.events = open(prefix + ".log", "w")
        self.ins = open(prefix + ".in", "w")
        self.outs = open(prefix + ".out", "w")

    def event(self, t, kind, text=""):
        self.events.write(f"{1000 * t:.3f} {kind} {text}".rstrip() + "\n")

    def close(self):
        for f in (self.events, self.ins, self.outs):
            f.close()


@dataclass
class Seen:
    t: float
    answer: bp.Answer
    current: bool


@dataclass
class Latest:
    seq: int
    sampled: float
    answered: bool = False
    at: float = 0.0


class Bridge:
    """BR1 to BR6.  lease[r] is the end of relay r's lease, or None, and blocked is the
    condition of BR6 under which no relay is energized."""

    def __init__(self, link, world, log):
        self.link, self.world, self.log = link, world, log
        self.seq = SEQ0
        self.sent = 0
        self.latest = None
        self.last = None
        self.lease = [None] * 3
        self.blocked = True
        self.coils = 0
        self.rx = bytearray()
        self.raw = bytearray()
        self.raw_dropped = False
        self.last_rx = -math.inf
        self.frames = 0
        self.drop = False
        self.seen = []
        self.records = {}
        self.shadow = bp.Board()
        self.expected = deque()
        self.exchange_end = 0.0
        self.record_end = 0.0
        self.timeouts = 0
        self.expiries = []
        self.lag = 0.0
        self.sample_lag = 0.0
        self.exchange_times = []
        self.margins = []

    def now(self):
        return self.link.now()

    def service(self):
        """Ends the leases whose time has passed and drives the relays: a relay is energized
        while it holds a lease and BR6 does not block."""
        now = self.now()
        ended = []
        for r in range(3):
            if self.lease[r] is not None and now >= self.lease[r]:
                ended.append((r, self.lease[r]))
                self.expiries.append((r, self.lease[r], now))
                self.log.event(now, "expire", f"{RELAYS[r]} {1000 * self.lease[r]:.3f}")
                self.lease[r] = None
                self.blocked = True
                self.drop = False
        coils = 0 if self.blocked else sum(1 << r for r in range(3) if self.lease[r] is not None)
        if coils != self.coils:
            for r, end in ended:
                if self.coils >> r & 1:
                    self.lag = max(self.lag, now - end)
            self.coils = coils
            self.world.set_coils(coils, now)
            self.log.event(now, "coils", f"{coils:#04x}")

    def write(self, data):
        self.log.ins.write(data.hex() + "\n")
        self.log.event(self.now(), "tx", data.hex())
        for b in data:
            frame = self.shadow.push(b)
            if frame:
                self.expected.append(frame)
        return self.link.write(data, self.service)

    def receive(self, t, data):
        for b in data:
            self.raw.append(b)
            if self.drop:
                self.raw_dropped = True
            else:
                self.rx.append(b)
                self.last_rx = t
            if b != 0:
                continue
            frame = bytes(self.raw)
            self.raw.clear()
            self.frames += 1
            self.log.outs.write(frame.hex() + "\n")
            self.log.event(t, "rx", frame.hex())
            if not self.expected:
                raise Failure(f"the board sent {frame.hex()}, and the mirror expects no answer")
            expected = self.expected.popleft()
            if frame != expected:
                raise Failure(f"the board sent {frame.hex()}, and the mirror expects "
                              f"{expected.hex()}")
            if self.raw_dropped:
                self.log.event(t, "drop", frame.hex())
                self.raw_dropped = False
            if not self.drop:
                body = bytes(self.rx[:-1])
                self.rx.clear()
                if body:
                    self.answer(t, body)

    def answer(self, t, body):
        """BR1 for the frame body: an authentic answer acts on the leases."""
        try:
            a = bp.decode_answer(bp.cobs_decode(body))
        except bp.DecodeError:
            a = None
        if a is None:
            self.log.event(t, "inauthentic", body.hex())
            return
        latest = self.latest
        current = latest is not None and a.answered == latest.seq and not latest.answered
        if current:
            latest.answered = True
            latest.at = t
        self.last = a
        self.seen.append(Seen(t, a, current))
        self.log.event(t, "answer", f"{a.board} {a.answered:#010x} {a} "
                                    f"{'current' if current else 'other'}")
        for r in range(3):
            if a.permit >> r & 1:
                if current:
                    if self.lease[r] is not None:
                        self.margins.append(self.lease[r] - t)
                    self.lease[r] = latest.sampled + T_LEASE
            elif self.lease[r] is not None:
                self.lease[r] = None
                self.log.event(t, "revoke", f"{RELAYS[r]} {'current' if current else 'other'}")
                if not current:
                    self.blocked = True
        if current and a.permit == 0:
            self.blocked = False
        self.service()

    def wait(self, deadline, stop):
        """Receives and applies answers until stop() holds, then returns True, or until
        deadline() passes, then returns False."""
        while True:
            self.service()
            if stop():
                return True
            d = deadline()
            if self.now() >= d:
                return False
            ends = [e for e in self.lease if e is not None]
            got = self.link.read(min([d] + ends))
            if got:
                self.receive(*got)

    def quiet(self, end, stop):
        return self.wait(lambda: max(end, self.last_rx) + T_ANS, stop)

    def power_up(self):
        self.world.set_coils(0, self.now())
        self.log.event(self.now(), "power-up")
        self.quiet(self.write(b"\x00"), lambda: False)
        self.exchange_end = self.now()

    def idle(self, duration):
        end = self.now() + duration
        self.wait(lambda: end, lambda: False)

    def pause(self):
        if self.link.step:
            self.idle(self.link.step)

    def resume(self):
        self.exchange_end = self.now()

    def timeout(self):
        self.timeouts += 1
        self.rx.clear()
        self.log.event(self.now(), "timeout")
        self.quiet(self.write(b"\x00"), lambda: self.latest.answered)

    def exchange(self, edit=None, raw_edit=None, chunks=None):
        """One scan: BR5's sampling, the record with a channel fault, and BR3's and BR4's
        waits.  edit changes the readings, raw_edit the raw record, and chunks turns the wire
        bytes into the pieces that the channel delivers, with BOARD_RESET for a board reset.
        Returns the authentic answers received."""
        self.seen = []
        self.pause()
        sampled = self.now()
        v = self.world.sample(sampled)
        if edit:
            edit(v)
        raw = bp.scan_record(self.seq, v["cells"], v["temps"], v["current"], v["pack"], v["bus"],
                             v["digital"])
        if raw_edit:
            raw = raw_edit(raw)
        self.records[self.seq] = (raw, sampled)
        self.latest = Latest(self.seq, sampled)
        self.log.event(sampled, "sample", f"{self.seq} {raw.hex()}")
        self.pause()
        self.sample_lag = max(self.sample_lag, sampled - self.exchange_end,
                              self.now() - sampled)
        w = bp.wire(raw)
        parts = chunks(w) if chunks else [w]
        for part in parts:
            if part is BOARD_RESET:
                self.reset_board()
                continue
            end = self.write(part)
            if len(parts) > 1:
                n = self.frames
                self.quiet(end, lambda: self.frames > n)
        self.record_end = end
        if self.wait(lambda: end + T_ANS, lambda: self.latest.answered):
            if len(parts) == 1:
                self.exchange_times.append(self.latest.at - sampled)
        else:
            self.timeout()
        self.seq = (self.seq + 1) % (1 << 32)
        self.sent += 1
        self.exchange_end = self.now()
        return self.seen

    def reset_board(self):
        """A board reset between two writes.  The sampling after it counts its T_sample from the
        end of the reset."""
        if self.expected or self.raw:
            raise Failure(f"a board reset with {len(self.expected)} answers outstanding")
        self.log.event(self.now(), "board-reset")
        self.link.reset_board(self.service)
        self.log.ins.write("reset\n")
        self.log.outs.write("reset\n")
        self.shadow = bp.Board()
        self.exchange_end = self.now()


BOARD_RESET = object()


class Run:
    """The scenarios' view of the bridge and the world, with the checks of the expected
    answers."""

    def __init__(self, bridge, world, link):
        self.bridge, self.world, self.link = bridge, world, link
        self.fresh = True
        self.trace = []
        self.granted = None

    def ex(self, **kw):
        """One exchange.  granted becomes the sampling time of the record of the last current
        answer with a nonzero permit."""
        self.fresh = False
        seen = self.bridge.exchange(**kw)
        self.trace += [s.answer for s in seen]
        for s in seen:
            if s.current and s.answer.permit:
                self.granted = self.bridge.records[s.answer.answered][1]
        return seen

    def record(self, seen=None):
        seq = self.bridge.latest.seq if seen is None else seen.answer.answered
        return bp.decode_scan(self.bridge.records[seq][0])

    def fail(self, text):
        raise ScenarioFailure(text)

    def one(self, seen, permit, state, codes, answered=None, current=True, board=None):
        if len(seen) != 1:
            self.fail(f"{len(seen)} answers ({', '.join(str(s.answer) for s in seen)}) where "
                      f"one {permit:#04x} {bp.STATES[state]} is expected")
        return self.check(seen[0], permit, state, codes, answered, current, board)

    def check(self, s, permit, state, codes, answered=None, current=True, board=None):
        a = s.answer
        codes = {codes} if isinstance(codes, int) else codes
        if answered is None and current:
            answered = self.bridge.latest.seq
        if (a.permit, a.state) != (permit, state) or a.code not in codes:
            self.fail(f"answer {a} where {permit:#04x} {bp.STATES[state]} "
                      f"{' or '.join(f'{c:#06x}' for c in sorted(codes))} is expected")
        if answered is not None and a.answered != answered:
            self.fail(f"answer {a} answers {a.answered:#010x}, not {answered:#010x}")
        if s.current != current:
            self.fail(f"answer {a} is {'' if s.current else 'not '}current")
        if board is not None and a.board != board:
            self.fail(f"answer {a} has board sequence number {a.board}, not {board}")
        return s

    def coils(self, mask):
        if self.bridge.coils != mask:
            self.fail(f"the bridge energizes {self.bridge.coils:#04x}, not {mask:#04x}")

    def boot(self):
        if not self.fresh:
            self.need_reset()
            self.bridge.reset_board()

    def need_reset(self):
        if not self.link.can_reset:
            raise Skip("no board reset on this link")

    def mark(self):
        self.trace = []
        self.timeouts = self.bridge.timeouts

    def start(self):
        """A start from STANDBY with the relays open, and the precharge."""
        self.world.run = True
        self.one(self.ex(), 0x03, PRECHARGE, 0)
        self.coils(0b011)
        self.precharge()

    def precharge(self):
        for _ in range(N_PC - 1):
            seen = self.ex()
            if precharge_condition(self.record()):
                self.one(seen, 0x05, NORMAL, 0)
                self.coils(0b101)
                return
            self.one(seen, 0x03, PRECHARGE, 0)
        self.fail(f"no precharge condition within {N_PC} records")

    def to_normal(self):
        """From any state to NORMAL: a release and a press of the reset button with RUN 0 in
        RESET_REQUIRED or FAULT, a record with RUN 0 in STANDBY, and a start."""
        w = self.world
        state = self.bridge.last.state if self.bridge.last else RESET_REQUIRED
        w.stop_ok, w.reset = True, False
        if state == NORMAL:
            w.run = True
            return
        if state == PRECHARGE:
            w.run = True
            self.precharge()
            return
        w.run = False
        if state in (RESET_REQUIRED, FAULT):
            seen = self.ex()
            if len(seen) != 1 or seen[0].answer.state not in (RESET_REQUIRED, FAULT):
                self.fail(f"answers {', '.join(str(s.answer) for s in seen)} to the release "
                          f"of the reset button")
            w.reset = True
            self.one(self.ex(), 0, STANDBY, 0)
            w.reset = False
        else:
            self.one(self.ex(), 0, STANDBY, 0)
        self.start()


def precharge_condition(sc):
    return abs(sc.bus - sc.pack) <= TOL_PC and sc.digital & 0b011 == 0b011


def cell(i, mv):
    def edit(v):
        v["pack"] += mv - v["cells"][i]
        v["cells"][i] = mv
    return edit


def temp(i, tenths, current=None):
    def edit(v):
        v["temps"][i] = tenths
        if current is not None:
            v["current"] = current
    return edit


def current(ma):
    return lambda v: v.__setitem__("current", ma)


def pack_above_sum(mv):
    return lambda v: v.__setitem__("pack", sum(v["cells"]) + mv)


def reserved(v):
    v["digital"] |= 0x40


def data_position(w):
    """A wire position near the middle of the record that holds a data byte, not a COBS code
    byte or the delimiter."""
    codes, i = set(), 0
    while i < len(w) - 1:
        codes.add(i)
        i += w[i]
    return next(p for p in range(len(w) // 2, len(w) - 1) if p not in codes)


def limit_scenario(ok, bad, code):
    def run(r):
        r.to_normal()
        r.mark()
        if ok:
            r.one(r.ex(edit=ok), 0x05, NORMAL, 0)
        r.one(r.ex(edit=bad), 0, FAULT, code)
        r.coils(0)
    return run


def normal_start(r):
    r.boot()
    r.mark()
    w = r.world
    w.stop_ok, w.reset, w.run = True, False, False
    r.one(r.ex(), 0, RESET_REQUIRED, 0x0001, board=0)
    w.reset = True
    r.one(r.ex(), 0, STANDBY, 0, board=1)
    w.reset = False
    r.start()


def reset_held_at_boot(r):
    r.boot()
    r.mark()
    w = r.world
    w.stop_ok, w.reset, w.run = True, True, False
    for _ in range(3):
        r.one(r.ex(), 0, RESET_REQUIRED, 0x0001)
    w.reset = False
    for _ in range(2):
        r.one(r.ex(), 0, RESET_REQUIRED, 0x0001)
    w.reset = True
    r.one(r.ex(), 0, STANDBY, 0)
    w.reset = False
    r.start()


def reset_with_run(r):
    r.to_normal()
    r.mark()
    r.one(r.ex(edit=cell(0, 3651)), 0, FAULT, 0x2002)
    r.one(r.ex(edit=temp(0, 551)), 0, FAULT, 0x2002)
    r.one(r.ex(), 0, FAULT, 0x2002)
    r.world.reset = True
    r.one(r.ex(), 0, FAULT, 0x2002)
    r.one(r.ex(), 0, FAULT, 0x2002)
    r.world.reset = False
    r.one(r.ex(), 0, FAULT, 0x2002)


def restart_after_standby(r):
    """RUN 0 for one record, then RUN 1: a record that reports a contact still closed gets
    STANDBY, since a start needs the auxiliary word 0."""
    r.to_normal()
    r.mark()
    r.world.run = False
    r.one(r.ex(), 0, STANDBY, 0)
    r.coils(0)
    r.world.run = True
    for _ in range(3):
        seen = r.ex()
        if r.record().digital & 0b111 == 0:
            r.one(seen, 0x03, PRECHARGE, 0)
            r.coils(0b011)
            r.precharge()
            return
        r.one(seen, 0, STANDBY, 0)
    r.fail("the contacts did not open")


def comm_fault(chunks, codes, raw_edit=None):
    """A damaged record answered 0xFFFFFFFF, BR4, and the next record, which synchronizes."""
    def run(r):
        r.to_normal()
        r.mark()
        s = r.one(r.ex(chunks=chunks, raw_edit=raw_edit), 0, FAULT, codes, answered=UNANSWERED,
                  current=False)
        r.coils(0)
        if r.bridge.timeouts != r.timeouts + 1:
            r.fail("no timeout after the damaged record")
        r.one(r.ex(), 0, FAULT, s.answer.code)
    return run


def lost_delimiter(r):
    r.to_normal()
    r.mark()
    n = len(r.bridge.expiries)
    s = r.one(r.ex(chunks=lambda w: [w[:-1]]), 0x05, NORMAL, 0)
    if r.bridge.timeouts != r.timeouts + 1:
        r.fail("no timeout after the record without its delimiter")
    if s.t < r.bridge.record_end + T_ANS:
        r.fail("an answer within T_ans of the record without its delimiter")
    if len(r.bridge.expiries) != n or r.bridge.coils != 0b101:
        r.fail("the relays were released")


def inserted_between(r):
    r.to_normal()
    r.mark()
    r.one(r.ex(chunks=lambda w: [w + b"\x55"]), 0x05, NORMAL, 0)
    r.one(r.ex(), 0, FAULT, 0x1002, answered=UNANSWERED, current=False)
    r.coils(0)
    r.one(r.ex(), 0, FAULT, 0x1002)


def zero_byte(r):
    r.to_normal()
    r.mark()
    seen = r.ex(chunks=lambda w: [w[:data_position(w)] + b"\x00", w[data_position(w) + 1:]])
    if len(seen) != 2:
        r.fail(f"{len(seen)} answers to the record split by 0x00")
    first = r.check(seen[0], 0, FAULT, {0x1001, 0x1003}, answered=UNANSWERED, current=False)
    r.check(seen[1], 0, FAULT, first.answer.code, answered=UNANSWERED, current=False)
    r.coils(0)
    r.one(r.ex(), 0, FAULT, first.answer.code)


def wrong_link(raw):
    return raw[:31] + bp.be(zlib.crc32(raw[:31], zlib.crc32(OTHER_LINK)), 4)


def wrong_tag(raw):
    body = b"\x11" + raw[1:31]
    return body + bp.be(bp.crc(body), 4)


def wrong_tag_scenario(r):
    r.to_normal()
    r.mark()
    r.one(r.ex(raw_edit=wrong_tag), 0, FAULT, 0x1005)
    r.coils(0)


def repeated_record(r):
    r.to_normal()
    r.mark()
    seen = r.ex(chunks=lambda w: [w, w])
    if len(seen) != 2:
        r.fail(f"{len(seen)} answers to the repeated record")
    seq = r.bridge.latest.seq
    r.check(seen[0], 0x05, NORMAL, 0)
    r.check(seen[1], 0, FAULT, 0x1006, answered=seq, current=False)
    r.coils(0)
    if not r.bridge.blocked:
        r.fail("no BR6 block after the second answer released the relays")
    r.one(r.ex(), 0, FAULT, 0x1006)
    if r.bridge.blocked:
        r.fail("BR6 still blocks after a current answer with permit 0")


def skipped_number(r):
    r.to_normal()
    r.mark()
    r.bridge.seq = (r.bridge.seq + 1) % (1 << 32)
    r.bridge.log.event(r.bridge.now(), "inject", "skipped sequence number")
    r.one(r.ex(), 0, FAULT, 0x1006)
    r.one(r.ex(), 0, FAULT, 0x1006)


def released_then(r, n, granted, seen):
    """Checks the release of the relays within T_act of T_lease after granted, the sampling of
    the record of the last current answer with a nonzero permit, by expiries after the first n,
    and the answers seen and those that follow: NORMAL for records that report NEG closed, which
    energize nothing (BR6), and 0x3001 for the first record that reports NEG open."""
    expired = r.bridge.expiries[n:]
    if not expired:
        r.fail("no lease expired")
    for _, _, at in expired:
        if not -1e-9 <= at - (granted + T_LEASE) <= T_ACT + 1e-9:
            r.fail(f"a relay released {1000 * (at - granted):.1f} ms after the sampling of the "
                   f"record of its last permit")
    r.coils(0)
    for _ in range(4):
        for s in seen:
            if s.answer.state == FAULT:
                r.check(s, 0, FAULT, 0x3001)
                if r.record(s).digital & bp.AUX_NEG:
                    r.fail("0x3001 for a record that reports NEG closed")
                return
            r.check(s, 0x05, NORMAL, 0)
            if not r.record(s).digital & bp.AUX_NEG:
                r.fail("NORMAL for a record that reports NEG open")
            r.coils(0)
        seen = r.ex()
    r.fail("no 0x3001 after the release")


def lost_answers(r):
    r.to_normal()
    r.mark()
    n, granted = len(r.bridge.expiries), r.granted
    r.bridge.drop = True
    r.bridge.log.event(r.bridge.now(), "inject", "answers dropped until the lease expires")
    for _ in range(4):
        seen = r.ex()
        if not r.bridge.drop:
            break
        if seen:
            r.fail(f"answer {seen[0].answer} received while answers are dropped")
    else:
        r.fail("no lease expired while answers were dropped")
    released_then(r, n, granted, seen)


def bridge_silent(r):
    r.to_normal()
    r.mark()
    n, granted = len(r.bridge.expiries), r.granted
    r.bridge.log.event(r.bridge.now(), "inject", "bridge silent")
    r.bridge.seen = []
    r.bridge.idle(T_LEASE + 0.5)
    if r.bridge.seen:
        r.fail("an answer while the bridge was silent")
    r.bridge.resume()
    released_then(r, n, granted, [])


def welded_contactor(r):
    r.to_normal()
    r.mark()
    w = r.world
    w.change(r.bridge.now(), POS, weld=True)
    r.bridge.log.event(r.bridge.now(), "inject", "POS welded")
    w.run = False
    for _ in range(1 + D_EDM):
        r.one(r.ex(), 0, STANDBY, 0)
    r.one(r.ex(), 0, FAULT, 0x3001)
    r.one(r.ex(), 0, FAULT, 0x3001)
    w.reset = True
    r.one(r.ex(), 0, FAULT, 0x3001)
    w.reset = False


def fails_to_close(r):
    r.to_normal()
    r.mark()
    w = r.world
    w.run = False
    r.one(r.ex(), 0, STANDBY, 0)
    r.one(r.ex(), 0, STANDBY, 0)
    w.change(r.bridge.now(), POS, fail_close=True)
    r.bridge.log.event(r.bridge.now(), "inject", "POS fails to close")
    r.start()
    for _ in range(D_EDM):
        r.one(r.ex(), 0x05, NORMAL, 0)
    r.one(r.ex(), 0, FAULT, 0x3001)


def precharge_failure(r):
    r.to_normal()
    r.mark()
    w = r.world
    w.run = False
    r.one(r.ex(), 0, STANDBY, 0)
    r.one(r.ex(), 0, STANDBY, 0)
    w.advance(r.bridge.now())
    w.short = True
    r.bridge.log.event(r.bridge.now(), "inject", "bus shorted")
    w.run = True
    for _ in range(N_PC):
        r.one(r.ex(), 0x03, PRECHARGE, 0)
    r.one(r.ex(), 0, FAULT, 0x3002)


def stop(r):
    r.to_normal()
    r.mark()
    w = r.world
    w.stop_ok = False
    r.one(r.ex(), 0, RESET_REQUIRED, 0x5001)
    r.coils(0)
    r.one(r.ex(), 0, RESET_REQUIRED, 0x5001)
    w.stop_ok = True
    r.one(r.ex(), 0, RESET_REQUIRED, 0x5001)
    r.one(r.ex(), 0, RESET_REQUIRED, 0x5001)
    r.to_normal()


def standby_request(r):
    r.to_normal()
    r.mark()
    r.world.run = False
    r.one(r.ex(), 0, STANDBY, 0)
    r.coils(0)


def board_reset_normal(r):
    r.need_reset()
    r.to_normal()
    r.mark()
    r.bridge.reset_board()
    r.one(r.ex(), 0, RESET_REQUIRED, 0x0001, board=0)
    r.coils(0)
    if r.bridge.blocked:
        r.fail("BR6 blocks after a current answer with permit 0")
    for k in (1, 2):
        r.one(r.ex(), 0, RESET_REQUIRED, 0x0001, board=k)


def reset_at_synchronization(r):
    """A press in the record that synchronizes after a lost byte, which accepts no reset, then
    the press held, a release, and a press."""
    r.to_normal()
    r.mark()
    s = r.one(r.ex(chunks=lose), 0, FAULT, {0x1001, 0x1003}, answered=UNANSWERED, current=False)
    code = s.answer.code
    w = r.world
    w.run, w.reset = False, True
    r.one(r.ex(), 0, FAULT, code)
    r.one(r.ex(), 0, FAULT, code)
    w.reset = False
    r.one(r.ex(), 0, FAULT, code)
    w.reset = True
    r.one(r.ex(), 0, STANDBY, 0)
    w.reset = False


def precharge_limit(r):
    """A precharge whose records report the bus 501 mV below the pack until NEG and PRE report
    closed, and then 500 mV below it."""
    r.to_normal()
    r.mark()
    w = r.world
    w.run = False
    r.one(r.ex(), 0, STANDBY, 0)
    r.one(r.ex(), 0, STANDBY, 0)
    w.run = True
    r.one(r.ex(), 0x03, PRECHARGE, 0)
    for _ in range(3):
        r.one(r.ex(edit=lambda v: v.__setitem__("bus", v["pack"] - 501)), 0x03, PRECHARGE, 0)
        if r.record().digital & 0b011 == 0b011:
            break
    else:
        r.fail("NEG and PRE did not close")
    r.one(r.ex(edit=lambda v: v.__setitem__("bus", v["pack"] - 500)), 0x05, NORMAL, 0)


def board_reset_slow(r):
    """A board reset in NORMAL with NEG and POS releasing in SLOW_RELEASE: the records of
    segments 0 to 2 may report them closed, and segment 3 gets 0x3001 if it does."""
    r.need_reset()
    r.to_normal()
    r.mark()
    for k in (NEG, POS):
        r.world.change(r.bridge.now(), k, release=SLOW_RELEASE)
    r.bridge.reset_board()
    for k in range(4):
        seen = r.ex()
        if k == 3 and r.record().digital & 0b111:
            r.one(seen, 0, FAULT, 0x3001, board=k)
        else:
            r.one(seen, 0, RESET_REQUIRED, 0x0001, board=k)


def board_reset_cut(r):
    r.need_reset()
    r.to_normal()
    r.mark()
    s = r.one(r.ex(chunks=lambda w: [w[:18], BOARD_RESET, w[18:]]), 0, FAULT, {0x1001, 0x1003},
              answered=UNANSWERED, current=False, board=0)
    r.coils(0)
    r.one(r.ex(), 0, FAULT, s.answer.code, board=1)


def lose(w):
    p = data_position(w)
    return [w[:p] + w[p + 1:]]


def insert(w):
    p = data_position(w)
    return [w[:p] + b"\x55" + w[p:]]


def change(w):
    p = data_position(w)
    return [w[:p] + bytes([w[p] % 255 + 1]) + w[p + 1:]]


SCENARIOS = {
    "normal-start": normal_start,
    "reset-held-at-boot": reset_held_at_boot,
    "reset-with-run": reset_with_run,
    "restart-after-standby": restart_after_standby,
    "cell-overvoltage": limit_scenario(cell(0, 3650), cell(0, 3651), 0x2002),
    "cell-undervoltage": limit_scenario(cell(1, 2500), cell(1, 2499), 0x2003),
    "overtemperature": limit_scenario(temp(0, 550), temp(0, 551), 0x2004),
    "undertemperature": limit_scenario(temp(1, -200), temp(1, -201), 0x2005),
    "charge-overcurrent": limit_scenario(current(280_000), current(280_001), 0x2006),
    "discharge-overcurrent": limit_scenario(current(-280_000), current(-280_001), 0x2007),
    "cold-charge": limit_scenario(temp(0, 0, 2801), temp(0, -1, 2801), 0x2008),
    "hot-charge": limit_scenario(temp(1, 450, 2801), temp(1, 451, 2801), 0x2008),
    "thermistor-open": limit_scenario(None, temp(0, -500), 0x2001),
    "sum-mismatch": limit_scenario(pack_above_sum(300), pack_above_sum(301), 0x2009),
    "reserved-bit": limit_scenario(None, reserved, 0x1007),
    "lost-byte": comm_fault(lose, {0x1001, 0x1003}),
    "lost-delimiter": lost_delimiter,
    "inserted-byte": comm_fault(insert, 0x1002),
    "inserted-byte-between-records": inserted_between,
    "changed-byte": comm_fault(change, 0x1004),
    "byte-changed-to-zero": zero_byte,
    "wrong-link": comm_fault(None, 0x1004, raw_edit=wrong_link),
    "wrong-tag": wrong_tag_scenario,
    "repeated-record": repeated_record,
    "skipped-number": skipped_number,
    "lost-answers": lost_answers,
    "bridge-silent": bridge_silent,
    "welded-contactor": welded_contactor,
    "contactor-fails-to-close": fails_to_close,
    "precharge-failure": precharge_failure,
    "stop": stop,
    "standby-request": standby_request,
    "board-reset-in-normal": board_reset_normal,
    "board-reset-during-record": board_reset_cut,
    "reset-at-synchronization": reset_at_synchronization,
    "precharge-limit": precharge_limit,
    "board-reset-slow-contacts": board_reset_slow,
}


def summary(trace):
    """The answers as runs of equal permit, state, and code."""
    runs = []
    for a in trace:
        if runs and runs[-1][0] == str(a):
            runs[-1][1] += 1
        else:
            runs.append([str(a), 1])
    return ", ".join(s if n == 1 else f"{s} x{n}" for s, n in runs)


def play(link, world, log, names):
    bridge = Bridge(link, world, log)
    if link.start_delay:
        bridge.idle(link.start_delay)
    bridge.power_up()
    r = Run(bridge, world, link)
    results = []
    for name in names:
        log.event(bridge.now(), "scenario", name)
        try:
            SCENARIOS[name](r)
            results.append(("pass", name, summary(r.trace)))
        except Skip as e:
            results.append(("skip", name, str(e)))
        except ScenarioFailure as e:
            results.append(("fail", name, f"{e}; answers {summary(r.trace)}"))
        log.event(bridge.now(), "result", f"{name} {results[-1][0]}")
        world.clear_faults(bridge.now())
        bridge.drop = False
    return results, bridge


def replay(prefix):
    """Feeds the bytes of PREFIX.in through the Python machine, from a board reset at the start
    and at each line "reset", and compares its answers with the lines of PREFIX.out.  Returns the
    number of answers."""
    with open(prefix + ".in") as f:
        ins = f.read().split()
    with open(prefix + ".out") as f:
        outs = f.read().split()
    board, expected = bp.Board(), []
    for line in ins:
        if line == "reset":
            expected.append(line)
            board = bp.Board()
            continue
        for b in bytes.fromhex(line):
            frame = board.push(b)
            if frame:
                expected.append(frame.hex())
    for i, (e, o) in enumerate(zip(expected, outs)):
        if e != o:
            raise Failure(f"line {i + 1} of {prefix}.out is {o}, and the mirror gives {e}")
    if len(expected) != len(outs):
        raise Failure(f"{prefix}.out has {len(outs)} lines, and the mirror gives {len(expected)}")
    return sum(line != "reset" for line in outs)


def finish(results, bridge, prefix, extra):
    for status, name, text in results:
        print(f"{status}: {name}: {text}")
    count = lambda s: sum(r[0] == s for r in results)
    problems = []
    if bridge.lag > T_ACT + 1e-9:
        problems.append(f"a relay released {1000 * bridge.lag:.1f} ms after its lease ended")
    if bridge.sample_lag > T_SAMPLE + 1e-9:
        problems.append(f"a sampling or a first byte {1000 * bridge.sample_lag:.1f} ms late")
    problems += extra
    try:
        answers = f"{replay(prefix)} answers equal to the mirror's replay of {prefix}.in"
    except Failure as e:
        answers = "a replay that differs"
        problems.append(str(e))
    print(f"{len(results)} scenarios: {count('pass')} passed, {count('fail')} failed, "
          f"{count('skip')} skipped; {bridge.sent} records, {answers}, {bridge.timeouts} "
          f"timeouts; sampling to the current answer at most "
          f"{1000 * max(bridge.exchange_times, default=0):.1f} ms in exchanges without a "
          f"channel fault, a lease renewed at least {1000 * min(bridge.margins, default=0):.1f} "
          f"ms before its end, relays released at most {1000 * bridge.lag:.1f} ms after a "
          f"lease's end, sampling and first byte at most {1000 * bridge.sample_lag:.1f} ms late")
    for p in problems:
        print(f"fail: {p}")
    return 0 if count("fail") == 0 and not problems else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("mirror", "qemu", "device"):
        p = sub.add_parser(name)
        p.add_argument("--scenario", action="append", choices=list(SCENARIOS))
        p.add_argument("--seed", type=int, default=1)
        if name == "mirror":
            p.add_argument("--step", type=float, default=1.0)
        else:
            p.add_argument("--timeout", type=float, default=120)
            p.add_argument("--start-delay", type=float, default=3.0 if name == "qemu" else 0.0)
        if name == "device":
            p.add_argument("--baud", type=int, default=4800)
            p.add_argument("--reset-command")
            p.add_argument("--reopen", action="store_true")
            p.add_argument("--pace", action="store_true")
            p.add_argument("device")
        p.add_argument("prefix")
        if name == "qemu":
            p.add_argument("log")
            p.add_argument("qemu", nargs=argparse.REMAINDER)
    sub.add_parser("replay").add_argument("prefix")
    sub.add_parser("list")
    args = parser.parse_args()
    if args.command == "list":
        print("\n".join(SCENARIOS))
        return 0
    if args.command == "replay":
        try:
            print(f"{replay(args.prefix)} answers equal to the mirror's replay of "
                  f"{args.prefix}.in")
        except Failure as e:
            print(e)
            return 1
        return 0
    names = args.scenario or list(SCENARIOS)
    world = World(args.seed)
    log = Log(args.prefix)
    try:
        if args.command == "mirror":
            if not 0 < args.step <= 1000 * T_SAMPLE:
                parser.error(f"STEP must lie in (0, {1000 * T_SAMPLE:g}]")
            link = SimLink(args.step / 1000)
            try:
                results, bridge = play(link, world, log, names)
            except Failure as e:
                print(e)
                return 1
            extra = [f"{link.board.lost} bytes lost in USART_RDR"] if link.board.lost else []
        else:
            def session(conn, trace):
                if args.command == "qemu":
                    link = RealLink(conn, BYTE_TIME, True, start_delay=args.start_delay)
                else:
                    def reopen(service):
                        deadline = time.monotonic() + REOPEN_WAIT
                        while True:
                            try:
                                return Serial(args.device, args.baud, args.timeout)
                            except OSError as e:
                                if time.monotonic() > deadline:
                                    raise Failure(f"{args.device} did not reopen: {e}")
                            service()
                            time.sleep(0.01)

                    link = RealLink(conn, 10 / args.baud, args.pace, args.reset_command,
                                    reopen if args.reopen else None, args.start_delay)
                return play(link, world, log, names)

            if args.command == "qemu":
                if not args.qemu:
                    parser.error("QEMU is missing")
                result, error, _, early, status = serve(args.qemu, args.log, args.timeout,
                                                        session)
                failure = report(error, early, status)
            else:
                result, error, _ = serve_device(args.device, args.baud, args.timeout, session)
                failure = str(error) if error else None
            if failure:
                print(failure)
                return 1
            (results, bridge), extra = result, []
    finally:
        log.close()
    return finish(results, bridge, args.prefix, extra)


if __name__ == "__main__":
    sys.exit(main())
