# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The replay tool of the energy authorizer.

The tool implements the acceptance rule of energy-controller-plan.md a second time, apart from the
Lean program, with exact integer arithmetic, and runs it on cases and on historical data.

    uv run tests/energy/replay.py check CASES
    uv run tests/energy/replay.py prepare NIST_YEAR_DIR SERIES
    uv run tests/energy/replay.py margins CALIBRATION EVALUATION
    uv run tests/energy/replay.py economics CALIBRATION EVALUATION --window W [--open-caps]
    uv run tests/energy/replay.py calibration CALIBRATION --window W
    uv run tests/energy/replay.py within NET_LOAD_FILE PV_FILE

`check` compares the decisions of the module cases that `lake exe verified-cases-energy` prints
with the tool's decisions for the test site's profile.  `prepare` reads the minute files of one
test year of NIST's Net-Zero Energy Residential Test Facility and writes the house's load and PV
power for each minute.  `margins` replays the self-consumption rule through the authorizer for
each window length, tracking tolerance, efficiency bound, interval rule, and set of grid caps,
and `economics` compares the bills of the dispatch policies.  Both calibrate the causal interval
rule on the first series and report on the second, and `calibration` prints that rule's widening.
`within` compares one-second extremes with minute extremes in one house-year of PTProsumer data.
"""
import argparse
import csv
import dataclasses
import gzip
import math
import sys
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timedelta
from fractions import Fraction

OFFSET = 2**32
POWER_BOUND = 2**20
ENERGY_BOUND = 2**42
TIME_BOUND = 2**40
STATUSES = ["accepted", "length", "version", "range", "order", "power", "exportCap", "floor",
            "importCap", "ceiling"]


@dataclass(frozen=True)
class Profile:
    floor: int
    ceiling: int
    charge_max: int
    discharge_max: int
    import_cap: int
    export_cap: int
    eta: int
    loss_max: int
    tolerance: int
    fallback_low: int
    fallback_high: int
    transition: int
    window: int
    send_deadline: int


SITE = Profile(floor=10_800_000, ceiling=34_200_000, charge_max=5000, discharge_max=5000,
               import_cap=5000, export_cap=2000, eta=900_000, loss_max=20, tolerance=50,
               fallback_low=-50, fallback_high=50, transition=30, window=900, send_deadline=60)


@dataclass(frozen=True)
class Snapshot:
    """A snapshot in signed units: the state in force is `None` for fallback, or the limits of a
    command, which for a setpoint `s` are `(s, s)`."""
    time: int
    energy_low: int
    energy_high: int
    held: tuple[int, int] | None
    load_low: int
    load_high: int
    pv_low: int
    pv_high: int


def power_bounds(p: Profile, q: Snapshot, low: int, high: int) -> tuple[int, int]:
    """The window's power interval `B`: the hull of the state in force, `[low - e, high + e]`,
    and `F`, where a setpoint `s` has `low = high = s`."""
    e = p.tolerance
    held = ((p.fallback_low, p.fallback_high) if q.held is None
            else (q.held[0] - e, q.held[1] + e))
    return min(held[0], low - e, p.fallback_low), max(held[1], high + e, p.fallback_high)


def drain_low(p: Profile, b_low: int) -> int:
    """`⌈|B⁻| · W · 10^6 / η⌉ + ℓ⁺ · W`, the ceiling taken as the negated floor of the
    negation."""
    return -(b_low * p.window * 1_000_000 // p.eta) + p.loss_max * p.window


def decide(p: Profile, q: Snapshot, low: int, high: int) -> str:
    """The side tests of the acceptance rule for a valid snapshot and command limits within the
    setpoint limits."""
    b_low, b_high = power_bounds(p, q, low, high)
    if b_low < p.fallback_low:
        if q.load_low + b_low + p.export_cap < q.pv_high:
            return "exportCap"
        if not (p.floor <= q.energy_low and p.floor + drain_low(p, b_low) <= q.energy_low):
            return "floor"
    if b_high > p.fallback_high:
        if q.load_high + b_high > p.import_cap + q.pv_low:
            return "importCap"
        if not (q.energy_high <= p.ceiling and q.energy_high + b_high * p.window <= p.ceiling):
            return "ceiling"
    return "accepted"


def authorize(p: Profile, words: list[int]) -> tuple[str, int, int]:
    """The status, setpoint word, and expiry that the authorizer returns for input words."""
    if len(words) != 11:
        return "length", 0, 0
    if words[0] != 1:
        return "version", 0, 0
    _, time, e_lo, e_hi, mode, held, l_lo, l_hi, s_lo, s_hi, proposal = words

    def power_word(w: int) -> bool:
        return abs(w - OFFSET) <= POWER_BOUND

    if not (time < TIME_BOUND and e_lo <= ENERGY_BOUND and e_hi <= ENERGY_BOUND and mode <= 1
            and power_word(held) and power_word(proposal)
            and all(x <= POWER_BOUND for x in (l_lo, l_hi, s_lo, s_hi))):
        return "range", 0, 0
    if not (e_lo <= e_hi and l_lo <= l_hi and s_lo <= s_hi):
        return "order", 0, 0
    s = proposal - OFFSET
    if not (-p.discharge_max <= s <= p.charge_max):
        return "power", 0, 0
    q = Snapshot(time, e_lo, e_hi, None if mode == 1 else (held - OFFSET, held - OFFSET),
                 l_lo, l_hi, s_lo, s_hi)
    status = decide(p, q, s, s)
    if status != "accepted":
        return status, 0, 0
    return status, proposal, time + p.window - p.transition


def accepted_range(p: Profile, q: Snapshot) -> tuple[int, int] | None:
    """The largest discharge and the largest charge that the rule accepts, or `None` when it
    accepts no setpoint.  When `F` contains `[-e, e]` the accepted setpoints form an interval
    that contains 0 whenever it is not empty, because `B⁻` falls and `B⁺` rises with `s`.  The
    lower side depends only on the lower limit and the upper side only on the upper limit, so the
    two results are also the widest limits that the rule accepts."""
    if decide(p, q, 0, 0) != "accepted":
        return None
    lo, hi = 0, p.charge_max
    while lo < hi:
        mid = (lo + hi + 1) // 2
        lo, hi = (mid, hi) if decide(p, q, mid, mid) == "accepted" else (lo, mid - 1)
    charge = lo
    lo, hi = 0, p.discharge_max
    while lo < hi:
        mid = (lo + hi + 1) // 2
        lo, hi = (mid, hi) if decide(p, q, -mid, -mid) == "accepted" else (lo, mid - 1)
    return -lo, charge


def check(path: str) -> int:
    failures = 0
    count = 0
    with open(path) as f:
        for line in f:
            fields = line.rstrip("\n").split("|")
            if len(fields) != 6 or fields[0] != "energy" or fields[1] != "authorize":
                raise ValueError(f"not an energy case: {line!r}")
            text = fields[3].removeprefix("array-u64:")
            words = [int(w) for w in text.split(",")] if text else []
            index, setpoint, expiry = map(int, fields[4].split())
            got = authorize(SITE, words)
            count += 1
            if (STATUSES.index(got[0]), got[1], got[2]) != (index, setpoint, expiry):
                failures += 1
                print(f"mismatch: {words}: module {index} {setpoint} {expiry}, replay {got}")
    print(f"replay check: {count} cases, {failures} mismatches")
    return 1 if failures else 0


# The NIST test house.  Load is the sum of the channels below: every circuit of the house, the
# heat pump, the dehumidifier, the water heater, and the oven, without the facility's
# instrumentation, its emulators of the occupants' heat and moisture, the water heater's
# single-leg circuit, which `DHW_HeatPumpWaterHeaterPowerTotal` covers, and the `Load` channels
# that sum circuits.  PV is the power that the inverters feed into the panel.  A channel that is
# empty for a whole year is absent from that year.  A minute in which another channel reads below
# -100 W or is empty is missing, and so is every minute of a day with more than 60 such minutes.
ELEC_EXCLUDED = {
    "Elec_PowerPV1of2", "Elec_PowerPV2of2", "Elec_PowerHeatPumpWH1of2", "Elec_PowerHeatPumpWH2of2",
    "Elec_PowerParentADownstairs", "Elec_PowerParentBDownstairs", "Elec_PowerParentAUpstairs",
    "Elec_PowerParentBUpstairs", "Elec_PowerChildADownstairs", "Elec_PowerChildBDownstairs",
    "Elec_PowerChildAUpstairs", "Elec_PowerChildBUpstairs", "Elec_PowerHeatLoadforRefrigerator",
    "Elec_PowerLightingControlPanelRPS1", "Elec_PowerLightingControlPanelRPS2",
}
LOAD_CHANNELS = {
    "HVAC": ["HVAC_HeatPumpIndoorUnitPower", "HVAC_HeatPumpOutdoorUnitPower",
             "HVAC_DehumidifierPower"],
    "DHW": ["DHW_HeatPumpWaterHeaterPowerTotal"],
    "Load": ["Load_OvenPowerTotal"],
}
PV_CHANNELS = {"Elec": ["Elec_PowerPV1of2", "Elec_PowerPV2of2"]}
ERROR_READING = -100
BAD_DAY = 60


def load_names(name: str, head: list[str]) -> list[str]:
    if name == "Elec":
        return [h for h in head if h.startswith("Elec_Power") and h not in ELEC_EXCLUDED
                and not h.startswith("Elec_PowerPlugsInst") and "Instrumentation" not in h]
    return LOAD_CHANNELS.get(name, [])


def prepare(directory: str, out: str) -> int:
    rows: dict[int, list] = {}
    files = ["Elec", "HVAC", "DHW", "Load"]
    empty: dict[str, int] = {}
    count: dict[str, int] = {}
    for name in files:
        with open(f"{directory}/{name}-minute.csv", newline="") as f:
            reader = csv.reader(f)
            head = next(reader)
            names = load_names(name, head) + PV_CHANNELS.get(name, [])
            pv = set(PV_CHANNELS.get(name, []))
            cols = [(c, head.index(c), c in pv) for c in names]
            for row in reader:
                count[name] = count.get(name, 0) + 1
                stamp = datetime.fromisoformat(row[0]).replace(second=0)
                minute = int(stamp.timestamp()) // 60
                entry = rows.setdefault(minute, [stamp, 0.0, 0.0, set(), set()])
                entry[3].add(name)
                for c, i, is_pv in cols:
                    if row[i] == "":
                        empty[c] = empty.get(c, 0) + 1
                        entry[4].add(c)
                        continue
                    v = float(row[i])
                    entry[2 if is_pv else 1] += v
                    if v < ERROR_READING:
                        entry[4].add(c)
    absent = {c for c, n in empty.items() if n == count[c.split("_")[0]]}
    first, last = min(rows), max(rows)
    errors: dict = {}
    for entry in rows.values():
        entry[4] -= absent
        errors[entry[0].date()] = errors.get(entry[0].date(), 0) + bool(entry[4])
    bad_days = {day for day, n in errors.items() if n > BAD_DAY}
    missing = negative = dropped = 0
    energy = [0.0, 0.0]
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["minute", "local", "load", "pv"])
        for minute in range(first, last + 1):
            entry = rows.get(minute)
            if entry is None or len(entry[3]) != len(files):
                missing += 1
                continue
            if entry[0].date() in bad_days:
                dropped += 1
                continue
            load, pv = round(entry[1]), round(entry[2])
            if entry[4] or load < 0 or pv < 0:
                negative += 1
                continue
            w.writerow([minute, entry[0].isoformat(), load, pv])
            energy[0] += load / 60_000
            energy[1] += pv / 60_000
    print(f"{out}: {last - first + 1} minutes, {missing} missing, channels empty all year "
          f"{sorted(absent)}, {len(bad_days)} days with more than {BAD_DAY} error readings "
          f"({dropped} minutes), {negative} other minutes with an error reading; "
          f"load {energy[0]:.0f} kWh, PV {energy[1]:.0f} kWh")
    return 0


@dataclass
class Series:
    """Minute values from a prepared file, with `None` for a missing minute, and the local hour
    and month of each minute."""
    hour: list[int]
    month: list[int]
    load: list[int | None]
    pv: list[int | None]


def load_series(path: str) -> Series:
    with open(path, newline="") as f:
        reader = csv.reader(f)
        next(reader)
        data = [(int(m), datetime.fromisoformat(t), int(l), int(p)) for m, t, l, p in reader]
    start = data[0][0]
    n = data[-1][0] - start + 1
    s = Series([0] * n, [0] * n, [None] * n, [None] * n)
    last = data[0]
    rows = iter(data)
    row = next(rows, None)
    for k in range(n):
        if row is not None and row[0] - start == k:
            last = row
            s.load[k], s.pv[k] = row[2], row[3]
            row = next(rows, None)
        local = last[1] + timedelta(minutes=k + start - last[0])
        s.hour[k], s.month[k] = local.hour, local.month
    return s


def sliding(xs: list[int | None], n: int) -> tuple[list, list]:
    """The minimum and maximum of `xs[i - n + 1 .. i]` for each `i`, or `None` when the range
    starts before the series or holds a missing value."""
    lo: list[int | None] = [None] * len(xs)
    hi: list[int | None] = [None] * len(xs)
    mins: deque[int] = deque()
    maxs: deque[int] = deque()
    missing = -1
    for i, x in enumerate(xs):
        if x is None:
            missing = i
            mins.clear()
            maxs.clear()
            continue
        while mins and xs[mins[-1]] >= x:
            mins.pop()
        mins.append(i)
        while maxs and xs[maxs[-1]] <= x:
            maxs.pop()
        maxs.append(i)
        start = i - n + 1
        while mins[0] < start:
            mins.popleft()
        while maxs[0] < start:
            maxs.popleft()
        if start > missing and start >= 0:
            lo[i], hi[i] = xs[mins[0]], xs[maxs[0]]
    return lo, hi


HISTORY = 15
QUANTILE = Fraction(999, 1000)


def quantile(xs: list[int], q: Fraction) -> int:
    xs = sorted(xs)
    return xs[max(0, math.ceil(q * len(xs)) - 1)]


@dataclass(frozen=True)
class Margins:
    """The causal rule's widening of each bound, by month and hour, from the excursions of the
    month and its two neighbors, so that the hours of sunrise and sunset fall in like bins."""
    load_up: list[list[int]]
    load_down: list[list[int]]
    pv_up: list[list[int]]
    pv_down: list[list[int]]


def calibrate(s: Series, minutes: int, q: Fraction = QUANTILE) -> Margins:
    def excursions(xs):
        recent = sliding(xs, HISTORY)
        future = sliding(xs, minutes)
        up = [[[] for _ in range(24)] for _ in range(12)]
        down = [[[] for _ in range(24)] for _ in range(12)]
        for k in range(HISTORY, len(xs) - minutes + 1):
            r_lo, r_hi = recent[0][k - 1], recent[1][k - 1]
            f_lo, f_hi = future[0][k + minutes - 1], future[1][k + minutes - 1]
            if r_lo is None or f_lo is None:
                continue
            up[s.month[k] - 1][s.hour[k]].append(f_hi - r_hi)
            down[s.month[k] - 1][s.hour[k]].append(r_lo - f_lo)

        def widen(bins):
            return [[max(0, quantile(bins[m - 1][h] + bins[m][h] + bins[(m + 1) % 12][h], q))
                     for h in range(24)] for m in range(12)]
        return widen(up), widen(down)

    load_up, load_down = excursions(s.load)
    pv_up, pv_down = excursions(s.pv)
    return Margins(load_up, load_down, pv_up, pv_down)


@dataclass
class Intervals:
    """The load and PV intervals of a snapshot at each minute, and whether the minute values of
    its window lie inside them."""
    bounds: list[tuple[int, int, int, int] | None]
    covered: list[bool]


def intervals(s: Series, minutes: int, margins: Margins | None) -> Intervals:
    n = len(s.load)
    f_load = sliding(s.load, minutes)
    f_pv = sliding(s.pv, minutes)
    r_load = sliding(s.load, HISTORY)
    r_pv = sliding(s.pv, HISTORY)
    bounds: list = [None] * n
    covered = [False] * n
    for k in range(HISTORY, n - minutes + 1):
        end = k + minutes - 1
        if margins is None:
            if f_load[0][end] is None or f_pv[0][end] is None:
                continue
            b = (f_load[0][end], f_load[1][end], f_pv[0][end], f_pv[1][end])
        else:
            if r_load[0][k - 1] is None or r_pv[0][k - 1] is None:
                continue
            m, h = s.month[k] - 1, s.hour[k]
            b = (max(0, r_load[0][k - 1] - margins.load_down[m][h]),
                 min(POWER_BOUND, r_load[1][k - 1] + margins.load_up[m][h]),
                 max(0, r_pv[0][k - 1] - margins.pv_down[m][h]),
                 min(POWER_BOUND, r_pv[1][k - 1] + margins.pv_up[m][h]))
        bounds[k] = b
        covered[k] = (f_load[0][end] is not None and f_pv[0][end] is not None
                      and b[0] <= f_load[0][end] and f_load[1][end] <= b[1]
                      and b[2] <= f_pv[0][end] and f_pv[1][end] <= b[3])
    return Intervals(bounds, covered)


# The simulated site: the worked example's battery with caps that the test house's largest loads
# and its PV array's output on clear days each break when the battery is idle.
STUDY = dataclasses.replace(SITE, import_cap=10_000, export_cap=5000, window=300)
CAPACITY = 36_000_000
ETA_CHARGE = ETA_DISCHARGE = 0.95
LOSS = 10
ENERGY_ERROR = 360_000
START_ENERGY = 22_500_000


@dataclass(frozen=True)
class Plant:
    """The simulated battery: its efficiencies and loss, the offset of its power from the state in
    force, and where its energy lies in the snapshot's interval of width `2 * ENERGY_ERROR`: -1 at
    the lower end, 0 in the middle, 1 at the upper end."""
    eta_charge: float = ETA_CHARGE
    eta_discharge: float = ETA_DISCHARGE
    loss: float = LOSS
    offset: int = 0
    position: int = 0

    def rate(self, b: float) -> float:
        return (self.eta_charge * b if b >= 0 else b / self.eta_discharge) - self.loss

    def step(self, energy: float, b: float) -> tuple[float, float]:
        """The power after the BMS cutoffs at 0 and `CAPACITY`, and the energy one minute
        later."""
        after = energy + 60 * self.rate(b)
        if after > CAPACITY and b > 0:
            b = max(0.0, ((CAPACITY - energy) / 60 + self.loss) / self.eta_charge)
        elif after < 0 and b < 0:
            b = min(0.0, (self.loss - energy / 60) * self.eta_discharge)
        return b, min(CAPACITY, max(0.0, energy + 60 * self.rate(b)))

    def interval(self, energy: float) -> tuple[int, int]:
        low = math.floor(energy - (1 + self.position) * ENERGY_ERROR)
        return max(0, low), math.ceil(energy + (1 - self.position) * ENERGY_ERROR)


NOMINAL = Plant()


def extremes(p: Profile) -> list[Plant]:
    """The plants at the premises' extremes.  On the lower side power is `s - e`, both
    efficiencies are `η`, the loss is `ℓ⁺`, and the energy lies at the lower end of its interval.
    On the upper side power is `s + e`, both efficiencies are 1, there is no loss, and the energy
    lies at the upper end."""
    eta = p.eta / 1_000_000
    return [Plant(eta, eta, p.loss_max, -p.tolerance, -1), Plant(1.0, 1.0, 0, p.tolerance, 1)]


def fallback_breaks(p: Profile, q: Snapshot) -> tuple[bool, bool, bool, bool]:
    """Whether the worst case of an immediate return to fallback breaks the floor, the ceiling,
    the export cap, and the import cap within the window."""
    return (q.energy_low < p.floor or q.energy_low - drain_low(p, p.fallback_low) < p.floor,
            q.energy_high > p.ceiling or q.energy_high + p.fallback_high * p.window > p.ceiling,
            q.load_low + p.fallback_low + p.export_cap < q.pv_high,
            q.load_high + p.fallback_high > p.import_cap + q.pv_low)


def within_or_fallback(p: Profile, q: Snapshot, elapsed: int, energy: float, grid: float) -> bool:
    """`WithinOrFallback` of the specification at `elapsed` seconds after the snapshot."""
    eff = p.eta / 1_000_000
    low = p.fallback_low / eff if p.fallback_low < 0 else eff * p.fallback_low
    slack = 1e-6
    return (min(p.floor, q.energy_low + (low - p.loss_max) * elapsed) - slack <= energy
            <= max(p.ceiling, q.energy_high + p.fallback_high * elapsed) + slack
            and min(-p.export_cap, q.load_low + p.fallback_low - q.pv_high) - slack <= grid
            <= max(p.import_cap, q.load_high + p.fallback_high - q.pv_low) + slack)


SUMMER = {6, 7, 8, 9}
PRICES = {True: {"off": 0.33, "partial": 0.39, "peak": 0.55},
          False: {"off": 0.28, "partial": 0.30, "peak": 0.32}}
EXPORT_CREDIT = 0.05
WEAR = 0.05  # $400 per kWh of capacity over 8,000 full cycles, per kWh discharged


def period(hour: int) -> str:
    return "peak" if 16 <= hour < 21 else "partial" if hour == 15 or hour >= 21 else "off"


@dataclass
class Command:
    low: int
    high: int
    expiry: int
    bounds: tuple[int, int, int, int]


@dataclass
class Window:
    start: int
    q: Snapshot
    b_low: int
    b_high: int


@dataclass
class Totals:
    minutes: int = 0
    snapshots: int = 0
    skipped: int = 0
    accepted: int = 0
    statuses: dict = dataclasses.field(default_factory=dict)
    no_setpoint: int = 0
    charge: list = dataclasses.field(default_factory=list)
    discharge: list = dataclasses.field(default_factory=list)
    breaks: list = dataclasses.field(default_factory=lambda: [0, 0, 0, 0])
    covered: int = 0
    by_month: list = dataclasses.field(default_factory=lambda: [[0, 0] for _ in range(12)])
    run_on: float = 0.0
    checks: int = 0
    violations: int = 0
    premise_failures: int = 0
    unchecked_breaks: int = 0
    cutoffs: int = 0
    fallbacks: int = 0
    cost: float = 0.0
    imported: float = 0.0
    exported: float = 0.0
    curtailed: float = 0.0
    discharged: float = 0.0
    lowest: float = math.inf
    below_floor: int = 0


def account(t: Totals, p: Profile, s: Series, k: int, b: float, energy: float) -> None:
    """Adds minute `k`'s grid exchange, battery throughput, and reserve to the totals."""
    grid = s.load[k] + b - s.pv[k]
    exported = min(-grid, p.export_cap) if grid < 0 else 0.0
    imported = max(grid, 0.0)
    t.minutes += 1
    t.imported += imported / 60_000
    t.exported += exported / 60_000
    t.curtailed += (max(-grid, 0.0) - exported) / 60_000
    t.cost += (imported * PRICES[s.month[k] in SUMMER][period(s.hour[k])]
               - exported * EXPORT_CREDIT) / 60_000
    t.discharged += max(-b, 0.0) / 60_000
    t.lowest = min(t.lowest, energy - p.floor)
    t.below_floor += energy < p.floor


def replay(p: Profile, s: Series, iv: Intervals, propose, margins: bool, gate: bool = True,
           plant: Plant = NOMINAL, follow: bool = False) -> Totals:
    """Replays the gateway's rules with one snapshot a minute.  `propose(k, q, energy)` returns
    command limits, `(s, s)` for a setpoint `s`, or `None`.  The device follows a command from the
    start of its snapshot's minute until its expiry and runs in the idle fallback otherwise.  A
    setpoint holds its power, and with `follow` the device's own self-consumption mode follows
    each minute's net load within the limits, the floor, and the ceiling, and idles within the
    limits when the minute's data are missing.  Each accepted window's
    conclusion is checked at the end of every minute up to which its premises held.  Run-on is the
    energy that a command delivers after a later snapshot's proposal is rejected or absent.
    Without `gate` the gateway sends every proposal, as if the authorizer accepted it."""
    t = Totals()
    minutes = p.window // 60
    energy = float(START_ENERGY)
    command: Command | None = None
    stale = False
    power = 0.0
    windows: list[Window] = []
    for k in range(1, len(s.load)):
        held = (command.low, command.high) if command else None
        in_state = (held[0] - p.tolerance <= power <= held[1] + p.tolerance if held is not None
                    else p.fallback_low <= power <= p.fallback_high)
        if iv.bounds[k] is not None and s.load[k - 1] is not None:
            if not in_state:
                t.skipped += 1
            else:
                q = Snapshot(60 * k, *plant.interval(energy), held, *iv.bounds[k])
                t.snapshots += 1
                t.covered += iv.covered[k]
                t.by_month[s.month[k] - 1][0] += 1
                t.by_month[s.month[k] - 1][1] += iv.covered[k]
                for i, broken in enumerate(fallback_breaks(p, q)):
                    t.breaks[i] += broken
                if margins:
                    r = accepted_range(p, q)
                    t.no_setpoint += r is None
                    t.discharge.append(-r[0] if r else 0)
                    t.charge.append(r[1] if r else 0)
                limits = propose(k, q, energy)
                stale = True
                if limits is not None:
                    status = decide(p, q, *limits) if gate else "accepted"
                    t.statuses[status] = t.statuses.get(status, 0) + 1
                    if status == "accepted":
                        t.accepted += 1
                        stale = False
                        command = Command(*limits, 60 * k + p.window - p.transition,
                                          iv.bounds[k])
                        b_low, b_high = power_bounds(p, q, *limits)
                        if gate:
                            windows.append(Window(k, q, b_low, b_high))
        if command and 60 * k >= command.expiry:
            command = None
        target = 0
        if command and follow:
            net = s.pv[k] - s.load[k] if s.load[k] is not None else 0
            net = min(net, max(0.0, ((p.ceiling - energy) / 60 + LOSS) / ETA_CHARGE))
            net = max(net, min(0.0, ((p.floor - energy) / 60 + LOSS) * ETA_DISCHARGE))
            target = min(command.high, max(command.low, net))
        elif command:
            target = command.low
        target += plant.offset
        power, after = plant.step(energy, target)
        t.cutoffs += power != target
        if command and stale:
            t.run_on += abs(power) / 60_000
        known = s.load[k] is not None
        grid = s.load[k] + power - s.pv[k] if known else 0.0
        still = []
        for w in windows:
            q = w.q
            if not (known and w.b_low <= power <= w.b_high
                    and q.load_low <= s.load[k] <= q.load_high
                    and q.pv_low <= s.pv[k] <= q.pv_high):
                t.premise_failures += 1
                if known and not within_or_fallback(p, q, 60 * (k + 1 - w.start), after, grid):
                    t.unchecked_breaks += 1
                continue
            t.checks += 1
            t.violations += not within_or_fallback(p, q, 60 * (k + 1 - w.start), after, grid)
            if k + 1 - w.start < minutes:
                still.append(w)
        windows = still
        if known:
            account(t, p, s, k, power, after)
        if command and not (known and command.bounds[0] <= s.load[k] <= command.bounds[1]
                            and command.bounds[2] <= s.pv[k] <= command.bounds[3]):
            command = None
            t.fallbacks += 1
        energy = after
    return t


def extreme_proposer(p: Profile):
    """A proposer for the replay at the premises' extremes: the largest accepted discharge in even
    hours and the largest accepted charge in odd hours, which drives the energy against the floor
    and the ceiling."""
    def propose(k: int, q: Snapshot, energy: float) -> tuple[int, int] | None:
        r = accepted_range(p, q)
        return None if r is None else (r[(k // 60) % 2],) * 2
    return propose


def authorized_limits(p: Profile):
    """Power limits for the device's own self-consumption mode: the widest that the acceptance
    rule accepts."""
    def propose(k: int, q: Snapshot, energy: float) -> tuple[int, int] | None:
        return accepted_range(p, q)
    return propose


def self_consumption(p: Profile, s: Series):
    """The vendor's self-consumption rule as a proposer: the last minute's surplus PV or deficit,
    within the setpoint limits and the power that keeps the snapshot's estimate of the energy
    between the floor and the ceiling for one minute."""
    def propose(k: int, q: Snapshot, energy: float) -> tuple[int, int]:
        estimate = (q.energy_low + q.energy_high) / 2
        net = s.pv[k - 1] - s.load[k - 1]
        if net > 0:
            v = min(net, p.charge_max,
                    max(0, int(((p.ceiling - estimate) / 60 + LOSS) / ETA_CHARGE)))
        else:
            v = max(net, -p.discharge_max,
                    min(0, -int(((estimate - p.floor) / 60 - LOSS) * ETA_DISCHARGE)))
        return v, v
    return propose


def vendor(p: Profile, s: Series, schedule: bool) -> Totals:
    """The vendor's self-consumption mode, or with `schedule` the fixed time-of-use schedule, which
    discharges only during partial peak and peak.  Both track the present minute's net load
    between the floor and the ceiling, without the authorizer."""
    t = Totals()
    energy = float(START_ENERGY)
    for k in range(1, len(s.load)):
        b = 0.0
        if s.load[k] is not None:
            net = s.pv[k] - s.load[k]
            if net > 0:
                b = min(net, p.charge_max,
                        max(0.0, ((p.ceiling - energy) / 60 + LOSS) / ETA_CHARGE))
            elif not schedule or period(s.hour[k]) != "off":
                b = max(net, -p.discharge_max,
                        min(0.0, ((p.floor - energy) / 60 + LOSS) * ETA_DISCHARGE))
        b, after = NOMINAL.step(energy, b)
        if s.load[k] is not None:
            account(t, p, s, k, b, after)
        energy = after
    return t


def look_behind(s: Series) -> tuple[list[float], list[int]]:
    """For each minute before 3 p.m., from the same minutes of the previous day up to 3 p.m.: the
    energy that surplus PV stored, and the largest surplus."""
    n = len(s.load)
    store = [0.0] * n
    peak = [0] * n
    acc, top = 0.0, 0
    for k in range(n - 1, -1, -1):
        if k + 1 < n and s.hour[k + 1] == 0 and s.hour[k] == 23:
            acc, top = 0.0, 0
        j = k - 1440
        if s.hour[k] < 15 and j >= 0 and s.load[j] is not None:
            acc += max(s.pv[j] - s.load[j], 0) * 60 * ETA_CHARGE
            top = max(top, s.pv[j] - s.load[j])
        store[k], peak[k] = acc, top
    return store, peak


def controller(p: Profile, s: Series, limit: bool, unlimited: list[int]):
    """The rule-based optimizer: the self-consumption rule, except that before 3 p.m., when the
    look-behind forecast has a surplus within 1,000 W of the export cap and stores half again the
    room left below the ceiling, it charges only the surplus within 1,000 W of the cap, so that
    the battery takes PV that the cap would curtail.  Every proposal stays within the power that
    keeps the snapshot's estimate of the energy between the floor and the ceiling for one minute,
    and with `limit` within the range that the acceptance rule accepts."""
    store, peak = look_behind(s)
    plain = self_consumption(p, s)

    def propose(k: int, q: Snapshot, energy: float) -> tuple[int, int] | None:
        want = plain(k, q, energy)[0]
        if (want > 0 and s.hour[k] < 15 and peak[k] > p.export_cap - 1000
                and store[k] > 1.5 * (p.ceiling - energy)):
            want = min(want, max(0, s.pv[k - 1] - s.load[k - 1] - p.export_cap + 1000))
        unlimited[0] += 1
        unlimited[1] += decide(p, q, want, want) == "accepted"
        if not limit:
            return want, want
        r = accepted_range(p, q)
        return None if r is None else (max(r[0], min(r[1], want)),) * 2
    return propose


def percent(a: float, b: float) -> str:
    return f"{100 * a / b:.1f}" if b else "-"


def pct(xs: list[int], q: Fraction) -> int:
    return quantile(xs, q) if xs else 0


OPEN_CAPS = {"import_cap": POWER_BOUND, "export_cap": POWER_BOUND}


def margins_report(calibration: Series, evaluation: Series) -> None:
    """The sweep of Stage 2.  Each run is an interval rule, `W`, `e`, `η`, the causal rule's
    percentile, and whether the grid caps are the study's or caps that never bind."""
    q = QUANTILE
    runs = [(rule, w, 50, 900_000, q, False) for w in (180, 300, 600, 900)
            for rule in ("true", "causal")]
    runs += [("causal", 300, e, 900_000, q, False) for e in (25, 100, 200)]
    runs += [("causal", 300, 50, eta, q, False) for eta in (850_000, 950_000)]
    runs += [("causal", 300, 50, 900_000, Fraction(99, 100), False)]
    runs += [(rule, w, 50, 900_000, q, True) for w in (180, 900) for rule in ("true", "causal")]
    vendor_totals = vendor(STUDY, evaluation, False)
    free = replay(STUDY, evaluation, intervals(evaluation, 1, None),
                  self_consumption(STUDY, evaluation), False, gate=False)
    columns = "| Rule | Percentile | Caps | W (s) | e (W) | η (ppm) "
    dispatch = [columns + "| Discharged (kWh) | Run-on (kWh) | Import (kWh) | Export (kWh) "
                "| Curtailed (kWh) | Rejected by export, floor, import, ceiling (% of snapshots) |",
                "|" + "---|" * 12]
    for name, t in (("Vendor's mode, each minute's own values", vendor_totals),
                    ("One-minute proposer, every proposal sent", free)):
        dispatch.append(f"| {name} | | | | | | {t.discharged:,.0f} | | {t.imported:,.0f} "
                        f"| {t.exported:,.0f} | {t.curtailed:,.0f} | |")
    margin = [columns + "| Largest charge: full, none beyond F (%), median (W) "
              "| Largest discharge: full, none beyond F (%), median (W) "
              "| Fallback breaks floor, ceiling, export, import (%) | Coverage (%) "
              "| Window-minutes checked, violations | Premise failures, with a limit broken |",
              "|" + "---|" * 12]
    months = ["| Percentile | W (s) | " + " | ".join(str(m) for m in range(1, 13)) + " |",
              "|" + "---|" * 14]
    calibrated: dict = {}
    for rule, w, e, eta, pc, open_caps in runs:
        p = dataclasses.replace(STUDY, window=w, tolerance=e, fallback_low=-max(e, 50),
                                fallback_high=max(e, 50), eta=eta,
                                **(OPEN_CAPS if open_caps else {}))
        minutes = w // 60
        if rule == "causal" and (minutes, pc) not in calibrated:
            calibrated[minutes, pc] = calibrate(calibration, minutes, pc)
        iv = intervals(evaluation, minutes, calibrated[minutes, pc] if rule == "causal" else None)
        t = replay(p, evaluation, iv, self_consumption(p, evaluation), True)
        n = t.snapshots
        rejected = ", ".join(percent(t.statuses.get(x, 0), n)
                             for x in ("exportCap", "floor", "importCap", "ceiling"))
        head = (f"| {rule} | {float(pc) if rule == 'causal' else ''} "
                f"| {'open' if open_caps else 'study'} | {w} | {e} | {eta:,} ")
        dispatch.append(head + f"| {t.discharged:,.0f} | {t.run_on:,.0f} | {t.imported:,.0f} "
                        f"| {t.exported:,.0f} | {t.curtailed:,.0f} | {rejected} |")

        def spread(xs, full, inside):
            return (f"{percent(sum(x == full for x in xs), n)}, "
                    f"{percent(sum(x <= inside for x in xs), n)}, {pct(xs, Fraction(1, 2)):,}")
        breaks = ", ".join(percent(b, n) for b in t.breaks)
        margin.append(head + f"| {spread(t.charge, p.charge_max, p.fallback_high - e)} "
                      f"| {spread(t.discharge, p.discharge_max, -p.fallback_low - e)} | {breaks} "
                      f"| {percent(t.covered, n)} | {t.checks:,}, {t.violations} "
                      f"| {t.premise_failures:,}, {t.unchecked_breaks} |")
        if rule == "causal" and e == 50 and eta == 900_000 and not open_caps:
            months.append(f"| {float(pc)} | {w} | "
                          + " | ".join(percent(c, n) for n, c in t.by_month) + " |")
        print(f"{rule} {pc} {open_caps} {w} {e} {eta} done", file=sys.stderr, flush=True)
    print("\n".join(dispatch))
    print()
    print("\n".join(margin))
    print()
    print("Coverage of the causal rule by month (%):\n")
    print("\n".join(months))
    print()
    print("Replay at the premises' extremes with the true-range rule and the extreme proposer:\n")
    print("| W (s) | Side | Snapshots | Accepted | Window-minutes checked | Violations |")
    print("|---|---|---|---|---|---|")
    for w in (180, 900):
        p = dataclasses.replace(STUDY, window=w)
        iv = intervals(evaluation, w // 60, None)
        for side, plant in zip(("lower", "upper"), extremes(p)):
            t = replay(p, evaluation, iv, extreme_proposer(p), False, plant=plant)
            print(f"| {w} | {side} | {t.snapshots:,} | {t.accepted:,} | {t.checks:,} "
                  f"| {t.violations} |", flush=True)


def calibration_report(calibration: Series, minutes: int) -> None:
    m = calibrate(calibration, minutes)
    print(f"Causal rule's widening for W = {60 * minutes} s, by month and hour (W):")
    for name in ("load_up", "load_down", "pv_up", "pv_down"):
        print(f"  {name}: {getattr(m, name)}")


def economics_report(calibration: Series, evaluation: Series, windows: list[int],
                     open_caps: bool) -> None:
    """The bills of Stage 3: no battery, the vendor's two modes, and the controller through the
    authorizer with the causal rule, for each window length."""
    p = dataclasses.replace(STUDY, **(OPEN_CAPS if open_caps else {}))
    results = [("No battery", vendor(dataclasses.replace(p, charge_max=0, discharge_max=0),
                                     evaluation, False)),
               ("Self-consumption mode", vendor(p, evaluation, False)),
               ("Time-of-use schedule", vendor(p, evaluation, True)),
               ("Self-consumption rule, one-minute commands, every proposal sent",
                replay(p, evaluation, intervals(evaluation, 1, None),
                       self_consumption(p, evaluation), False, gate=False)),
               ("Controller, every proposal sent",
                replay(p, evaluation, intervals(evaluation, 1, None),
                       controller(p, evaluation, False, [0, 0]), False, gate=False))]
    notes = []
    for w in windows:
        pw = dataclasses.replace(p, window=w)
        iv = intervals(evaluation, w // 60, calibrate(calibration, w // 60))
        unlimited = [0, 0]
        t = replay(pw, evaluation, iv, controller(pw, evaluation, True, unlimited), False)
        results.append((f"Controller through the authorizer, W = {w} s", t))
        lt = replay(pw, evaluation, iv, authorized_limits(pw), False, follow=True)
        results.append((f"Self-consumption mode within authorized limits, W = {w} s", lt))
        notes.append(f"Limits, W = {w} s: {lt.snapshots:,} snapshots, {lt.accepted:,} accepted, "
                     f"run-on {lt.run_on:,.0f} kWh, window-minutes checked {lt.checks:,} with "
                     f"{lt.violations} violations")
        notes.append(f"W = {w} s: {t.snapshots:,} snapshots, {t.skipped} skipped, "
                     f"{t.accepted:,} accepted, unlimited proposals accepted "
                     f"{percent(unlimited[1], unlimited[0])}%, run-on {t.run_on:,.0f} kWh, "
                     f"returns to fallback {t.fallbacks:,}, BMS cutoffs {t.cutoffs}, "
                     f"window-minutes checked {t.checks:,} with {t.violations} violations, "
                     f"coverage by month (%) "
                     + ", ".join(percent(v, n) for n, v in t.by_month))
    print("| Policy | Bill ($) | Wear ($) | Bill and wear ($) | Import (kWh) | Export (kWh) "
          "| Curtailed (kWh) | Discharged (kWh) | Lowest energy above the floor (kWh) |")
    print("|" + "---|" * 9)
    for name, t in results:
        lowest = f"{t.lowest / 3.6e6:.2f}" if t.discharged else ""
        print(f"| {name} | {t.cost:,.0f} | {WEAR * t.discharged:,.0f} | "
              f"{t.cost + WEAR * t.discharged:,.0f} | {t.imported:,.0f} | {t.exported:,.0f} | "
              f"{t.curtailed:,.0f} | {t.discharged:,.0f} | {lowest} |")
    print()
    for note in notes:
        print(note)


def seconds(path: str):
    """The UTC time and the summed active power of each row of a PTProsumer file."""
    with gzip.open(path, "rt", newline="") as f:
        reader = csv.reader(f)
        head = next(reader)
        cols = [i for i, h in enumerate(head) if h.startswith("active_power_P")]
        for row in reader:
            if all(row[i] != "" for i in cols):
                yield row[0], sum(float(row[i]) for i in cols)


def within_report(net_path: str, pv_path: str) -> None:
    """How far one-second load and PV extremes lie beyond the extremes of the minute averages
    over each window, from one PTProsumer house: load is net load plus PV."""
    minutes: dict[str, list] = {}
    pv_rows = seconds(pv_path)
    pv = next(pv_rows, None)
    for stamp, net in seconds(net_path):
        while pv is not None and pv[0] < stamp:
            pv = next(pv_rows, None)
        if pv is None or pv[0] != stamp:
            continue
        load = net + pv[1]
        m = minutes.setdefault(stamp[:16], [0, 0.0, math.inf, -math.inf, 0.0, math.inf, -math.inf])
        m[0] += 1
        m[1] += load
        m[2] = min(m[2], load)
        m[3] = max(m[3], load)
        m[4] += pv[1]
        m[5] = min(m[5], pv[1])
        m[6] = max(m[6], pv[1])
    first = datetime.fromisoformat(min(minutes)).timestamp() // 60
    last = datetime.fromisoformat(max(minutes)).timestamp() // 60
    n = int(last - first) + 1
    rows: list = [None] * n
    for key, m in minutes.items():
        if m[0] >= 50:
            rows[int(datetime.fromisoformat(key).timestamp() // 60 - first)] = m
    print(f"{len(minutes):,} minutes with data, {sum(r is not None for r in rows):,} with at least "
          "50 seconds\n")
    print("| W (s) | Windows | Load above the minute maximum: p50, p90, p99, p99.9 (W) "
          "| Load below the minute minimum | PV above | PV below |")
    print("|---|---|---|---|---|---|")
    series = {"avg_load": [None if r is None else round(r[1] / r[0]) for r in rows],
              "min_load": [None if r is None else round(r[2]) for r in rows],
              "max_load": [None if r is None else round(r[3]) for r in rows],
              "avg_pv": [None if r is None else round(r[4] / r[0]) for r in rows],
              "min_pv": [None if r is None else round(r[5]) for r in rows],
              "max_pv": [None if r is None else round(r[6]) for r in rows]}
    for w in (1, 3, 5, 10, 15):
        ext = {k: sliding(v, w) for k, v in series.items()}
        gaps: dict[str, list[int]] = {"load_up": [], "load_down": [], "pv_up": [], "pv_down": []}
        for i in range(w - 1, n):
            if ext["avg_load"][0][i] is None:
                continue
            gaps["load_up"].append(ext["max_load"][1][i] - ext["avg_load"][1][i])
            gaps["load_down"].append(ext["avg_load"][0][i] - ext["min_load"][0][i])
            gaps["pv_up"].append(ext["max_pv"][1][i] - ext["avg_pv"][1][i])
            gaps["pv_down"].append(ext["avg_pv"][0][i] - ext["min_pv"][0][i])
        cells = [", ".join(f"{quantile(g, q):,}" for q in (Fraction(1, 2), Fraction(9, 10),
                                                         Fraction(99, 100), Fraction(999, 1000)))
                 for g in gaps.values()]
        print(f"| {60 * w} | {len(gaps['load_up']):,} | " + " | ".join(cells) + " |", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("check").add_argument("cases")
    c = commands.add_parser("prepare")
    c.add_argument("directory")
    c.add_argument("out")
    c = commands.add_parser("within")
    c.add_argument("net")
    c.add_argument("pv")
    for name in ("margins", "economics", "calibration"):
        c = commands.add_parser(name)
        c.add_argument("calibration")
        c.add_argument("evaluation", nargs="?" if name == "calibration" else None)
        c.add_argument("--window", type=int, action="append")
        c.add_argument("--open-caps", action="store_true")
    args = parser.parse_args()
    if args.command == "check":
        return check(args.cases)
    if args.command == "prepare":
        return prepare(args.directory, args.out)
    if args.command == "within":
        within_report(args.net, args.pv)
        return 0
    calibration = load_series(args.calibration)
    if args.command == "calibration":
        calibration_report(calibration, (args.window or [300])[0] // 60)
        return 0
    evaluation = load_series(args.evaluation)
    if args.command == "margins":
        margins_report(calibration, evaluation)
    else:
        economics_report(calibration, evaluation, args.window or [300], args.open_caps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
