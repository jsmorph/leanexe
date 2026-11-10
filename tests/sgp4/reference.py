# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compares the SGP4 programs in native Lean with the reference states of Vallado, Crawford,
Hujsak, and Kelso (AIAA 2006-6753).  `near-earth.tle` holds the near-Earth element sets of their
verification file, each followed on its second line by the start, the end, and the step of its
times in minutes, and `near-earth.out` holds the states that their code printed: the time, the
position in km, and the velocity in km/s.

For each printed state, the status of Demos.Sgp4.sgp4 must be 0 or 6, its position must lie
within POSITION km of the reference, and its velocity within VELOCITY km/s.  The status of
Demos.Sgp4.sgp4BoxAround must be the same, and each coordinate of the reference and of
Demos.Sgp4.sgp4 must lie within BOX_POSITION km or BOX_VELOCITY km/s of its interval.  The
intervals contain the model's values with the exact root of Kepler's equation, and the reference
code and Demos.Sgp4.sgp4 stop their iteration at a correction below 1e-12, so their values may
lie outside an interval by that correction times the semimajor axis.  For each later time of an
element set, for which the verification file holds no state, neither status may be 0.

Demos.Sgp4.Tle.propagate reads the two lines of each element set.  Its status must equal that of
Demos.Sgp4.sgp4BoxAround at every time, and each reference coordinate must lie within the same
distances of its interval.  It must return status 9 for an element set with one digit changed,
which breaks the checksum, and the status of the unchanged lines for an element set whose catalog
fields begin with a letter, the Alpha-5 form.  The check prints the largest differences and the
largest widths of the intervals.
Usage: uv run tests/sgp4/reference.py STATES_EXECUTABLE BOXES_EXECUTABLE"""
import pathlib
import struct
import subprocess
import sys

POSITION = 1e-8
VELOCITY = 1e-9
BOX_POSITION = 2e-8
BOX_VELOCITY = 1e-9


def bits(x: float) -> str:
    return str(struct.unpack("<Q", struct.pack("<d", x))[0])


def double(word: str) -> float:
    return struct.unpack("<d", struct.pack("<Q", int(word)))[0]


def elements(line1: str, line2: str) -> list[float]:
    bstar = float(line1[53] + "." + line1[54:59]) * 10.0 ** int(line1[59:61])
    return [
        float(line2[52:63]),
        float("0." + line2[26:33].replace(" ", "0")),
        float(line2[8:16]),
        float(line2[17:25]),
        float(line2[34:42]),
        float(line2[43:51]),
        bstar,
    ]


def main() -> int:
    here = pathlib.Path(__file__).parent
    lines = (here / "near-earth.tle").read_text().splitlines()
    sets = {}
    texts = {}
    for line1, line2 in zip(lines[0::2], lines[1::2]):
        start, stop, step = (float(x) for x in line2[69:].split())
        sets[str(int(line2[2:7]))] = (elements(line1, line2), start, stop, step)
        texts[str(int(line2[2:7]))] = (line1[:69], line2[:69])
    queries = []
    name = None
    last = {}
    for line in (here / "near-earth.out").read_text().splitlines():
        fields = line.split()
        if fields[1] == "xx":
            name = fields[0]
            continue
        values = [float(x) for x in fields]
        queries.append((name, values[0], values[1:]))
        last[name] = values[0]
    for name, (_, start, stop, step) in sets.items():
        t = last[name] + step
        while t <= stop + 1e-9:
            queries.append((name, t, None))
            t += step
    text = "".join(
        " ".join(bits(x) for x in sets[name][0] + [t]) + "\n" for name, t, _ in queries
    )
    def call(executable: str, mode: str) -> list[str]:
        run = subprocess.run(
            [executable, mode], input=text, capture_output=True, text=True, check=True
        )
        lines = run.stdout.splitlines()
        if len(lines) != len(queries):
            raise SystemExit(f"{mode}: expected {len(queries)} lines, read {len(lines)}")
        return lines

    def read_lines(pairs: list[tuple[str, str, float]]) -> list[list[str]]:
        text = "".join(f"{a}\n{b}\n{bits(t)}\n" for a, b, t in pairs)
        run = subprocess.run(
            [sys.argv[2], "--lines"], input=text, capture_output=True, text=True, check=True
        )
        return [line.split() for line in run.stdout.splitlines()]

    states = call(sys.argv[1], "--states")
    boxes = call(sys.argv[2], "--boxes")
    from_lines = read_lines([(*texts[name], t) for name, t, _ in queries])
    failures = 0
    worst_r = worst_v = 0.0
    width_r = width_v = 0.0
    outside_r = outside_v = 0.0
    away_r = away_v = 0.0
    for (name, t, expected), state_line, box_line in zip(queries, states, boxes):
        words = state_line.split()
        status = int(words[0])
        state = [double(w) for w in words[1:]]
        words = box_line.split()
        box_status = int(words[0])
        accepted = [int(words[1 + 3 * i]) == 0 for i in range(6)]
        lows = [double(words[2 + 3 * i]) for i in range(6)]
        highs = [double(words[3 + 3 * i]) for i in range(6)]
        if expected is None:
            if status == 0 or box_status == 0:
                failures += 1
                print(f"fail {name} t={t}: statuses {status} and {box_status} "
                      "at a time without a reference state")
            continue
        dr = max(abs(a - b) for a, b in zip(state[:3], expected[:3]))
        dv = max(abs(a - b) for a, b in zip(state[3:], expected[3:]))
        worst_r = max(worst_r, dr)
        worst_v = max(worst_v, dv)
        if status not in (0, 6) or not dr <= POSITION or not dv <= VELOCITY:
            failures += 1
            print(f"fail {name} t={t}: status {status}, position {dr:.3e}, velocity {dv:.3e}")
        if box_status != status or not all(accepted):
            failures += 1
            print(f"fail {name} t={t}: box status {box_status}, program status {status}")
            continue
        for i in range(6):
            tolerance = BOX_POSITION if i < 3 else BOX_VELOCITY
            width = highs[i] - lows[i]
            gap = max(lows[i] - expected[i], expected[i] - highs[i], 0.0)
            away = max(lows[i] - state[i], state[i] - highs[i], 0.0)
            if i < 3:
                width_r = max(width_r, width)
                outside_r = max(outside_r, gap)
                away_r = max(away_r, away)
            else:
                width_v = max(width_v, width)
                outside_v = max(outside_v, gap)
                away_v = max(away_v, away)
            if not gap <= tolerance or not away <= tolerance:
                failures += 1
                print(f"fail {name} t={t} coordinate {i}: reference {gap:.3e} outside, "
                      f"program {away:.3e} outside, width {width:.3e}")
    line_width = 0.0
    for (name, t, expected), box_line, words in zip(queries, boxes, from_lines):
        if int(words[0]) != int(box_line.split()[0]):
            failures += 1
            print(f"fail {name} t={t}: status {words[0]} from the lines, "
                  f"{box_line.split()[0]} from the values")
            continue
        if expected is None:
            continue
        for i in range(6):
            low = double(words[2 + 3 * i])
            high = double(words[3 + 3 * i])
            tolerance = BOX_POSITION if i < 3 else BOX_VELOCITY
            gap = max(low - expected[i], expected[i] - high, 0.0)
            if i < 3:
                line_width = max(line_width, high - low)
            if int(words[1 + 3 * i]) != 0 or not gap <= tolerance:
                failures += 1
                print(f"fail {name} t={t} coordinate {i} from the lines: {gap:.3e} outside")

    def checksum(line: str) -> str:
        total = sum(int(c) if c.isdigit() else (1 if c == "-" else 0) for c in line[:68])
        return line[:68] + str(total % 10)

    name, t, _ = queries[0]
    line1, line2 = texts[name]
    def change(line: str, column: int) -> str:
        digit = "1" if line[column] != "1" else "2"
        return line[:column] + digit + line[column + 1:]

    changed = read_lines([
        (line1, change(line2, 30), t),
        (change(line1, 56), line2, t),
        (line1, line2[:68], t),
        (checksum(line1[:2] + "A" + line1[3:]), checksum(line2[:2] + "A" + line2[3:]), t),
        (checksum(line1[:2] + "A" + line1[3:]), line2, t),
    ])
    expected_statuses = [9, 9, 9, int(from_lines[0][0]), 9]
    for words, wanted in zip(changed, expected_statuses):
        if int(words[0]) != wanted:
            failures += 1
            print(f"fail changed lines: status {words[0]}, expected {wanted}")
    print(f"states {len(queries)}")
    print(f"program: largest position difference {worst_r:.3e} km, "
          f"largest velocity difference {worst_v:.3e} km/s")
    print(f"intervals: largest width {width_r:.3e} km and {width_v:.3e} km/s")
    print(f"largest distance of a reference value from its interval {outside_r:.3e} km "
          f"and {outside_v:.3e} km/s")
    print(f"largest distance of a program value from its interval {away_r:.3e} km "
          f"and {away_v:.3e} km/s")
    print(f"intervals from the lines: largest width {line_width:.3e} km")
    print(f"{failures} failures")
    return 1 if failures else 0


sys.exit(main())
