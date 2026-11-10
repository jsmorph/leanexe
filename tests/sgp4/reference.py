# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compares Demos.Sgp4.sgp4 in native Lean with the reference states of Vallado, Crawford,
Hujsak, and Kelso (AIAA 2006-6753).  `near-earth.tle` holds the near-Earth element sets of their
verification file, each followed on its second line by the start, the end, and the step of its
times in minutes, and `near-earth.out` holds the states that their code printed: the time, the
position in km, and the velocity in km/s.  For each printed state, the program's status must be 0
or 6, its position must lie within POSITION km of the reference, and its velocity within VELOCITY
km/s.  For each later time of an element set, which the reference code did not print, the status
must not be 0.  The check prints the largest differences.
Usage: uv run tests/sgp4/reference.py EXECUTABLE"""
import pathlib
import struct
import subprocess
import sys

POSITION = 1e-8
VELOCITY = 1e-9


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
    for line1, line2 in zip(lines[0::2], lines[1::2]):
        start, stop, step = (float(x) for x in line2[69:].split())
        sets[str(int(line2[2:7]))] = (elements(line1, line2), start, stop, step)
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
    run = subprocess.run(
        [sys.argv[1], "--states"], input=text, capture_output=True, text=True, check=True
    )
    results = run.stdout.splitlines()
    if len(results) != len(queries):
        print(f"expected {len(queries)} states, read {len(results)}")
        return 1
    failures = 0
    worst_r = worst_v = 0.0
    for (name, t, expected), result in zip(queries, results):
        words = result.split()
        status = int(words[0])
        state = [double(w) for w in words[1:]]
        if expected is None:
            if status == 0:
                failures += 1
                print(f"fail {name} t={t}: status 0 after the reference code stopped")
            continue
        dr = max(abs(a - b) for a, b in zip(state[:3], expected[:3]))
        dv = max(abs(a - b) for a, b in zip(state[3:], expected[3:]))
        worst_r = max(worst_r, dr)
        worst_v = max(worst_v, dv)
        if status not in (0, 6) or not dr <= POSITION or not dv <= VELOCITY:
            failures += 1
            print(f"fail {name} t={t}: status {status}, position {dr:.3e}, velocity {dv:.3e}")
    print(f"states {len(queries)}, largest position difference {worst_r:.3e} km, "
          f"largest velocity difference {worst_v:.3e} km/s")
    print(f"{failures} failures")
    return 1 if failures else 0


sys.exit(main())
