# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Counts the 2022 OUSD District 4 contest from Otis's CVR three ways and compares each with the county's figures.

The first count follows `recount.py`'s rules and eliminates the candidate with the fewest votes in
each round until two remain; every round must equal the corrected report that Alameda County
re-ran on 2023-03-10.  The second count adds the first-round suspension of Alameda's 2022
configuration; its rounds must equal Table A of slide 6 of the Registrar's presentation, the count
the county certified first, and the suspended ballots must count as slide 5 shows under the correct
configuration.  The third count makes the aggregate write-in a candidate and prints its first round,
which differs from the report.  The script exits with status 1 if the first or second comparison
fails.
"""

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import recount  # noqa: E402
import reports  # noqa: E402

KEY = "248/Oakland/007-SchoolDirector_District_4"
H, M, R = "MIKE HUTCHINSON", "PECOLIA MANIGO", "NICK RESNICK"

# Table A of slide 6, "Table A shows the certified results using the incorrect RCV configuration."
CERTIFIED = [
    {"tallies": {H: 8112, M: 8153, R: 9954}, "suspended": 235},
    {"tallies": {M: 11753, R: 12352}},
]
# Slide 5, "each candidate's votes within the 235 suspended ballots".
SUSPENDED = {H: 115, M: 37, R: 61, "overvotes": 22}


def count(cvr, candidates, suspend=False, passed=recount.PASS):
    """Rounds of single elimination until two candidates remain."""
    continuing = list(candidates)
    rounds = []
    while True:
        rnd = {"tallies": dict.fromkeys(continuing, 0), **dict.fromkeys(recount.FIELDS, 0)}
        for ballot, n in cvr.items():
            if suspend and not rounds and recount.suspended(ballot, passed):
                rnd["suspended"] += n
                continue
            where = recount.interpret(ballot, continuing, passed)
            if where in recount.FIELDS:
                rnd[where] += n
            else:
                rnd["tallies"][where] += n
        rounds.append(rnd)
        if len(continuing) <= 2:
            return rounds
        least = min(rnd["tallies"].values())
        lowest = [c for c in continuing if rnd["tallies"][c] == least]
        if len(lowest) > 1:
            raise SystemExit(f"tie for last place among {lowest}")
        continuing.remove(lowest[0])


def compare(name, mine, theirs, fields):
    """Prints each round's comparison and returns the number of rounds that differ."""
    bad = 0
    if len(mine) != len(theirs):
        print(f"{name}: {len(mine)} rounds against {len(theirs)}")
        bad += 1
    for i, (a, b) in enumerate(zip(mine, theirs), start=1):
        names = list(dict.fromkeys([*b["tallies"], *a["tallies"]]))
        diff = [f"{c} {a['tallies'].get(c, 0)} against {b['tallies'].get(c, 0)}" for c in names
                if a["tallies"].get(c, 0) != b["tallies"].get(c, 0)]
        diff += [f"{k} {a[k]} against {b[k]}" for k in fields if k in b and a[k] != b[k]]
        shown = ", ".join(f"{c.split()[-1].title()} {v:,}" for c, v in a["tallies"].items())
        extra = ", ".join(f"{k} {a[k]:,}" for k in fields if a[k])
        print(f"{name} round {i}: {shown}; {extra}: " + ("agrees" if not diff else "differs: " + "; ".join(diff)))
        bad += bool(diff)
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data", default="tmp/rcv-data", help="data directory (default tmp/rcv-data)")
    args = ap.parse_args()
    data = Path(args.data)
    manifest = json.loads((Path(__file__).resolve().parent / "manifest.json").read_text())
    contest = next(c for c in manifest["contests"] if c["key"] == KEY)
    report = reports.parse(data / contest["report"]["path"])
    cvr = recount.ballots(data / contest["cvr"]["path"])
    candidates = report["candidates"]
    print(f"{KEY}: {sum(cvr.values()):,} ballots in the CVR, report timestamp {report['timestamp']}, "
          f"useFirstRoundSuspension {report['settings']['useFirstRoundSuspension']}")

    bad = compare("corrected", count(cvr, candidates), report["rounds"], recount.FIELDS)

    misconfigured = count(cvr, candidates, suspend=True)
    bad += compare("suspension", misconfigured, CERTIFIED, recount.FIELDS)
    moved = Counter()
    for ballot, n in cvr.items():
        if recount.suspended(ballot):
            moved[recount.interpret(ballot, candidates)] += n
    line = ", ".join(f"{k} {moved[k]}" for k in SUSPENDED)
    agree = all(moved[k] == v for k, v in SUSPENDED.items()) and sum(moved.values()) == sum(SUSPENDED.values())
    print(f"suspended ballots under the correct configuration: {line}: " + ("agrees" if agree else "differs"))
    bad += not agree

    write_in = count(cvr, candidates + ["Write-in"], passed={"skipped"})[0]
    shown = ", ".join(f"{c} {v:,}" for c, v in write_in["tallies"].items())
    print(f"write-in as a candidate, round 1: {shown}")

    print("District 4 checks " + ("pass" if not bad else f"fail in {bad} comparisons"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
