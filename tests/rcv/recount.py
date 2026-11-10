# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Recounts Otis's Oakland CVRs under Alameda County's practice and compares every round with the report.

A ballot counts for its first ranked continuing candidate.  The count passes over skipped rankings,
the aggregate `Write-in` rankings, and rankings of eliminated candidates, and a ballot that reaches
an `overvote` ranking first is an overvote from then on.  A ballot without a candidate or overvote
mark is a blank.  Any other inactive ballot is exhausted.  Each round eliminates the candidate that
the report eliminates in that round, and the script checks that this candidate has the fewest votes
of the recount.  With `--suspend`, round 1 instead counts as suspended every ballot whose first
ranking is skipped or a write-in and that has a later candidate or overvote mark, as Alameda's 2022
configuration did; later rounds count those ballots normally.

For each contest of `manifest.json` with a CVR, or for the contests named on the command line, the
script prints one line per round that differs from the report and a summary line per contest.  The
summary also gives the charter's majority stop and first batch on the recount's tallies.  It exits
with status 1 if a file is missing or a recount names a candidate that the report lacks.
"""

import argparse
import csv
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import reports  # noqa: E402

PASS = {"skipped", "Write-in"}
FIELDS = ("blanks", "overvotes", "exhausted", "suspended")


def ballots(path):
    """Each ballot's rankings, as a tuple of strings, with its multiplicity."""
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.reader(f)
        header = next(reader)
        ranks = [i for i, h in enumerate(header) if h.startswith("rank")]
        return Counter(tuple(row[i] for i in ranks) for row in reader)


def interpret(ballot, continuing, passed=PASS):
    """The candidate the ballot counts for, or the reason it is inactive."""
    for mark in ballot:
        if mark in passed:
            continue
        if mark == "overvote":
            return "overvotes"
        if mark in continuing:
            return mark
    if all(mark in passed for mark in ballot):
        return "blanks"
    return "exhausted"


def suspended(ballot, passed=PASS):
    return ballot[0] in passed and any(mark not in passed for mark in ballot[1:])


def recount(cvr, report, suspend):
    """Rounds in the report's form, eliminating in each round the candidate the report eliminates."""
    named = {m for b in cvr for m in b} - PASS - {"overvote"}
    unknown = named - set(report["candidates"])
    if unknown:
        raise reports.ReportError(f"CVR names {sorted(unknown)}, absent from the report")
    continuing = list(report["candidates"])
    rounds = []
    for published in report["rounds"]:
        rnd = {"round": published["round"], "tallies": dict.fromkeys(report["candidates"], 0)}
        rnd.update(dict.fromkeys(FIELDS, 0))
        for ballot, n in cvr.items():
            if suspend and published["round"] == 1 and suspended(ballot):
                rnd["suspended"] += n
                continue
            where = interpret(ballot, continuing)
            if where in FIELDS:
                rnd[where] += n
            else:
                rnd["tallies"][where] += n
        rnd["eliminated"] = list(published["eliminated"])
        rnd["elected"] = list(published["elected"])
        least = min(rnd["tallies"][c] for c in continuing)
        rnd["not_lowest"] = [c for c in rnd["eliminated"] if rnd["tallies"][c] != least]
        rounds.append(rnd)
        continuing = [c for c in continuing if c not in published["eliminated"]]
    return {"candidates": report["candidates"], "rounds": rounds}


def differences(mine, published):
    out = []
    for c in published["tallies"]:
        if mine["tallies"][c] != published["tallies"][c]:
            out.append(f"{c} {mine['tallies'][c]} against {published['tallies'][c]}")
    for k in FIELDS:
        if mine[k] != published[k]:
            out.append(f"{k} {mine[k]} against {published[k]}")
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("keys", nargs="*", help="contest keys such as 248/Oakland/007-SchoolDirector_District_4")
    ap.add_argument("--data", default="tmp/rcv-data", help="data directory (default tmp/rcv-data)")
    ap.add_argument("--suspend", action="store_true", help="apply the 2022 first-round suspension")
    args = ap.parse_args()
    data = Path(args.data)
    manifest = json.loads((Path(__file__).resolve().parent / "manifest.json").read_text())
    contests = [c for c in manifest["contests"] if "cvr" in c and (not args.keys or c["key"] in args.keys)]
    failed = 0
    for contest in contests:
        try:
            report = reports.parse(data / contest["report"]["path"])
            cvr = ballots(data / contest["cvr"]["path"])
            mine = recount(cvr, report, args.suspend)
        except (OSError, reports.ReportError) as e:
            print(f"{contest['key']}: {e}", file=sys.stderr)
            failed += 1
            continue
        differing = 0
        for m, p in zip(mine["rounds"], report["rounds"]):
            diff = differences(m, p)
            if m["not_lowest"]:
                diff.append(f"the report eliminates {m['not_lowest']}, not lowest in the recount")
            if diff:
                differing += 1
                print(f"{contest['key']} round {m['round']}: " + "; ".join(diff))
        ch = reports.charter(mine)
        stop = ch["stop"]["report_round"] if "stop" in ch else ch.get("incomplete")
        print(f"{contest['key']}: {sum(cvr.values())} ballots, {len(report['rounds'])} rounds, "
              f"{differing} differ; charter stop {stop}, first batch {ch['first_batch_round']}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
