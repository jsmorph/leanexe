# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Recounts the Maine corpus's RCV contests under the Maine requirements and compares the rounds
with the Secretary of State's summary reports.

The script reads each contest's cast vote record spreadsheets from the data directory,
`tmp/rcv-maine-data` by default, with Python's zip and XML modules.  A ranking cell holding
`undervote`, or a missing cell, is an empty position, `overvote` is an overvote whose candidates the
records do not name, `Write-in` is a ranking of the aggregate write-in, an uncounted candidate, and
any other value, with surrounding spaces removed, must name a candidate of the report.

The count is the one of `Demos/Rcv/Maine/requirements.md`.  The examination of a ballot passes an
empty position unless the position begins a run of two or more empty positions followed by a marked
position, which ends it with the reason `exhausted`; it ends at an overvote with `overvote`, counts
the ballot at a position marking a continuing candidate, and passes a position marking any other
candidate.  A ballot whose examination passes its last position is `blank` when every position is
empty, `exhausted` when some position marks a counted candidate alone, and `uncounted` otherwise.
The initial test elects a candidate ranked first alone on more than half of the ballots.  Otherwise
each round eliminates the candidate with the fewest votes while three or more continue and names the
candidate with more votes when two remain.  Ties are decided by the report's candidate order, the
candidate latest in it eliminated, and none arises in the corpus.

For each contest the script prints each round's votes, inactive counts by reason, and elimination,
then the report's figures minus the recount's, where the report's single inactive category is
compared with the sum of the four reasons.  When a contest's figures differ, `--residual LABEL`
tests whether the differences can lie in the ballots of the file with that manifest label alone:
the report's figures minus the recount of the other files must, in every round, be nonnegative, sum
to that file's rows, and not decrease from round to round for each continuing candidate and for the
inactive ballots.  `--writein empty` passes a write-in ranking as an empty position instead, and
`--no-skip-rule` drops the rule of two empty positions, to show the effect of each reading.

The exit status is 0 when every contest compared without `--residual` equals its report, and 1
otherwise.
"""

import argparse
import collections
import json
import re
import sys
import zipfile
from pathlib import Path
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
RNS = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"

EMPTY = None
MULTI = "*"
WRITEIN = "Write-in"

# The summary reports' figures: candidates in the report's order, then for each round the votes of
# the candidates in that order (None once eliminated) and the report's inactive ballots.
REPORTS = {
    "2026-06-09/DEM-CG2": (
        ["Baldacci, Joseph M.", "Dunlap, Matthew G.", "Wood, Jordan", "Loud, Paige"],
        [([24966, 22933, 22712, 8194], 4675),
         ([25923, 25681, 25377, None], 6499),
         ([32555, 35924, None, None], 15001)],
        "Dunlap, Matthew G."),
    "2026-06-09/DEM-GOV": (
        ["Shah, Nirav D.", "Pingree, Hannah M.", "Jackson, Troy Dale", "Bellows, Shenna", "King, Angus, III"],
        [([58606, 50552, 45959, 44770, 17860], 4658),
         ([62860, 55360, 47597, 47049, None], 9539),
         ([72681, 75671, 60010, None, None], 14043),
         ([86950, 111750, None, None, None], 23705)],
        "Pingree, Hannah M."),
    "2026-06-09/REP-GOV": (
        ["Charles, Robert B.", "Midgley, Benjamin T.", "Bush, Jonathan J.", "Mason, Garrett Paul",
         "McCarthy, Owen Z.", "Jones, David J.", "Wessels, Robert J.", "Libby, James D."],
        [([49129, 25880, 25449, 14820, 5033, 3740, 3525, 1831], 8574),
         ([49294, 25967, 25703, 15005, 5258, 3874, 3637, None], 9243),
         ([49780, 26550, 26092, 15342, 5528, 4048, None, None], 10641),
         ([50342, 27243, 26744, 15761, 5769, None, None, None], 12122),
         ([50916, 28536, 27768, 16438, None, None, None, None], 14323),
         ([53246, 31553, 31104, None, None, None, None, None], 22078),
         ([59873, 39499, None, None, None, None, None, None], 38609)],
        "Charles, Robert B."),
    "2026-06-09/REP-SS4": (
        ["Perkins, Chad Richard", "Guerin, Joseph P.", "Wood, Zachary Anders", "Pierce, Gregory"],
        [([2831, 1889, 924, 229], 526),
         ([2865, 1947, 945, None], 642),
         ([3014, 2098, None, None], 1287)],
        "Perkins, Chad Richard"),
    "2026-06-09/REP-SR58": (
        ["Bridges, Dexter E., Jr.", "Bessey, Lawrence E.", "Harris, Jeffrey S."],
        [([462, 459, 312], 174),
         ([540, 488, None], 379)],
        "Bridges, Dexter E., Jr."),
    "2024-11-05/CG2": (
        ["Golden, Jared Forrest", "Theriault, Austin"],
        [([197151, 194445], 11340)],
        "Golden, Jared Forrest"),
}


def column(ref):
    n = 0
    for ch in re.match(r"[A-Z]+", ref).group(0):
        n = n * 26 + ord(ch) - 64
    return n - 1


def sheets(path):
    """The rows of each worksheet of an xlsx file, as lists of strings."""
    with zipfile.ZipFile(path) as z:
        try:
            ss = [''.join(t.text or '' for t in si.iter(NS + 't'))
                  for si in ET.fromstring(z.read("xl/sharedStrings.xml")).iter(NS + "si")]
        except KeyError:
            ss = []
        rels = {r.get("Id"): r.get("Target") for r in ET.fromstring(z.read("xl/_rels/workbook.xml.rels"))}
        for sheet in ET.fromstring(z.read("xl/workbook.xml")).iter(NS + "sheet"):
            target = rels[sheet.get(RNS + "id")].lstrip("/")
            if not target.startswith("xl/"):
                target = "xl/" + target
            rows = []
            for row in ET.fromstring(z.read(target)).iter(NS + "row"):
                cells = {}
                for c in row.iter(NS + "c"):
                    v = c.find(NS + "v")
                    if c.get("t") == "s":
                        val = ss[int(v.text)] if v is not None else ""
                    elif c.get("t") == "inlineStr":
                        val = ''.join(t.text or '' for t in c.iter(NS + "t"))
                    else:
                        val = v.text if v is not None and v.text is not None else ""
                    cells[column(c.get("r"))] = val
                if cells:
                    rows.append([cells.get(i, "") for i in range(max(cells) + 1)])
            yield rows


def load(data, contest, names, writein):
    """The ballots of a contest, each a tuple of positions, with the manifest label of its file."""
    ballots = []
    repeats = []
    for f in contest["cvr"]:
        seen = set()
        for rows in sheets(data / f["path"]):
            header = rows[0]
            ranks = [i for i, h in enumerate(header) if "Choice" in h]
            for r in rows[1:]:
                ident = r[0][:-2] if r[0].endswith(".0") else r[0]
                if ident in seen:
                    repeats.append(f"{f['label']}:{ident}")
                seen.add(ident)
                ps = []
                for i in ranks:
                    v = r[i].strip() if i < len(r) else ""
                    if v in ("", "undervote"):
                        ps.append(EMPTY)
                    elif v == "overvote":
                        ps.append(MULTI)
                    elif v == WRITEIN:
                        ps.append(EMPTY if writein == "empty" else WRITEIN)
                    elif v in names:
                        ps.append(v)
                    else:
                        sys.exit(f"{f['path']}: Cast Vote Record {ident}: unknown ranking {v!r}")
                ballots.append((f["label"], tuple(ps)))
    return ballots, repeats


def interpret(C, counted, ps, skip_rule=True):
    n = len(ps)
    for i, p in enumerate(ps):
        if p is EMPTY:
            if skip_rule and i + 1 < n and ps[i + 1] is EMPTY and any(q is not EMPTY for q in ps[i + 2:]):
                return ("inactive", "exhausted")
            continue
        if p == MULTI:
            return ("inactive", "overvote")
        if p in C:
            return ("counts", p)
    if all(p is EMPTY for p in ps):
        return ("inactive", "blank")
    if any(p in counted for p in ps):
        return ("inactive", "exhausted")
    return ("inactive", "uncounted")


def tally(C, counted, ballots, skip_rule):
    votes = {c: 0 for c in C}
    inactive = collections.Counter()
    for ps, m in ballots.items():
        kind, x = interpret(set(C), counted, ps, skip_rule)
        if kind == "counts":
            votes[x] += m
        else:
            inactive[x] += m
    return votes, inactive


def count(names, ballots, skip_rule):
    """The initial test's first rankings, its winner or None, and the rounds of the count."""
    counted = set(names)
    groups = collections.Counter(ps for _, ps in ballots)
    first = {c: sum(m for ps, m in groups.items() if ps and ps[0] == c) for c in names}
    N = len(ballots)
    initial = next((c for c in names if 2 * first[c] > N), None)
    rounds = []
    if initial is not None:
        return first, initial, rounds, initial
    C = list(names)
    while True:
        votes, inactive = tally(C, counted, groups, skip_rule)
        rd = {"votes": votes, "inactive": inactive, "elim": None}
        rounds.append(rd)
        if len(C) <= 2:
            if len(C) == 2 and votes[C[0]] == votes[C[1]]:
                loser = max(C, key=names.index)
                rd["elim"] = ("order", loser)
                C = [c for c in C if c != loser]
                continue
            return first, None, rounds, (max(C, key=lambda c: votes[c]) if C else None)
        fewest = min(votes.values())
        Z = [c for c in C if votes[c] == fewest]
        loser = max(Z, key=names.index)
        rd["elim"] = ("lowest" if len(Z) == 1 else "order", loser)
        C = [c for c in C if c != loser]


def report_differences(names, rounds, official):
    diffs = []
    for r, ((votes, inactive), rd) in enumerate(zip(official, rounds), 1):
        for c, v in zip(names, votes):
            mine = rd["votes"].get(c)
            if v != mine:
                diffs.append((r, c, v, mine))
        mine_inactive = sum(rd["inactive"].values())
        if inactive != mine_inactive:
            diffs.append((r, "inactive", inactive, mine_inactive))
    if len(official) != len(rounds):
        diffs.append(("rounds", "", len(official), len(rounds)))
    return diffs


def residual(names, ballots, official, label, skip_rule):
    rest = collections.Counter(ps for lab, ps in ballots if lab != label)
    rows = sum(1 for lab, _ in ballots if lab == label)
    implied = []
    for votes, inactive in official:
        C = [c for c, v in zip(names, votes) if v is not None]
        mine_votes, mine_inactive = tally(C, set(names), rest, skip_rule)
        implied.append([(v - mine_votes[c]) if v is not None else None for c, v in zip(names, votes)]
                       + [inactive - sum(mine_inactive.values())])
    nonneg = all(x is None or x >= 0 for row in implied for x in row)
    sums = all(sum(x for x in row if x is not None) == rows for row in implied)
    grows = all(b is None or a <= b for r0, r1 in zip(implied, implied[1:]) for a, b in zip(r0, r1)
                if a is not None)
    return rows, implied, nonneg and sums and grows


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("keys", nargs="*", help="manifest keys of the contests (default: every contest with CVRs)")
    ap.add_argument("--data", default="tmp/rcv-maine-data", help="data directory (default tmp/rcv-maine-data)")
    ap.add_argument("--residual", metavar="LABEL", help="test whether the differences lie in one file")
    ap.add_argument("--writein", choices=["ranking", "empty"], default="ranking")
    ap.add_argument("--no-skip-rule", action="store_true")
    args = ap.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    data = Path(args.data)
    status = 0
    for contest in manifest["contests"]:
        key = contest["key"]
        if "cvr" not in contest or (args.keys and key not in args.keys):
            continue
        names, official, winner = REPORTS[key]
        ballots, repeats = load(data, contest, set(names), args.writein)
        skip_rule = not args.no_skip_rule
        first, initial, rounds, named = count(names, ballots, skip_rule)
        print(f"{key}: {len(ballots)} ballots" + (f", Cast Vote Record numbers repeated within a file: "
                                                  f"{' '.join(repeats)}" if repeats else ""))
        print("  first " + ", ".join(f"{c} {first[c]}" for c in names)
              + (f"; initial test elects {initial}" if initial else "; initial test elects no one"))
        for r, rd in enumerate(rounds, 1):
            votes = ", ".join(f"{c} {rd['votes'][c]}" for c in names if c in rd["votes"])
            inactive = ", ".join(f"{k} {rd['inactive'][k]}" for k in ("blank", "uncounted", "overvote", "exhausted"))
            elim = f"; eliminate {rd['elim'][0]} {rd['elim'][1]}" if rd["elim"] else ""
            print(f"  round {r}: {votes}; inactive {inactive}{elim}")
        print(f"  winner {named}")
        diffs = report_differences(names, rounds, official)
        if named != winner:
            diffs.append(("winner", "", winner, named))
        if not diffs:
            print("  equals the report in every round")
        else:
            print(f"  {len(diffs)} figures differ from the report (report, recount):")
            for d in diffs:
                print(f"    round {d[0]} {d[1]}: {d[2]}, {d[3]}")
            if args.residual:
                rows, implied, ok = residual(names, ballots, official, args.residual, skip_rule)
                print(f"  the report minus the recount of the other files, for {args.residual} ({rows} rows):")
                for row in implied:
                    print("    " + " ".join("-" if x is None else str(x) for x in row))
                print(f"  {'consistent' if ok else 'not consistent'} with ballots of {args.residual} alone")
            else:
                status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
