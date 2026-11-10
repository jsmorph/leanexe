# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Converts the Maine corpus's contests and checks the converter and the reference's Maine mode
against the Secretary of State's summary reports.

For each contest of `tests/rcv/maine/manifest.json` with cast vote record spreadsheets, the script
converts the spreadsheets with `convert.py`, with `--practice` for the 2024 contest, writes the
canonical file under OUT with the reference's Maine report, contest words, and Maine result words,
and runs these checks:

  round trip KEY   the reference reads the file back to the spreadsheets' identifiers and rankings,
                   read again with `recount.py`'s spreadsheet reader, and its writer reproduces the
                   file
  initial KEY      the initial test elects no one, as the report's rounds require
  rounds KEY       the reference's rounds against the summary report's figures, as
                   `Demos/Rcv/Maine/review.md` records them: every figure equal for State Senate
                   District 4, House District 58, and the 2024 contest, and for the other three every
                   elimination and the winner equal and each figure within 4, 17, or 21 votes
  residual KEY     for those three, the report's figures minus the reference's count of every
                   spreadsheet but the third manual-entry one, with the report's continuing sets,
                   are nonnegative, sum to that spreadsheet's rows, and do not decrease from round to
                   round for a continuing candidate or for the inactive ballots
  District 58      the report of House District 58 after its header lines equals the requirements'
                   block

Each planted error is a copy of `convert.py` with one change, and each must fail the round trip of
every contest.  The script prints one line per contest and per planted error and exits with status 1
if a check fails or a planted error passes a round trip.  The summary reports' figures are those that
`recount.py` transcribes.

  check.py [--data DIR] [--out DIR]
"""

import argparse
import collections
import json
import re
import sys
import types
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import convert  # noqa: E402
import recount  # noqa: E402
import reference  # noqa: E402

REQUIREMENTS = HERE.parent.parent.parent / "Demos" / "Rcv" / "Maine" / "requirements.md"
PRACTICE = {"2024-11-05/CG2"}
TOLERANCE = {"2026-06-09/REP-GOV": 4, "2026-06-09/DEM-GOV": 17, "2026-06-09/DEM-CG2": 21}
RESIDUAL = "manual-3"

PLANTED = [
    ("an overvote written as an empty field", 'return b"*"', 'return b""'),
    ("the candidates' indices reversed",
     "index = {name: i for i, name in enumerate(names, 1)}",
     "index = {name: n + 1 - i for i, name in enumerate(names, 1)}"),
    ("the first ranking column dropped",
     'columns = [i for i in sorted(header) if "Choice" in header[i]]',
     'columns = [i for i in sorted(header) if "Choice" in header[i]][1:]'),
]


def requirement_block(prefix):
    blocks = re.findall(r"^```\n(.*?)^```$", REQUIREMENTS.read_text(), re.S | re.M)
    found = [b for b in blocks if b.startswith(prefix)]
    if len(found) != 1:
        raise SystemExit(f"check.py: {len(found)} blocks of the requirements start with {prefix!r}")
    return found[0].encode()


def spreadsheet_ballots(entry, data):
    """Each ballot of a contest's spreadsheets as (identifier, rankings), read with `recount.py`'s
    reader: a ranking is None for `undervote` or a missing cell, `*` for `overvote`, and otherwise
    the cell with its surrounding spaces removed."""
    ballots = []
    for f in entry["cvr"]:
        for rows in recount.sheets(data / f["path"]):
            ranks = [i for i, h in enumerate(rows[0]) if "Choice" in h]
            for r in rows[1:]:
                number = r[0][:-2] if r[0].endswith(".0") else r[0]
                marks = []
                for i in ranks:
                    v = r[i].strip(" ") if i < len(r) else ""
                    marks.append(None if v in ("", "undervote") else "*" if v == "overvote" else v)
                ballots.append((f"{f['label']}:{number}", tuple(marks)))
    return ballots


def round_trip(data, sheet_ballots, names):
    contest = reference.read(data)
    if isinstance(contest, reference.Malformed):
        return [f"the file fails at line {contest.line} with the role {contest.role}"]
    problems = []
    index = {name.decode(): i for i, (_, name) in enumerate(contest.candidates, 1)}
    if [name.decode() for _, name in contest.candidates[:len(names)]] != names:
        problems.append("the listed candidates differ from the report's")
    if len(contest.ballots) != len(sheet_ballots):
        problems.append(f"{len(contest.ballots)} ballots against {len(sheet_ballots)} rows")
    for (ident, words), (want_ident, marks) in zip(contest.ballots, sheet_ballots):
        want = tuple(0 if m is None else reference.UNNAMED if m == "*" else
                     1 << (index[m] - 1) if m in index else None for m in marks)
        if ident != want_ident.encode() or words != want:
            problems.append(f"the ballot {want_ident} reads back as {ident} {words}")
            break
    if reference.write(contest) != data:
        problems.append("the reference's writer does not reproduce the file")
    return problems


def compare_rounds(key, contest, rounds, winner):
    """The differences of the reference's rounds from the summary report beyond the tolerance."""
    names, official, official_winner = recount.REPORTS[key]
    index = {name: i for i, name in enumerate(names, 1)}
    tolerance = TOLERANCE.get(key, 0)
    problems = []
    if len(rounds) != len(official):
        problems.append(f"{len(rounds)} rounds against the report's {len(official)}")
    largest = 0
    for r, (rnd, (votes, inactive)) in enumerate(zip(rounds, official), 1):
        continuing = {index[name] for name, v in zip(names, votes) if v is not None}
        if set(rnd.votes) != continuing:
            problems.append(f"round {r}: continuing set {sorted(rnd.votes)} against {sorted(continuing)}")
            continue
        for name, v in zip(names, votes):
            if v is not None:
                largest = max(largest, abs(rnd.votes[index[name]] - v))
        largest = max(largest, abs(sum(rnd.inactive.values()) - inactive))
        if r < len(official):
            gone = continuing - {index[name] for name, v in zip(names, official[r][0]) if v is not None}
            if rnd.eliminated != sorted(gone):
                problems.append(f"round {r}: eliminates {rnd.eliminated} against {sorted(gone)}")
    if winner != index[official_winner]:
        problems.append(f"winner {winner} against {index[official_winner]}")
    if largest > tolerance:
        problems.append(f"a figure differs by {largest} votes, more than {tolerance}")
    return problems, largest


def residual(key, contest):
    """Whether the report's figures minus the count of every spreadsheet but the third manual-entry
    one can be that spreadsheet's ballots."""
    names, official, _ = recount.REPORTS[key]
    index = {name: i for i, name in enumerate(names, 1)}
    counted, _, _ = reference.setup(contest)
    prefix = f"{RESIDUAL}:".encode()
    rest = collections.Counter(words for ident, words in contest.ballots if not ident.startswith(prefix))
    rows = sum(1 for ident, _ in contest.ballots if ident.startswith(prefix))
    implied = []
    for r, (votes, inactive) in enumerate(official, 1):
        continuing = {index[name] for name, v in zip(names, votes) if v is not None}
        rnd = reference.tally(rest, counted, continuing, r, maine=True)
        implied.append([None if v is None else v - rnd.votes[index[name]] for name, v in zip(names, votes)]
                       + [inactive - sum(rnd.inactive.values())])
    nonnegative = all(x is None or x >= 0 for row in implied for x in row)
    sums = all(sum(x for x in row if x is not None) == rows for row in implied)
    grows = all(b is None or a <= b for r0, r1 in zip(implied, implied[1:]) for a, b in zip(r0, r1)
                if a is not None)
    problems = [] if nonnegative and sums and grows else [f"not consistent with the {rows} rows of {RESIDUAL}"]
    return problems, rows


def planted(old, new):
    path = HERE / "convert.py"
    source = path.read_text()
    if source.count(old) != 1:
        raise SystemExit(f"check.py: the planted change's text occurs {source.count(old)} times: {old!r}")
    module = types.ModuleType("planted_convert")
    module.__file__ = str(path)
    exec(compile(source.replace(old, new), str(path), "exec"), module.__dict__)
    return module


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data", default="tmp/rcv-maine-data", help="data directory (default tmp/rcv-maine-data)")
    ap.add_argument("--out", help="output directory (default DATA/canonical)")
    args = ap.parse_args()
    data = Path(args.data)
    out = Path(args.out) if args.out else data / "canonical"
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((HERE / "manifest.json").read_text())
    district58 = requirement_block("first 1 461\n")
    failed = 0
    corpus = []
    for entry in manifest["contests"]:
        if "cvr" not in entry:
            continue
        key = entry["key"]
        names = recount.REPORTS[key][0]
        try:
            text = convert.convert(manifest, key, data, practice=key in PRACTICE)
        except convert.Refused as e:
            print(f"convert {key}: {e}", file=sys.stderr)
            return 1
        sheet_ballots = spreadsheet_ballots(entry, data)
        corpus.append((entry, sheet_ballots))
        checks = {"round trip": round_trip(text, sheet_ballots, names)}
        contest = reference.read(text)
        first, rounds, winner = reference.maine_count(contest)
        largest_first = max(first.values())
        checks["initial"] = ([] if 2 * largest_first <= len(contest.ballots) else
                             ["the initial test elects a candidate"])
        checks["rounds"], largest = compare_rounds(key, contest, rounds, winner)
        note = f"each figure within {largest} votes of the report" if largest else "every figure equal"
        if key in TOLERANCE:
            checks["residual"], rows = residual(key, contest)
            note += f", differences consistent with the {rows} rows of {RESIDUAL}"
        report = reference.report(text, "maine")
        if key == "2026-06-09/REP-SR58":
            body = b"".join(line + b"\n" for line in report.split(b"\n")[7 + len(contest.candidates):-1])
            checks["District 58"] = [] if body == district58 else ["the report differs from the requirements' block"]
        for check, problems in checks.items():
            for p in problems:
                print(f"{check} {key}: {p}", file=sys.stderr)
            failed += bool(problems)
        stem = key.replace("/", "_")
        words = reference.contest_words(contest)
        (out / f"{stem}.rcv").write_bytes(text)
        (out / f"{stem}.report").write_bytes(report)
        (out / f"{stem}.words").write_bytes(reference.pack(words))
        (out / f"{stem}.result").write_bytes(reference.pack(reference.result_words(words, maine=True)))
        print(f"{key}: {len(contest.ballots)} ballots, {len(rounds)} rounds, largest first-choice share "
              f"{largest_first} of {len(contest.ballots)}, winner {names[winner - 1]}; {note}")
    for title, old, new in PLANTED:
        module = planted(old, new)
        caught = 0
        for entry, sheet_ballots in corpus:
            key = entry["key"]
            text = module.convert(manifest, key, data, practice=key in PRACTICE)
            caught += bool(round_trip(text, sheet_ballots, recount.REPORTS[key][0]))
        print(f"planted error in the converter, {title}: fails {caught} of {len(corpus)} round trips")
        if caught != len(corpus):
            failed += 1
    print(f"{failed} checks failing")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
