# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Checks the converter and the reference against the requirements, the County's reports, and planted errors.

The checks read their expected values from sources other than the reference:

  rule identifier  the reference's rule line equals the requirements' block
  worked example   the report of the requirements' example file equals the requirements' report
  District 4       the converted District 4 record's rounds equal the requirements' block
  Table A          the faulty setting on District 4 gives the figures of the Registrar's Table A
  edge NAME        a case of `edges.py` gives its hand-stated report, error, or result words
  round trip KEY   the reference reads the converted file back to the CVR's rankings, and its
                   writer reproduces the file
  charter KEY      the charter's count against the County's report, by the requirements' comparison
                   rule, or by winner alone for a report with the 2022 suspension
  county KEY       the county count against every round of a report without the suspension
  suspend KEY      the faulty setting against every round of a report with the suspension

For the contests whose CVR lacks ballots of the report, a compared round passes when each of the
County's figures equals or exceeds the reference's and the excesses sum to the missing ballots.

Each planted error is a copy of `reference.py` or `convert.py` with one change.  A copy of the
reference must fail every check predicted for it, and a copy of the converter must fail the round
trip of every contest.  The script prints every check that each copy fails.  The script writes each
converted contest under DATA/canonical with the reference's report, contest words, and result words,
prints one line per contest and per planted error, and exits with status 1 if a check of the
reference fails, a planted error passes a check predicted to fail, or a file is missing.

  check.py [--data DIR]
"""

import argparse
import json
import re
import sys
import types
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import convert  # noqa: E402
import district4  # noqa: E402
import edges  # noqa: E402
import reference  # noqa: E402
import reports  # noqa: E402

REQUIREMENTS = HERE.parent.parent / "Demos" / "Rcv" / "requirements.md"
D4 = "248/Oakland/007-SchoolDirector_District_4"
CATEGORIES = ("blanks", "overvotes", "exhausted", "suspended")

PLANTED = [
    ("a non-strict batch test",
     "if len(lower) >= 2 and v > sum(votes[y] for y in lower)",
     "if len(lower) >= 2 and v >= sum(votes[y] for y in lower)",
     ["edge tie-lowest-and-final", "edge batch-boundary-equal", "edge suspension"]),
    ("the smallest qualifying set",
     "and len(lower) > len(largest):",
     "and (not largest or len(lower) < len(largest)):",
     ["edge batch-nested"]),
    ("a tie that eliminates the candidate earliest in the order",
     "max(tied, key=rank.get)",
     "min(tied, key=rank.get)",
     ["worked example", "edge example-1", "edge tie-final", "edge tie-final-reversed",
      "edge tie-lowest-and-final", "edge kinds", "edge max-size", "edge words-valid"]),
    ("an overvote passed like an empty position",
     'return "overvote"\n        if word.bit_length()',
     'continue\n        if word.bit_length()',
     ["worked example", "District 4", "Table A", "edge overvote-positions", "edge all-inactive",
      "charter 252/Oakland/002-CityCouncil_District_1", "county 252/Oakland/002-CityCouncil_District_1",
      "suspend 248/Oakland/001-Mayor"]),
    ("an overvote only when two continuing candidates are marked",
     'return "overvote"\n        if word.bit_length()',
     'marks = [i for i in continuing if word >> (i - 1) & 1]\n'
     '            if len(marks) >= 2:\n'
     '                return "overvote"\n'
     '            if marks:\n'
     '                return marks[0]\n'
     '            continue\n'
     '        if word.bit_length()',
     ["worked example", "District 4", "edge overvote-positions"]),
    ("the aggregate write-in counted",
     'COUNTED = (b"listed", b"named-writein")',
     'COUNTED = (b"listed", b"named-writein", b"aggregate-writein")',
     ["worked example", "District 4", "edge all-inactive", "edge kinds", "edge no-counted-candidate",
      "county 252/Oakland/002-CityCouncil_District_1"]),
]
CONVERTER_PLANTED = [
    ("an overvote written as an empty field",
     'fields = {SKIPPED: b"", OVERVOTE: b"*"}',
     'fields = {SKIPPED: b"", OVERVOTE: b""}'),
    ("candidate indices reversed",
     'fields.update((name, b"%d" % i) for name, i in index.items())',
     'fields.update((name, b"%d" % (len(index) + 1 - i)) for name, i in index.items())'),
]


def requirement_blocks():
    text = REQUIREMENTS.read_text()
    blocks = re.findall(r"^```\n(.*?)^```$", text, re.S | re.M)

    def block(prefix):
        found = [b for b in blocks if b.startswith(prefix)]
        if len(found) != 1:
            raise SystemExit(f"check.py: {len(found)} blocks of the requirements start with {prefix!r}")
        return found[0].encode()

    return {"rule": block("oakland-1105 "), "example": block("rcv-ballots 1\n"),
            "example report": block("contest example-1\n"), "District 4": block("round 1\ncontinuing 26432\n")}


class Contest:
    """A corpus contest: its report, its CVR, the converted file, and the reference's reading of it."""

    def __init__(self, entry, data_dir):
        self.key = entry["key"]
        self.report = reports.parse(data_dir / entry["report"]["path"])
        cvr = data_dir / entry["cvr"]["path"]
        self.stem = cvr.stem
        self.header, self.rows = convert.read_cvr(cvr)
        self.names = self.report["candidates"]
        self.data = convert.convert(self.header, self.rows, self.names, self.stem)
        self.contest = reference.read(self.data)
        if isinstance(self.contest, reference.Malformed):
            raise SystemExit(f"check.py: {self.key}: the converted file fails at line {self.contest.line}")
        self.index_names = {i: name.decode() for i, (_, name) in enumerate(self.contest.candidates, 1)}
        first = self.report["rounds"][0]
        self.missing = first["continuing"] + first["non_transferable"] - len(self.rows)
        self.suspension = self.report["settings"].get("useFirstRoundSuspension") == "True"


def round_trip(c, data):
    """Problems of reading a converted file back against the CVR's rankings."""
    contest = reference.read(data)
    if isinstance(contest, reference.Malformed):
        return [f"the file fails at line {contest.line} with the role {contest.role}"]
    problems = []
    expected = [(b"listed", name.encode()) for name in c.names] + [(b"aggregate-writein", b"Write-in")]
    if contest.candidates != expected:
        problems.append("the candidates differ from the report's and the aggregate write-in")
    if contest.contest != c.stem.encode() or contest.order != list(range(1, len(expected) + 1)):
        problems.append("the contest identifier or the order differs")
    ranks = [i for i, h in enumerate(c.header) if h.startswith("rank")]
    if contest.positions != len(ranks) or len(contest.ballots) != len(c.rows):
        problems.append("the positions or the ballot count differ from the CVR")
    index = {name.decode(): i for i, (_, name) in enumerate(contest.candidates, 1)}
    identifier = c.header.index("ballotID")
    for number, (row, (ident, words)) in enumerate(zip(c.rows, contest.ballots), 2):
        marks = [row[i] for i in ranks]
        want = tuple(0 if m == "skipped" else reference.UNNAMED if m == "overvote"
                     else 1 << (index[m] - 1) if m in index else None for m in marks)
        if ident != row[identifier].encode() or words != want:
            problems.append(f"CVR row {number} reads back as {ident} {words}")
            break
    if reference.write(contest) != data:
        problems.append("the reference's writer does not reproduce the file")
    return problems


def figures(rnd, names):
    out = {names[i]: v for i, v in rnd.votes.items()}
    out.update(blanks=rnd.inactive["blank"] + rnd.inactive["uncounted"], overvotes=rnd.inactive["overvote"],
               exhausted=rnd.inactive["exhausted"], suspended=rnd.inactive.get("suspended", 0))
    return out


def published(rnd, continuing):
    out = {name: rnd["tallies"][name] for name in continuing}
    out.update({k: rnd[k] for k in CATEGORIES})
    return out


def differences(ours, theirs, missing):
    """Exact equality, or, with ballots missing from the CVR, the County's excesses summing to them."""
    if missing == 0:
        return [f"{k} {ours[k]} against {theirs[k]}" for k in theirs if ours[k] != theirs[k]]
    excess = {k: theirs[k] - ours[k] for k in theirs}
    problems = [f"{k} {ours[k]} above the County's {theirs[k]}" for k, x in excess.items() if x < 0]
    if sum(excess.values()) != missing:
        problems.append(f"the County's figures exceed ours by {sum(excess.values())}, not {missing}")
    return problems


def compare_charter(c, rounds, winner):
    """The requirements' comparison rule for a report without the suspension."""
    problems = []
    report_rounds = c.report["rounds"]
    sets = reports.continuing_sets(c.report)
    shift = 0
    for rnd in rounds:
        if len(rnd.votes) < 2:
            break
        q = rnd.number + shift
        if q > len(report_rounds):
            problems.append(f"round {rnd.number}: the report ends at round {len(report_rounds)}")
            break
        if {c.index_names[i] for i in rnd.votes} != set(sets[q - 1]):
            problems.append(f"round {rnd.number}: the continuing set differs from report round {q}'s")
            break
        pub = report_rounds[q - 1]
        problems += [f"round {rnd.number} (report round {q}): {p}"
                     for p in differences(figures(rnd, c.index_names), published(pub, sets[q - 1]), c.missing)]
        if rnd.elimination in ("lowest", "order") and pub["eliminated"]:
            if pub["eliminated"] != [c.index_names[i] for i in rnd.eliminated]:
                problems.append(f"round {rnd.number}: eliminates {rnd.eliminated}, the report {pub['eliminated']}")
        if rnd.elimination == "batch":
            shift += len(rnd.eliminated) - 1
    return problems + compare_winner(c, rounds, winner)


def compare_winner(c, rounds, winner):
    last = rounds[-1]
    if winner is None or not (last.number == 1 or len(last.votes) >= 2):
        return [f"the comparison rule does not apply to winner {winner} in round {last.number}"]
    if c.report["rounds"][-1]["elected"] != [c.index_names[winner]]:
        return [f"winner {c.index_names[winner]}, the report {c.report['rounds'][-1]['elected']}"]
    return []


def compare_rounds(c, rounds, winner):
    """Every round of the county count or the faulty setting against the report's."""
    problems = []
    report_rounds = c.report["rounds"]
    if len(rounds) != len(report_rounds):
        problems.append(f"{len(rounds)} rounds, the report {len(report_rounds)}")
    for rnd, pub, continuing in zip(rounds, report_rounds, reports.continuing_sets(c.report)):
        if {c.index_names[i] for i in rnd.votes} != set(continuing):
            problems.append(f"round {rnd.number}: the continuing set differs")
            break
        problems += [f"round {rnd.number}: {p}"
                     for p in differences(figures(rnd, c.index_names), published(pub, continuing), c.missing)]
        if [c.index_names[i] for i in rnd.eliminated] != pub["eliminated"]:
            problems.append(f"round {rnd.number}: eliminates {rnd.eliminated}, the report {pub['eliminated']}")
    elected = [c.index_names[winner]] if winner else []
    if elected != report_rounds[-1]["elected"]:
        problems.append(f"winner {elected}, the report {report_rounds[-1]['elected']}")
    return problems


def table_a(c, ref):
    """The faulty setting on District 4 against Table A of the Registrar's presentation."""
    rounds, _ = ref.count(c.contest, "suspend")
    problems = []
    if len(rounds) != len(district4.CERTIFIED):
        problems.append(f"{len(rounds)} rounds, Table A {len(district4.CERTIFIED)}")
    for rnd, table in zip(rounds, district4.CERTIFIED):
        ours = {c.index_names[i]: v for i, v in rnd.votes.items()}
        if ours != table["tallies"] or rnd.inactive["suspended"] != table.get("suspended", 0):
            problems.append(f"round {rnd.number}: {ours}, suspended {rnd.inactive['suspended']}, Table A {table}")
    return problems


def run_checks(ref, blocks, corpus, cases):
    """The names of the checks run, and a map from each failing check to its problems."""
    results = {}
    results["rule identifier"] = [] if ref.RULE + b"\n" == blocks["rule"] else ["the rule identifier differs"]
    expected = b"rcv-report 1\nrule " + blocks["rule"] + blocks["example report"]
    results["worked example"] = [] if ref.report(blocks["example"]) == expected else ["the report differs"]
    for c in corpus:
        if c.key == D4:
            n = len(c.contest.candidates)
            body = ref.report(c.data).split(b"\n", 7 + n)[-1]
            results["District 4"] = [] if body == blocks["District 4"] else ["the rounds differ"]
            results["Table A"] = table_a(c, ref)
    failures = edges.check(ref, cases)
    for case in cases:
        results[f"edge {case.name}"] = failures.get(case.name, [])
    for c in corpus:
        rounds, winner = ref.count(c.contest, "charter")
        if c.suspension:
            results[f"charter {c.key}"] = compare_winner(c, rounds, winner)
            results[f"suspend {c.key}"] = compare_rounds(c, *ref.count(c.contest, "suspend"))
        else:
            results[f"charter {c.key}"] = compare_charter(c, rounds, winner)
            results[f"county {c.key}"] = compare_rounds(c, *ref.count(c.contest, "county"))
    return results


def planted(path, old, new):
    """A module of the script at `path` with `old` replaced by `new`."""
    source = path.read_text()
    if source.count(old) != 1:
        raise SystemExit(f"check.py: the planted change's text occurs {source.count(old)} times in {path.name}: "
                         f"{old!r}")
    name = "planted_" + path.stem
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(source.replace(old, new), str(path), "exec"), module.__dict__)
    return module


def summary(c):
    rounds, winner = reference.count(c.contest, "charter")
    batches = [f"round {r.number} batch of {len(r.eliminated)}" for r in rounds if r.elimination == "batch"]
    county_rounds, _ = reference.count(c.contest, "suspend" if c.suspension else "county")
    return (f"{c.key}: {len(c.rows)} ballots, {c.missing} missing; charter {len(rounds)} rounds, winner "
            f"{c.index_names[winner] if winner else 'none'}" + (", " + ", ".join(batches) if batches else "") +
            f"; {'faulty setting' if c.suspension else 'county count'} {len(county_rounds)} rounds")


def write_outputs(c, out):
    out.mkdir(parents=True, exist_ok=True)
    words = reference.contest_words(c.contest)
    (out / f"{c.stem}.rcv").write_bytes(c.data)
    (out / f"{c.stem}.report").write_bytes(reference.report(c.data))
    (out / f"{c.stem}.words").write_bytes(reference.pack(words))
    (out / f"{c.stem}.result").write_bytes(reference.pack(reference.result_words(words)))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data", default="tmp/rcv-data", help="data directory (default tmp/rcv-data)")
    args = ap.parse_args()
    data_dir = Path(args.data)
    manifest = json.loads((HERE / "manifest.json").read_text())
    blocks = requirement_blocks()
    corpus = []
    for entry in manifest["contests"]:
        if "cvr" not in entry:
            continue
        try:
            corpus.append(Contest(entry, data_dir))
        except (OSError, convert.ConversionError, reports.ReportError) as e:
            print(f"{entry['key']}: {e}", file=sys.stderr)
            return 1
    cases = edges.cases()
    failed = 0
    for c in corpus:
        problems = round_trip(c, c.data)
        for p in problems:
            print(f"round trip {c.key}: {p}", file=sys.stderr)
        failed += bool(problems)
        write_outputs(c, data_dir / "canonical")
        print(summary(c))
    results = run_checks(reference, blocks, corpus, cases)
    for name, problems in results.items():
        for p in problems:
            print(f"{name}: {p}", file=sys.stderr)
        failed += bool(problems)
    print(f"reference: {len(results) + len(corpus)} checks, {failed} failing")
    for title, old, new in CONVERTER_PLANTED:
        module = planted(HERE / "convert.py", old, new)
        caught = sum(bool(round_trip(c, module.convert(c.header, c.rows, c.names, c.stem))) for c in corpus)
        print(f"planted error in the converter, {title}: fails {caught} of {len(corpus)} round trips")
        if caught != len(corpus):
            print(f"planted error in the converter, {title}: passes {len(corpus) - caught} round trips",
                  file=sys.stderr)
            failed += 1
    for title, old, new, predicted in PLANTED:
        results = run_checks(planted(HERE / "reference.py", old, new), blocks, corpus, cases)
        caught = [name for name, problems in results.items() if problems]
        missed = [name for name in predicted if name not in results or not results[name]]
        print(f"planted error, {title}: fails {', '.join(caught) or 'no check'}")
        if missed:
            print(f"planted error, {title}: passes the predicted checks {', '.join(missed)}", file=sys.stderr)
            failed += 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
