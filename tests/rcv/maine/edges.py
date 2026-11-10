# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes the Maine edge cases of the RCV tabulator with the reference's Maine outputs beside them.

Each well-formed case NAME gives `NAME.rcv`, the canonical ballot file, `NAME.report`, the
reference's Maine report, `NAME.words`, the contest's words, and `NAME.result`, the Maine count's
words, the last two as little-endian 64-bit words.  A malformed case gives `NAME.rcv` and
`NAME.report`, the Maine error report.  An edited case gives the files of a well-formed or a
malformed case, as the reader finds it, and a case of the word forms alone gives `NAME.words` and
`NAME.result`.

The Maine cases cover the edge cases that `Demos/Rcv/Maine/requirements.md` lists under Tests and
the requirements' worked example and initial-test example: runs of empty positions at the start,
between marks, at the end, before a multiple position, and before a mark of an uncounted candidate;
a write-in mark and an excluded candidate's mark that end a run; rule 1 of the interpretation
reached only after an elimination; duplicate rankings with and without other candidates; multiple
positions, named and unnamed; the initial test at 2 f(i) = N and N + 1, with blank, multiple, and
uncounted first positions, and with an excluded candidate first alone on more than half of the
ballots; ties at the fewest votes of two and of three or more candidates in rounds of three or more;
tied final pairs with and without continuing ballots; three candidates without a continuing ballot;
no ballots; no counted candidate, one, and two; 63 candidates and 63 positions in 63 rounds; the two
contests of T15; and every ballot of up to four positions over the empty field, each kind of
candidate, two multiple marks, and the unnamed overvote.  The shared cases are the cases of
`tests/rcv/edges.py`, written with the prefix `shared-` and the Maine outputs.

The small Maine cases carry expected report lines or result words derived by hand from the
requirements, never from the reference, and so do two shared cases.  The shared malformed files and
invalid word arrays keep their hand-stated error lines and results, which the Maine module shares.
Every ballot of the pattern contests is also interpreted against each subset of the counted
candidates and compared with a second statement of the interpretation: the earliest position that is
the first of two empty positions before a mark, a multiple position, or a single position for a
continuing candidate decides it.  The script checks the reference against these expectations, checks
that every report's rule line holds the requirements' rule identifier, that the writer reproduces
each file that the reader accepts, and that the result words agree with the report, and exits with
status 1 on any failure.

  edges.py [OUT]     write the files into OUT (default tmp/rcv-maine-edges in the repository)
"""

import argparse
import dataclasses
import itertools
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RCV = HERE.parent
ROOT = RCV.parent.parent
sys.path.insert(0, str(RCV))
import edges as shared  # noqa: E402  tests/rcv/edges.py, which precedes this directory on the path
import reference  # noqa: E402

REQUIREMENTS = ROOT / "Demos" / "Rcv" / "Maine" / "requirements.md"
L, NW, AW, EX = shared.L, shared.NW, shared.AW, shared.EX
Z = shared.ZERO
PATTERN_CANDIDATES = [(L, "A"), (NW, "B"), (AW, "Write-in"), (EX, "X")]
PATTERN_FIELDS = ["", "1", "2", "3", "4", "1|3", "3|4", "*"]


def blocks():
    return re.findall(r"^```\n(.*?)^```$", REQUIREMENTS.read_text(), re.S | re.M)


def rule_identifier():
    return next(b for b in blocks() if b.startswith("maine-723a ")).strip()


def example():
    """The worked example of the requirements with its report."""
    data = next(b for b in blocks() if b.startswith("rcv-ballots 1\n")).encode()
    report = next(b for b in blocks() if b.startswith("contest example-maine\n")).strip().split("\n")
    n = 5
    return shared.Case("example-maine", data, n, {"maine": report[5 + n:]})


def case(name, candidates, k, ballots, expected, order=None, result=None):
    return shared.well_formed(name, candidates, k, ballots, order, "maine-edge", result, maine=expected)


def hand_cases():
    yield example()
    yield case("initial-test-example", shared.listed("A", "B", "C"), 2, ["1,2", "1,", "1,3", ",1", "2,3"], """
first 1 3
first 2 1
first 3 0
winner 1""", result=[1, 0, 3, 1, 0, 1])
    runs = [",1,,", ",,1,", ",,,2", "1,,,", "2,,,", "2,,1,", ",,1|2,", ",1|2,,", ",,3,", ",,4,1", ",3,,", ",,,",
            "2,,,1", "1,,2,"]
    first_round = """
first 1 2
first 2 3
round 1
continuing 6
votes 1 3
votes 2 3
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 5
tie 1 2"""
    yield case("runs", PATTERN_CANDIDATES, 4, runs, first_round + """
eliminate order 2
round 2
continuing 4
votes 1 4
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 7
winner 1""")
    yield case("runs-reversed", PATTERN_CANDIDATES, 4, runs, first_round + """
eliminate order 1
round 2
continuing 4
votes 2 4
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 7
winner 2""", order=[2, 1, 3, 4])
    yield case("marks-end-runs", shared.listed("A", "B") + [(AW, "Write-in"), (EX, "X")], 4,
               ["3,,1,", "4,,1,", ",3,,1", ",4,,1", ",,,1", "3,,,1"] + shared.times("2,,,", 3), """
first 1 0
first 2 3
round 1
continuing 7
votes 1 4
votes 2 3
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 2
winner 1""", result=[1, 1, 0, 3, 0, 0, 3, 7, 4, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1])
    yield case("skip-after-elimination", shared.listed("A", "B", "C"), 4,
               shared.times("1,,,", 3) + shared.times("2,,,", 3) + ["3,,,1", "3,,1,"], f"""
first 1 3
first 2 3
first 3 2
round 1
continuing 8
votes 1 3
votes 2 3
votes 3 2
{Z}
eliminate lowest 3
round 2
continuing 7
votes 1 4
votes 2 3
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 1""")
    yield case("duplicates", shared.listed("A", "B", "C"), 5,
               ["3,3,3,3,3", "3,3,1,,", "3,3,,,1"] + shared.times("1,1,,,", 4) + shared.times("2,2,2,,", 4), f"""
first 1 4
first 2 4
first 3 3
round 1
continuing 11
votes 1 4
votes 2 4
votes 3 3
{Z}
eliminate lowest 3
round 2
continuing 9
votes 1 5
votes 2 4
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 2
winner 1""")
    yield case("overvotes", shared.listed("A", "B", "C") + [(AW, "Write-in"), (EX, "X")], 3,
               ["1|2,,", "*,,", "4|5,1,", "3,1|2,", "3,*,", ",1|2,", ",,*", "1|4,2,", "3,1,"]
               + shared.times("1,,", 4) + shared.times("2,,", 4), """
first 1 4
first 2 4
first 3 3
round 1
continuing 11
votes 1 4
votes 2 4
votes 3 3
inactive blank 0
inactive uncounted 0
inactive overvote 5
inactive exhausted 1
eliminate lowest 3
round 2
continuing 9
votes 1 5
votes 2 4
inactive blank 0
inactive uncounted 0
inactive overvote 7
inactive exhausted 1
winner 1""")
    others = [",1", ",", "1|2,", "3,2", "4,2"]
    yield case("test-equal", shared.listed("A", "B") + [(AW, "Write-in"), (EX, "X")], 2,
               ["1,", "1,2", "1,1", "1,3", "1,4"] + others, """
first 1 5
first 2 0
round 1
continuing 8
votes 1 6
votes 2 2
inactive blank 1
inactive uncounted 0
inactive overvote 1
inactive exhausted 0
winner 1""", result=[1, 1, 5, 0, 0, 0, 3, 8, 6, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1])
    yield case("test-plus-one", shared.listed("A", "B") + [(AW, "Write-in"), (EX, "X")], 2,
               ["1,", "1,", "1,2", "1,1", "1,3", "1,4"] + others, """
first 1 6
first 2 0
winner 1""", result=[1, 0, 6, 0, 0, 0, 1])
    yield case("test-excluded-majority", shared.listed("A", "B") + [(EX, "X")], 2,
               ["3,1", "3,1", "3,2", "1,", "2,"], f"""
first 1 1
first 2 1
round 1
continuing 5
votes 1 3
votes 2 2
{Z}
winner 1""", result=[1, 1, 1, 1, 0, 3, 5, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    tie_lowest = shared.times("1,", 3) + ["2,1", "3,1", "4,2"]
    tie_first = f"""
first 1 3
first 2 1
first 3 1
first 4 1
round 1
continuing 6
votes 1 3
votes 2 1
votes 3 1
votes 4 1
{Z}
tie 2 3 4"""
    yield case("tie-lowest", shared.listed("A", "B", "C", "D"), 2, tie_lowest, tie_first + f"""
eliminate order 4
round 2
continuing 6
votes 1 3
votes 2 2
votes 3 1
{Z}
eliminate lowest 3
round 3
continuing 6
votes 1 4
votes 2 2
{Z}
winner 1""")
    yield case("tie-lowest-reversed", shared.listed("A", "B", "C", "D"), 2, tie_lowest, tie_first + f"""
eliminate order 2
round 2
continuing 6
votes 1 4
votes 3 1
votes 4 1
{Z}
tie 3 4
eliminate order 3
round 3
continuing 6
votes 1 5
votes 4 1
{Z}
winner 1""", order=[4, 3, 2, 1])
    yield case("tie-final", shared.listed("A", "B"), 1, ["1", "2"], f"""
first 1 1
first 2 1
round 1
continuing 2
votes 1 1
votes 2 1
{Z}
tie 1 2
eliminate order 2
round 2
continuing 1
votes 1 1
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 1""", result=[1, 2, 1, 1, 3, 2, 1, 1, 0, 0, 0, 0, 2, 2, 3, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1])
    yield case("tie-final-reversed", shared.listed("A", "B"), 1, ["1", "2"], f"""
first 1 1
first 2 1
round 1
continuing 2
votes 1 1
votes 2 1
{Z}
tie 1 2
eliminate order 1
round 2
continuing 1
votes 2 1
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 2""", order=[2, 1])
    yield case("tie-final-zero", shared.listed("A", "B") + [(AW, "Write-in")], 2, [",", "3,", "1|2,"], """
first 1 0
first 2 0
round 1
continuing 0
votes 1 0
votes 2 0
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 0
tie 1 2
eliminate order 1
round 2
continuing 0
votes 2 0
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 0
winner 2""", order=[2, 1, 3])
    inactive = """
inactive blank 1
inactive uncounted 0
inactive overvote 1
inactive exhausted 1"""
    yield case("no-continuing-three", shared.listed("A", "B", "C"), 3, [",,", "*,,", ",,1"], f"""
first 1 0
first 2 0
first 3 0
round 1
continuing 0
votes 1 0
votes 2 0
votes 3 0{inactive}
tie 1 2 3
eliminate order 1
round 2
continuing 0
votes 2 0
votes 3 0{inactive}
tie 2 3
eliminate order 3
round 3
continuing 0
votes 2 0{inactive}
winner 2""", order=[2, 3, 1])
    yield case("no-ballots", shared.listed("A", "B"), 1, [], f"""
first 1 0
first 2 0
round 1
continuing 0
votes 1 0
votes 2 0
{Z}
tie 1 2
eliminate order 2
round 2
continuing 0
votes 1 0
{Z}
winner 1""", result=[1, 2, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    yield case("no-ballots-one", shared.listed("A"), 1, [], f"""
first 1 0
round 1
continuing 0
votes 1 0
{Z}
winner 1""", result=[1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    yield case("no-ballots-no-counted", [(AW, "Write-in")], 1, [], f"""
round 1
continuing 0
{Z}
winner none""", result=[1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    yield case("no-counted", [(AW, "Write-in"), (EX, "X")], 3, ["1,2,", "2,,", ",,", "1|2,,", ",1,", ",,1"], """
round 1
continuing 0
inactive blank 1
inactive uncounted 3
inactive overvote 1
inactive exhausted 1
winner none""", result=[1, 1, 0, 0, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0, 0])
    yield case("one-counted", [(L, "A"), (AW, "Write-in"), (EX, "X")], 2, ["1,", "2,1", "3,", ",", "2|3,"], """
first 1 1
round 1
continuing 2
votes 1 2
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 0
winner 1""")
    yield case("one-counted-test", [(L, "A"), (EX, "X")], 1, ["1", "1", "2"], """
first 1 2
winner 1""", result=[1, 0, 2, 0, 1])
    yield case("one-counted-zero", [(L, "A"), (AW, "Write-in")], 1, ["2", ""], """
first 1 0
round 1
continuing 0
votes 1 0
inactive blank 1
inactive uncounted 1
inactive overvote 0
inactive exhausted 0
winner 1""")
    yield case("two-counted", PATTERN_CANDIDATES, 2, ["1,", "1,", "2,", "4,1", "3,2", ","], """
first 1 2
first 2 1
round 1
continuing 5
votes 1 3
votes 2 2
inactive blank 1
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner 1""")
    t15 = shared.times("1,2,3", 6) + shared.times("2,1,3", 5) + shared.times("3,2,1", 4)
    yield case("t15-first", shared.listed("A", "B", "C"), 3, t15 + shared.times("3,1,2", 2), f"""
first 1 6
first 2 5
first 3 6
round 1
continuing 17
votes 1 6
votes 2 5
votes 3 6
{Z}
eliminate lowest 2
round 2
continuing 17
votes 1 11
votes 3 6
{Z}
winner 1""")
    yield case("t15-second", shared.listed("A", "B", "C"), 3, t15 + shared.times("1,3,2", 2), f"""
first 1 8
first 2 5
first 3 4
round 1
continuing 17
votes 1 8
votes 2 5
votes 3 4
{Z}
eliminate lowest 3
round 2
continuing 17
votes 1 8
votes 2 9
{Z}
winner 2""")
    yield max_size()


def max_size():
    """63 listed candidates and 63 positions, counted in 63 rounds, the most that 63 candidates allow."""
    n = 63
    empty = [""] * (n - 1)
    ballots = [",".join(map(str, range(1, n + 1))), ",".join(empty + ["63"]),
               ",".join(["|".join(map(str, range(1, n + 1)))] + empty), ",".join(empty + ["*"]),
               ",".join(["", "63"] + empty[1:]), ",".join(["63"] + empty[1:] + ["1"]), ",".join(["1"] + empty)]
    inactive = ["inactive blank 0", "inactive uncounted 0", "inactive overvote 1", "inactive exhausted 2"]
    lines = ["first 1 2"] + [f"first {i} 0" for i in range(2, n)] + ["first 63 1"]
    for r in range(1, 61):
        m = n - r
        lines += [f"round {r}", "continuing 4", "votes 1 2"] + [f"votes {i} 0" for i in range(2, m + 1)]
        lines += ["votes 63 2"] + inactive + ["tie " + " ".join(map(str, range(2, m + 1))), f"eliminate order {m}"]
    lines += ["round 61", "continuing 4", "votes 1 2", "votes 2 0", "votes 63 2"] + inactive + ["eliminate lowest 2"]
    lines += ["round 62", "continuing 4", "votes 1 2", "votes 63 2"] + inactive + ["tie 1 63", "eliminate order 63"]
    lines += ["round 63", "continuing 2", "votes 1 2", "inactive blank 0", "inactive uncounted 0",
              "inactive overvote 1", "inactive exhausted 4", "winner 1"]
    data = shared.ballot_file(shared.listed(*(f"C{i}" for i in range(1, n + 1))), n, ballots, contest="maine-edge")
    return shared.Case("max-size", data, n, {"maine": lines})


def pattern_ballots(k):
    return [tuple(p) for p in itertools.product(PATTERN_FIELDS, repeat=k)]


def pattern_cases():
    """Every ballot of k positions over the pattern fields, for k from 1 to 4, under both orders of the
    counted candidates."""
    for k in range(1, 5):
        ballots = [",".join(p) for p in pattern_ballots(k)]
        for order in ([1, 2, 3, 4], [2, 1, 3, 4]):
            name = f"patterns-k{k}-order-{order[0]}{order[1]}"
            yield shared.Case(name, shared.ballot_file(PATTERN_CANDIDATES, k, ballots, order, "maine-edge"), 4)


SHARED_REPORTS = {"example-1": """
first 1 4
first 2 3
first 3 1
first 4 1
round 1
continuing 11
votes 1 5
votes 2 4
votes 3 1
votes 4 1
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 0
tie 3 4
eliminate order 4
round 2
continuing 10
votes 1 5
votes 2 4
votes 3 1
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 1
eliminate lowest 3
round 3
continuing 10
votes 1 5
votes 2 5
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 1
tie 1 2
eliminate order 1
round 4
continuing 7
votes 2 7
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 4
winner 2"""}
SHARED_RESULTS = {"words-valid": [1, 2, 1, 1, 3, 2, 1, 1, 0, 0, 0, 0, 2, 2, 3, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]}


def shared_cases():
    """The cases of tests/rcv/edges.py with the Maine expectations: their error lines and the results
    [0], which the modules share, and the Maine reports and results stated here."""
    for c in shared.cases():
        expect = {"maine": SHARED_REPORTS[c.name].strip().split("\n")} if c.name in SHARED_REPORTS else {}
        result = c.result if c.result == [0] else SHARED_RESULTS.get(c.name)
        yield dataclasses.replace(c, name="shared-" + c.name, expect=expect, result=result)


def second_reading(ballot, counted, continuing):
    """The Maine interpretation of a ballot, decided by the earliest position that is the first of two
    empty positions before a mark, a multiple position, or a single position for a continuing
    candidate, and otherwise by the ballot's marks."""
    marked = [p for p, w in enumerate(ballot) if w]
    single = {p: ballot[p].bit_length() for p in marked if ballot[p] != reference.UNNAMED
              and not ballot[p] & (ballot[p] - 1)}
    skips = [p for p in range(len(ballot) - 1)
             if not ballot[p] and not ballot[p + 1] and any(q > p + 1 for q in marked)]
    multiples = [p for p in marked if p not in single]
    counts = [p for p, i in single.items() if i in continuing]
    end = min(skips + multiples + counts, default=None)
    if end is None:
        if not marked:
            return "blank"
        return "exhausted" if any(i in counted for i in single.values()) else "uncounted"
    if end in counts:
        return single[end]
    return "overvote" if end in multiples else "exhausted"


def check_interpretations():
    """The pattern ballots whose interpretation by the reference differs from the second reading, and the
    number of interpretations compared."""
    n = len(PATTERN_CANDIDATES)
    counted = {i for i, (kind, _) in enumerate(PATTERN_CANDIDATES, 1) if kind in (L, NW)}
    subsets = [set(s) for r in range(len(counted) + 1) for s in itertools.combinations(sorted(counted), r)]
    differences, compared = [], 0
    for k in range(1, 5):
        for fields in pattern_ballots(k):
            ballot = tuple(reference.position_word(f.encode(), n) for f in fields)
            for s in subsets:
                compared += 1
                got = reference.interpret(ballot, counted, s, maine=True)
                if got != second_reading(ballot, counted, s):
                    differences.append(f"{','.join(fields)} against {sorted(s)}: {got}")
    return differences, compared


def result_lines(result, words):
    """The report lines after the header that a Maine result array describes, with a line for each
    nonzero first-ranking word of an uncounted candidate, which no report holds."""
    n = words[0]
    counted = [i for i in range(1, n + 1) if reference.KINDS[words[2 + i]] in reference.COUNTED]
    lines = [f"first {i} {result[1 + i]}" for i in counted]
    lines += [f"uncounted first {i} {result[1 + i]}" for i in range(1, n + 1) if i not in counted and result[1 + i]]
    return lines + shared.result_lines(result[:2] + result[2 + n:], n)


def check(all_cases, rule):
    """A map from each failing case to its problems."""
    failures = {}
    for c in all_cases:
        problems = []
        if c.edited:
            contest = reference.read(c.data)
            if not isinstance(contest, reference.Malformed) and reference.write(contest) != c.data:
                problems.append("the writer does not reproduce a file that the reader accepts")
        elif c.data is not None:
            contest = reference.read(c.data)
            report = reference.report(c.data, "maine").decode("latin-1").split("\n")[:-1]
            if report[:2] != ["rcv-report 1", "rule " + rule]:
                problems.append("the report's first lines differ from the format line and the rule identifier")
            if c.error is not None:
                expected = ["error %d %s" % c.error]
                if report[2:] != expected:
                    problems.append(f"report {report[2:]}, expected {expected}")
            elif isinstance(contest, reference.Malformed):
                problems.append(f"read fails at line {contest.line} {contest.role}")
            else:
                header = c.data.decode("latin-1").split("\n")[1:6 + c.n]
                body = report[2 + len(header):]
                if report[2:2 + len(header)] != header:
                    problems.append("the report's header differs from the file's")
                if "maine" in c.expect and body != c.expect["maine"]:
                    problems.append("the report differs from the hand-stated one")
                if reference.write(contest) != c.data:
                    problems.append("the writer does not reproduce the file")
                words = reference.contest_words(contest)
                result = reference.result_words(words, maine=True)
                if len(result) < 2 or result[0] != 1 or len(result) != 3 + c.n + result[1] * (c.n + 9):
                    problems.append(f"the result words have the wrong length or first word: {result[:2]}")
                elif result_lines(result, words) != body:
                    problems.append("the result words disagree with the report")
                if c.result is not None and result != c.result:
                    problems.append(f"result words {result}, expected {c.result}")
        else:
            result = reference.result_words(c.words, maine=True)
            if result != c.result:
                problems.append(f"result words {result}, expected {c.result}")
        if problems:
            failures[c.name] = problems
    return failures


def write_files(out, all_cases):
    out.mkdir(parents=True, exist_ok=True)
    for c in all_cases:
        if c.data is not None:
            (out / f"{c.name}.rcv").write_bytes(c.data)
            (out / f"{c.name}.report").write_bytes(reference.report(c.data, "maine"))
            contest = reference.read(c.data)
            if not isinstance(contest, reference.Malformed):
                words = reference.contest_words(contest)
                (out / f"{c.name}.words").write_bytes(reference.pack(words))
                (out / f"{c.name}.result").write_bytes(reference.pack(reference.result_words(words, maine=True)))
        else:
            (out / f"{c.name}.words").write_bytes(reference.pack(c.words))
            (out / f"{c.name}.result").write_bytes(reference.pack(reference.result_words(c.words, maine=True)))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("out", nargs="?", default=ROOT / "tmp" / "rcv-maine-edges",
                    help="output directory (default tmp/rcv-maine-edges in the repository)")
    args = ap.parse_args()
    maine_cases = [*hand_cases(), *pattern_cases()]
    common = list(shared_cases())
    all_cases = maine_cases + common
    names = [c.name for c in all_cases]
    if len(set(names)) != len(names):
        print("edges.py: duplicate case names", file=sys.stderr)
        return 1
    write_files(Path(args.out), all_cases)
    failures = check(all_cases, rule_identifier())
    differences, compared = check_interpretations()
    if differences:
        failures["interpretation"] = differences
    for name, problems in failures.items():
        for problem in problems:
            print(f"{name}: {problem}", file=sys.stderr)
    maine_files = len(maine_cases)
    files = sum(c.data is not None and c.error is None and not c.edited for c in all_cases)
    bad = sum(c.error is not None for c in all_cases)
    edited = [c for c in all_cases if c.edited]
    accepted = sum(not isinstance(reference.read(c.data), reference.Malformed) for c in edited)
    words = sum(c.data is None for c in all_cases)
    stated = sum(bool(c.expect) or c.error is not None or c.result is not None for c in all_cases)
    print(f"{maine_files} Maine and {files - maine_files} shared well-formed files, {bad} malformed files, "
          f"{len(edited)} edited files of which the reader accepts {accepted}, {words} word arrays, "
          f"{stated} with hand-stated expectations, {compared} interpretations compared with the second "
          f"reading, {len(failures)} failing")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
