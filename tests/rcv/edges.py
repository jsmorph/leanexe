# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes the edge cases of the RCV requirements with the reference's outputs beside them.

Each well-formed case NAME gives `NAME.rcv`, the canonical ballot file, `NAME.report`, the
reference's report, `NAME.words`, the contest's words, and `NAME.result`, the count's words, the
last two as little-endian 64-bit words.  A malformed case gives `NAME.rcv` and `NAME.report`, the
error report.  An edited case gives the files of a well-formed or a malformed case, as the reader
finds it, and a case of the word forms alone gives `NAME.words` and `NAME.result`.

The cases cover the edge cases that `Demos/Rcv/requirements.md` lists under Tests: the worked
example; every ballot of up to four positions over the fields empty, a single mark of each kind of
candidate, two multiple marks, and the unnamed overvote, under every order of the counted
candidates; overvotes, named and unnamed, at each position; duplicate rankings; every kind of
candidate; ties at the fewest votes with three candidates and in the final round; batches at the
boundary of the strict test, with tied members, nested, and inside which the single count reaches a
majority; every ballot inactive, no ballots, one candidate, and no counted candidate; 63 candidates
and 63 positions; identifiers of 1 and 64 bytes; names with every class of byte; the two contests of
T15; seeded random contests; malformed files that fail each role; seeded edits of one to three bytes
of the small files; and invalid word arrays.

The small cases carry expected reports, error lines, or result words derived by hand from the
requirements, never from the reference.  The script checks the reference against them, checks that
the writer reproduces each file that the reader accepts and that the result words agree with the
report, and exits with status 1 on any failure.

  edges.py [OUT]     write the files into OUT (default tmp/rcv-edges)
"""

import argparse
import itertools
import random
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import reference  # noqa: E402

REQUIREMENTS = HERE.parent.parent / "Demos" / "Rcv" / "requirements.md"
L, NW, AW, EX = "listed", "named-writein", "aggregate-writein", "excluded"
ID64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
IDENTIFIER_ALPHABET = ID64 + ".:"


@dataclass
class Case:
    name: str
    data: bytes | None = None           # the ballot file
    n: int = 0                          # its number of candidates, when well formed
    expect: dict = field(default_factory=dict)  # mode -> report lines after the header, stated by hand
    error: tuple | None = None          # (line, role) of a malformed file, stated by hand
    words: list | None = None           # a word array, for a case of the word forms alone
    result: list | None = None          # result words stated by hand
    edited: bool = False                # a seeded edit of another case's file, with no stated result


def ballot_file(candidates, k, ballots, order=None, contest="edge"):
    """A canonical file from (kind, name) pairs and ballot lines."""
    order = order or list(range(1, len(candidates) + 1))
    lines = [b"rcv-ballots 1", b"contest " + contest.encode(), b"positions %d" % k,
             b"candidates %d" % len(candidates)]
    for i, (kind, name) in enumerate(candidates, 1):
        name = name if isinstance(name, bytes) else name.encode()
        lines.append(b"candidate %d %s %s" % (i, kind.encode(), name))
    lines.append(b"order " + b" ".join(b"%d" % i for i in order))
    lines.append(b"ballots %d" % len(ballots))
    lines += [b.encode() for b in ballots]
    return b"".join(line + b"\n" for line in lines)


def well_formed(name, candidates, k, ballots, order=None, contest="edge", result=None, **expect):
    data = ballot_file(candidates, k, ballots, order, contest)
    lines = {mode: text.strip().split("\n") for mode, text in expect.items()}
    return Case(name, data, len(candidates), lines, result=result)


def listed(*names):
    return [(L, name) for name in names]


def times(line, m):
    return [line] * m


ZERO = """inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 0"""


def example():
    """The worked example of the requirements with its report."""
    text = REQUIREMENTS.read_text()
    blocks = re.findall(r"^```\n(.*?)^```$", text, re.S | re.M)
    data = next(b for b in blocks if b.startswith("rcv-ballots 1\n")).encode()
    report = next(b for b in blocks if b.startswith("contest example-1\n")).strip().split("\n")
    n = 5
    return Case("example-1", data, n, {"charter": report[5 + n:]})


def hand_cases():
    yield example()
    yield well_formed("no-ballots", listed("A", "B"), 1, [], contest="x", charter=f"""
round 1
continuing 0
votes 1 0
votes 2 0
{ZERO}
winner none""", county=f"""
round 1
continuing 0
votes 1 0
votes 2 0
{ZERO}
winner none""")
    yield well_formed("one-candidate", listed("A"), 1, ["1", ""], charter="""
round 1
continuing 1
votes 1 1
inactive blank 1
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner 1""")
    yield well_formed("one-candidate-blank", listed("A"), 1, [""], charter="""
round 1
continuing 0
votes 1 0
inactive blank 1
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner none""", county="""
round 1
continuing 0
votes 1 0
inactive blank 1
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner 1""")
    yield well_formed("no-counted-candidate", [(AW, "Write-in"), (EX, "X")], 2, ["1,2", "2,", ",", "1|2,"],
                      charter="""
round 1
continuing 0
inactive blank 1
inactive uncounted 2
inactive overvote 1
inactive exhausted 0
winner none""", county="""
round 1
continuing 0
inactive blank 1
inactive uncounted 2
inactive overvote 1
inactive exhausted 0
winner none""")
    yield well_formed("all-inactive", listed("A", "B") + [(AW, "Write-in")], 2,
                      [",", "3,", "*,1", "1|3,", "3,1|2"], charter="""
round 1
continuing 0
votes 1 0
votes 2 0
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
winner none""")
    yield well_formed("tie-final", listed("A", "B"), 1, ["1", "2"], charter=f"""
round 1
continuing 2
votes 1 1
votes 2 1
{ZERO}
tie 1 2
eliminate order 2
round 2
continuing 1
votes 1 1
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 1""", county=f"""
round 1
continuing 2
votes 1 1
votes 2 1
{ZERO}
winner none""", result=[1, 2, 3, 2, 1, 1, 0, 0, 0, 0, 2, 2, 3, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1])
    yield well_formed("tie-final-reversed", listed("A", "B"), 1, ["1", "2"], order=[2, 1], charter=f"""
round 1
continuing 2
votes 1 1
votes 2 1
{ZERO}
tie 1 2
eliminate order 1
round 2
continuing 1
votes 2 1
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 2""")
    yield well_formed("tie-lowest-and-final", listed("A", "B", "C"), 2, ["1,", "1,", "2,1", "3,2"], charter=f"""
round 1
continuing 4
votes 1 2
votes 2 1
votes 3 1
{ZERO}
tie 2 3
eliminate order 3
round 2
continuing 4
votes 1 2
votes 2 2
{ZERO}
tie 1 2
eliminate order 2
round 3
continuing 3
votes 1 3
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
winner 1""")
    yield well_formed("batch-boundary-equal", listed("A", "B", "C", "D"), 1,
                      times("1", 5) + ["2"] + times("3", 2) + times("4", 3), charter=f"""
round 1
continuing 11
votes 1 5
votes 2 1
votes 3 2
votes 4 3
{ZERO}
eliminate lowest 2
round 2
continuing 10
votes 1 5
votes 3 2
votes 4 3
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 1
eliminate lowest 3
round 3
continuing 8
votes 1 5
votes 4 3
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 3
winner 1""", result=[1, 3, 15, 11, 5, 1, 2, 3, 0, 0, 0, 0, 1, 2, 0, 13, 10, 5, 0, 2, 3, 0, 0, 0, 1, 1, 4, 0,
                     9, 8, 5, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 1])
    yield well_formed("batch-boundary-plus-one", listed("A", "B", "C", "D"), 1,
                      times("1", 6) + ["2"] + times("3", 2) + times("4", 4), charter=f"""
round 1
continuing 13
votes 1 6
votes 2 1
votes 3 2
votes 4 4
{ZERO}
eliminate batch 2 3
round 2
continuing 10
votes 1 6
votes 4 4
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 3
winner 1""", result=[1, 2, 15, 13, 6, 1, 2, 4, 0, 0, 0, 0, 3, 6, 0, 9, 10, 6, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 1])
    yield well_formed("batch-tied-members", listed("A", "B", "C", "D"), 1,
                      times("1", 7) + times("2", 2) + times("3", 2) + times("4", 5), charter=f"""
round 1
continuing 16
votes 1 7
votes 2 2
votes 3 2
votes 4 5
{ZERO}
eliminate batch 2 3
round 2
continuing 12
votes 1 7
votes 4 5
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 4
winner 1""")
    yield well_formed("batch-nested", listed("A", "B", "C", "D", "E"), 1,
                      times("1", 16) + times("2", 9) + times("3", 4) + times("4", 2) + ["5"], charter=f"""
round 1
continuing 32
votes 1 16
votes 2 9
votes 3 4
votes 4 2
votes 5 1
{ZERO}
eliminate batch 3 4 5
round 2
continuing 25
votes 1 16
votes 2 9
inactive blank 0
inactive uncounted 0
inactive overvote 0
inactive exhausted 7
winner 1""")
    yield well_formed("batch-single-count-majority", listed("A", "B", "C", "D", "E"), 2,
                      times("1,", 10) + times("5,", 9) + times("2,5", 3) + times("3,1", 2) + ["4,1"], charter=f"""
round 1
continuing 25
votes 1 10
votes 2 3
votes 3 2
votes 4 1
votes 5 9
{ZERO}
eliminate batch 2 3 4
round 2
continuing 25
votes 1 13
votes 5 12
{ZERO}
winner 1""", county=f"""
round 1
continuing 25
votes 1 10
votes 2 3
votes 3 2
votes 4 1
votes 5 9
{ZERO}
eliminate lowest 4
round 2
continuing 25
votes 1 11
votes 2 3
votes 3 2
votes 5 9
{ZERO}
eliminate lowest 3
round 3
continuing 25
votes 1 13
votes 2 3
votes 5 9
{ZERO}
eliminate lowest 2
round 4
continuing 25
votes 1 13
votes 5 12
{ZERO}
winner 1""")
    t15 = times("1,2,3", 6) + times("2,1,3", 5) + times("3,2,1", 4)
    yield well_formed("t15-first", listed("A", "B", "C"), 3, t15 + times("3,1,2", 2), charter=f"""
round 1
continuing 17
votes 1 6
votes 2 5
votes 3 6
{ZERO}
eliminate lowest 2
round 2
continuing 17
votes 1 11
votes 3 6
{ZERO}
winner 1""")
    yield well_formed("t15-second", listed("A", "B", "C"), 3, t15 + times("1,3,2", 2), charter=f"""
round 1
continuing 17
votes 1 8
votes 2 5
votes 3 4
{ZERO}
eliminate lowest 3
round 2
continuing 17
votes 1 8
votes 2 9
{ZERO}
winner 2""")
    yield well_formed("overvote-positions", listed("A", "B", "C") + [(AW, "Write-in")], 3,
                      ["1|2,,", "*,,", ",2|3,", "4,*,", ",,1|2|3", "1,2|4,"] + times("2,,", 3) + times("3,,", 2),
                      charter="""
round 1
continuing 6
votes 1 1
votes 2 3
votes 3 2
inactive blank 0
inactive uncounted 0
inactive overvote 5
inactive exhausted 0
eliminate lowest 1
round 2
continuing 5
votes 2 3
votes 3 2
inactive blank 0
inactive uncounted 0
inactive overvote 6
inactive exhausted 0
winner 2""")
    yield well_formed("duplicates", listed("A", "B", "C"), 3,
                      times("1,1,2", 3) + times("2,2,2", 3) + ["3,3,1", "3,3,3"], charter=f"""
round 1
continuing 8
votes 1 3
votes 2 3
votes 3 2
{ZERO}
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
    yield well_formed("kinds", [(L, "A"), (NW, "B"), (AW, "Write-in"), (EX, "X")], 2,
                      ["3,", "4,3", "4,1", "3,2", "2,", "1,", "1|3,", "2|4,", ","], charter="""
round 1
continuing 4
votes 1 2
votes 2 2
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 0
tie 1 2
eliminate order 2
round 2
continuing 2
votes 1 2
inactive blank 1
inactive uncounted 2
inactive overvote 2
inactive exhausted 2
winner 1""")
    yield well_formed("identifiers", listed("A", "B"), 2, ["a,1,2", ID64 + ",2,", "1,2", ":,,", "7,1,"],
                      contest=ID64, charter="""
round 1
continuing 4
votes 1 3
votes 2 1
inactive blank 1
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner 1""")
    yield well_formed("identifiers-k1", listed("A"), 1, ["", "z,", "z,1", "1"], charter="""
round 1
continuing 2
votes 1 2
inactive blank 2
inactive uncounted 0
inactive overvote 0
inactive exhausted 0
winner 1""")
    names = [b" lead", b"trail ", b"a,b|c*", b"\x80\xc3\xa9\xff",
             bytes(range(0x20, 0x7F)) + bytes(range(0x80, 0x100)) + b"x" * 32]
    yield well_formed("names", [(L, name) for name in names], 1, ["5"], charter=f"""
round 1
continuing 1
votes 1 0
votes 2 0
votes 3 0
votes 4 0
votes 5 1
{ZERO}
winner 5""")
    yield well_formed("suspension", listed("A", "B", "C") + [(AW, "Write-in")], 2,
                      [",1", "4,2", ",*", "4,*", ",", "4,"] + times("1,2", 3) + times("2,", 2) + ["1|2,1", "3,1"],
                      charter="""
round 1
continuing 8
votes 1 4
votes 2 3
votes 3 1
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
eliminate lowest 3
round 2
continuing 8
votes 1 5
votes 2 3
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
winner 1""", county="""
round 1
continuing 8
votes 1 4
votes 2 3
votes 3 1
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
eliminate lowest 3
round 2
continuing 8
votes 1 5
votes 2 3
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
winner 1""", suspend="""
round 1
continuing 6
votes 1 3
votes 2 2
votes 3 1
inactive blank 1
inactive uncounted 1
inactive overvote 1
inactive exhausted 0
inactive suspended 4
eliminate lowest 3
round 2
continuing 8
votes 1 5
votes 2 3
inactive blank 1
inactive uncounted 1
inactive overvote 3
inactive exhausted 0
inactive suspended 0
winner 1""")
    yield max_size()


def max_size():
    """63 listed candidates and 63 positions, with full rankings, overvotes, and a mark at position 63."""
    n = 63
    empties = [""] * (n - 1)
    ballots = [",".join(str(i) for i in range(1, n + 1)), ",".join(empties + ["63"]),
               ",".join(["|".join(str(i) for i in range(1, n + 1))] + empties), ",".join(empties + ["*"])]
    lines = ["round 1", "continuing 2", "votes 1 1"] + [f"votes {i} 0" for i in range(2, n)] + ["votes 63 1"]
    lines += ["inactive blank 0", "inactive uncounted 0", "inactive overvote 2", "inactive exhausted 0"]
    lines.append("eliminate batch " + " ".join(str(i) for i in range(2, n)))
    lines += ["round 2", "continuing 2", "votes 1 1", "votes 63 1", "inactive blank 0", "inactive uncounted 0",
              "inactive overvote 2", "inactive exhausted 0", "tie 1 63", "eliminate order 63"]
    lines += ["round 3", "continuing 1", "votes 1 1", "inactive blank 0", "inactive uncounted 0",
              "inactive overvote 2", "inactive exhausted 1", "winner 1"]
    data = ballot_file(listed(*(f"C{i}" for i in range(1, n + 1))), n, ballots)
    return Case("max-size", data, n, {"charter": lines})


def exhaustive_cases():
    """Every ballot of k positions over nine fields, for k from 1 to 4, under each order of the counted candidates."""
    candidates = [(L, "A"), (L, "B"), (NW, "C"), (AW, "Write-in"), (EX, "X")]
    fields = ["", "1", "2", "3", "4", "5", "1|3", "2|4", "*"]
    for k in range(1, 5):
        ballots = [",".join(p) for p in itertools.product(fields, repeat=k)]
        for perm in ([1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]):
            order = perm + [4, 5]
            name = f"exhaustive-k{k}-order-{''.join(map(str, perm))}"
            yield Case(name, ballot_file(candidates, k, ballots, order), len(candidates))


def random_cases():
    """Seeded random contests: 200 small ones and 20 of up to 12 candidates and 2,000 ballots."""
    for seed in range(220):
        rng = random.Random(seed)
        large = seed >= 200
        n = rng.randint(1, 12 if large else 8)
        k = rng.randint(1, 6)
        kinds = [rng.choice([L, L, L, L, NW, AW, EX]) for _ in range(n)]
        order = rng.sample(range(1, n + 1), n)
        ballots = []
        for _ in range(rng.randint(0, 2000 if large else 60)):
            line = []
            for _ in range(k):
                x = rng.random()
                if x < 0.35:
                    line.append("")
                elif x < 0.85 or n == 1:
                    line.append(str(rng.randint(1, n)))
                elif x < 0.95:
                    line.append("|".join(map(str, sorted(rng.sample(range(1, n + 1), rng.randint(2, n))))))
                else:
                    line.append("*")
            if rng.random() < 0.3:
                line.insert(0, "".join(rng.choice(IDENTIFIER_ALPHABET) for _ in range(rng.randint(1, 64))))
            ballots.append(",".join(line))
        yield Case(f"random-{seed:03d}", ballot_file(list(zip(kinds, (f"K{i}" for i in range(1, n + 1)))), k,
                                                   ballots, order), n)


def edited_cases():
    """Seeded edits of one to three bytes of the hand-stated files."""
    sources = [case.data for case in hand_cases() if case.name != "max-size"]
    alphabet = b"0123456789|*,: \n\r\x00\x7f\x80abcdefghijklmnopqrstuvwxyz-_."
    rng = random.Random(0)
    for m in range(300):
        data = bytearray(rng.choice(sources))
        for _ in range(rng.randint(1, 3)):
            op, i = rng.random(), rng.randrange(len(data) + 1)
            if op < 0.4 and i < len(data):
                data[i] = rng.choice(alphabet)
            elif op < 0.7:
                data[i:i] = bytes([rng.choice(alphabet)])
            elif i < len(data):
                del data[i]
        yield Case(f"edited-{m:03d}", bytes(data), edited=True)


BASE = [b"rcv-ballots 1", b"contest m", b"positions 2", b"candidates 2", b"candidate 1 listed A",
        b"candidate 2 aggregate-writein Write-in", b"order 1 2", b"ballots 2", b"1,2", b",1"]


def malformed(name, line, role, changes=None, data=None):
    """BASE with each line of `changes` replaced by its text or its lines, and the expected error."""
    if data is None:
        lines = list(BASE)
        for j, text in sorted((changes or {}).items(), reverse=True):
            lines[j - 1:j] = text if isinstance(text, list) else [text]
        data = b"".join(x + b"\n" for x in lines)
    return Case(name, data, error=(line, role))


def malformed_cases():
    yield malformed("bad-empty", 1, "format", data=b"")
    yield malformed("bad-format-version", 1, "format", {1: b"rcv-ballots 2"})
    yield malformed("bad-format-no-lf", 1, "format", data=b"rcv-ballots 1")
    yield malformed("bad-format-cr", 1, "format", {1: b"rcv-ballots 1\r"})
    yield malformed("bad-contest-empty", 2, "contest", {2: b"contest "})
    yield malformed("bad-contest-slash", 2, "contest", {2: b"contest a/b"})
    yield malformed("bad-contest-space", 2, "contest", {2: b"contest a b"})
    yield malformed("bad-contest-65", 2, "contest", {2: b"contest " + ID64.encode() + b"a"})
    yield malformed("bad-contest-byte-80", 2, "contest", {2: b"contest caf\xc3\xa9"})
    yield malformed("bad-positions-0", 3, "positions", {3: b"positions 0"})
    yield malformed("bad-positions-64", 3, "positions", {3: b"positions 64"})
    yield malformed("bad-positions-leading-zero", 3, "positions", {3: b"positions 02"})
    yield malformed("bad-positions-empty", 3, "positions", {3: b"positions "})
    yield malformed("bad-candidates-0", 4, "candidates", {4: b"candidates 0"})
    yield malformed("bad-candidates-64", 4, "candidates", {4: b"candidates 64"})
    yield malformed("bad-candidates-leading-zero", 4, "candidates", {4: b"candidates 02"})
    yield malformed("bad-candidates-more-than-lines", 7, "candidate", {4: b"candidates 3"})
    yield malformed("bad-candidates-fewer-than-lines", 6, "order", {4: b"candidates 1"})
    yield malformed("bad-candidate-index", 5, "candidate", {5: b"candidate 2 listed A"})
    yield malformed("bad-candidate-index-leading-zero", 5, "candidate", {5: b"candidate 01 listed A"})
    yield malformed("bad-candidate-kind", 5, "candidate", {5: b"candidate 1 writein A"})
    yield malformed("bad-candidate-name-empty", 5, "candidate", {5: b"candidate 1 listed "})
    yield malformed("bad-candidate-name-7f", 5, "candidate", {5: b"candidate 1 listed A\x7f"})
    yield malformed("bad-candidate-name-tab", 6, "candidate", {6: b"candidate 2 aggregate-writein Write\tin"})
    yield malformed("bad-candidate-name-256", 5, "candidate", {5: b"candidate 1 listed " + b"A" * 256})
    yield malformed("bad-candidate-double-space", 5, "candidate", {5: b"candidate  1 listed A"})
    yield malformed("bad-order-repeat", 7, "order", {7: b"order 1 1"})
    yield malformed("bad-order-short", 7, "order", {7: b"order 1"})
    yield malformed("bad-order-long", 7, "order", {7: b"order 1 2 3"})
    yield malformed("bad-order-zero", 7, "order", {7: b"order 0 1"})
    yield malformed("bad-order-none", 7, "order", {7: b"order"})
    yield malformed("bad-order-double-space", 7, "order", {7: b"order 1  2"})
    yield malformed("bad-order-trailing-space", 7, "order", {7: b"order 1 2 "})
    yield malformed("bad-ballots-2-32", 8, "ballots", {8: b"ballots 4294967296"})
    yield malformed("bad-ballots-leading-zero", 8, "ballots", {8: b"ballots 02"})
    yield malformed("bad-ballots-negative", 8, "ballots", {8: b"ballots -1"})
    yield malformed("bad-ballots-above-lines", 11, "ballot", {8: b"ballots 3"})
    yield malformed("bad-ballots-below-lines", 10, "end", {8: b"ballots 1"})
    yield malformed("bad-ballots-above-with-bad-line", 10, "ballot", {8: b"ballots 5", 10: b"x"})
    yield malformed("bad-ballot-index-0", 9, "ballot", {9: b"0,1"})
    yield malformed("bad-ballot-index-above-n", 9, "ballot", {9: b"3,1"})
    yield malformed("bad-ballot-decreasing", 9, "ballot", {9: b"2|1,"})
    yield malformed("bad-ballot-repeated", 9, "ballot", {9: b"1|1,"})
    yield malformed("bad-ballot-leading-zero", 9, "ballot", {9: b"01,2"})
    yield malformed("bad-ballot-few-fields", 9, "ballot", {9: b"1"})
    yield malformed("bad-ballot-many-fields", 9, "ballot", {9: b"a,1,2,"})
    yield malformed("bad-ballot-identifier-slash", 9, "ballot", {9: b"a/b,1,2"})
    yield malformed("bad-ballot-identifier-65", 9, "ballot", {9: ID64.encode() + b"a,1,2"})
    yield malformed("bad-ballot-identifier-empty", 9, "ballot", {9: b",1,2"})
    yield malformed("bad-ballot-cr", 9, "ballot", {9: b"1,2\r"})
    yield malformed("bad-ballot-nul", 10, "ballot", {10: b",\x001"})
    yield malformed("bad-ballot-star-pipe", 9, "ballot", {9: b"*|1,"})
    yield malformed("bad-ballot-pipe-empty", 9, "ballot", {9: b"1|,2"})
    yield malformed("bad-ballot-space", 9, "ballot", {9: b" 1,2"})
    yield malformed("bad-ballot-two-stars", 9, "ballot", {9: b"**,"})
    yield malformed("bad-end-extra-line", 11, "end", {10: [b",1", b"1,2"]})
    yield malformed("bad-end-empty-line", 11, "end", {10: [b",1", b""]})
    yield malformed("bad-end-k1-empty-line", 11, "end",
                    data=b"rcv-ballots 1\ncontest m\npositions 1\ncandidates 1\ncandidate 1 listed A\n"
                         b"order 1\nballots 3\n1\n\n1\n\n")
    yield malformed("bad-end-bytes-without-lf", 8, "end",
                    data=b"rcv-ballots 1\ncontest m\npositions 1\ncandidates 1\ncandidate 1 listed A\n"
                         b"order 1\nballots 0\nxyz")
    yield malformed("bad-ballot-no-final-lf", 10, "ballot", data=b"\n".join(BASE))
    yield malformed("bad-ballots-no-final-lf", 7, "ballots",
                    data=b"rcv-ballots 1\ncontest m\npositions 1\ncandidates 1\ncandidate 1 listed A\n"
                         b"order 1\nballots 0")


def word_cases():
    """Invalid word arrays, each of whose results is [0], beside one valid array."""
    valid = [2, 1, 2, 0, 0, 1, 2, 1, 2]
    arrays = {
        "words-empty": [],
        "words-too-short": [2, 1],
        "words-extra-word": valid + [0],
        "words-missing-word": valid[:-1],
        "words-n-0": [0, 1, 0],
        "words-n-64": [64, 1, 0] + [0] * 64 + list(range(1, 65)),
        "words-k-0": [2, 0, 0, 0, 0, 1, 2],
        "words-k-64": [2, 64, 0, 0, 0, 1, 2],
        "words-ballots-2-32": [2, 1, 1 << 32, 0, 0, 1, 2],
        "words-kind-4": [2, 1, 2, 0, 4, 1, 2, 1, 2],
        "words-order-repeat": [2, 1, 2, 0, 0, 1, 1, 1, 2],
        "words-order-zero": [2, 1, 2, 0, 0, 0, 1, 1, 2],
        "words-order-above-n": [2, 1, 2, 0, 0, 1, 3, 1, 2],
        "words-bit-63-and-another": [2, 1, 2, 0, 0, 1, 2, 1, (1 << 63) | 1],
        "words-bit-at-n": [2, 1, 2, 0, 0, 1, 2, 1, 4],
        "words-all-bits": [2, 1, 2, 0, 0, 1, 2, 1, (1 << 64) - 1],
    }
    for name, words in arrays.items():
        yield Case(name, words=words, result=[0])
    yield Case("words-valid", words=valid,
               result=[1, 2, 3, 2, 1, 1, 0, 0, 0, 0, 2, 2, 3, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1])


def cases():
    return [*hand_cases(), *exhaustive_cases(), *random_cases(), *malformed_cases(), *edited_cases(),
            *word_cases()]


def result_lines(result, n):
    """The round lines of the report that a result array describes."""
    lines = []
    rounds = result[1]
    for r in range(rounds):
        w = result[2 + r * (n + 9):2 + (r + 1) * (n + 9)]
        members = [i for i in range(1, n + 1) if w[0] >> (i - 1) & 1]
        lines += [f"round {r + 1}", f"continuing {w[1]}"] + [f"votes {i} {w[1 + i]}" for i in members]
        lines += [f"inactive {reason} {x}" for reason, x in zip(reference.REASONS, w[n + 2:n + 6])]
        gone = [str(i) for i in range(1, n + 1) if w[n + 7] >> (i - 1) & 1]
        tied = [str(i) for i in range(1, n + 1) if w[n + 8] >> (i - 1) & 1]
        if w[n + 6] == 1:
            lines.append("eliminate lowest " + " ".join(gone))
        elif w[n + 6] == 2:
            lines += ["tie " + " ".join(tied), "eliminate order " + " ".join(gone)]
        elif w[n + 6] == 3:
            lines.append("eliminate batch " + " ".join(gone))
    lines.append(f"winner {result[-1]}" if result[-1] else "winner none")
    return lines


def check(ref, all_cases):
    """A map from each failing case of `ref`, a module with the reference's functions, to its problems."""
    failures = {}
    for case in all_cases:
        problems = []
        if case.edited:
            contest = ref.read(case.data)
            if not isinstance(contest, ref.Malformed) and ref.write(contest) != case.data:
                problems.append("the writer does not reproduce a file that the reader accepts")
        elif case.data is not None:
            contest = ref.read(case.data)
            report = ref.report(case.data).decode("latin-1").split("\n")[:-1]
            if case.error is not None:
                expected = ["error %d %s" % case.error]
                if report[2:] != expected:
                    problems.append(f"report {report[2:]}, expected {expected}")
            elif isinstance(contest, ref.Malformed):
                problems.append(f"read fails at line {contest.line} {contest.role}")
            else:
                header = case.data.decode("latin-1").split("\n")[1:6 + case.n]
                for mode, body in case.expect.items():
                    lines = ref.report(case.data, mode).decode("latin-1").split("\n")[:-1]
                    if lines[2:] != header + body:
                        problems.append(f"{mode} report differs from the hand-stated one")
                if ref.write(contest) != case.data:
                    problems.append("the writer does not reproduce the file")
                result = ref.result_words(ref.contest_words(contest))
                if result_lines(result, case.n) != report[2 + len(header):]:
                    problems.append("the result words disagree with the report")
                if case.result is not None and result != case.result:
                    problems.append(f"result words {result}, expected {case.result}")
        else:
            result = ref.result_words(case.words)
            if result != case.result:
                problems.append(f"result words {result}, expected {case.result}")
        if problems:
            failures[case.name] = problems
    return failures


def write_files(out, all_cases):
    out.mkdir(parents=True, exist_ok=True)
    for case in all_cases:
        if case.data is not None:
            (out / f"{case.name}.rcv").write_bytes(case.data)
            (out / f"{case.name}.report").write_bytes(reference.report(case.data))
            contest = reference.read(case.data)
            if not isinstance(contest, reference.Malformed):
                words = reference.contest_words(contest)
                (out / f"{case.name}.words").write_bytes(reference.pack(words))
                (out / f"{case.name}.result").write_bytes(reference.pack(reference.result_words(words)))
        else:
            (out / f"{case.name}.words").write_bytes(reference.pack(case.words))
            (out / f"{case.name}.result").write_bytes(reference.pack(reference.result_words(case.words)))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("out", nargs="?", default="tmp/rcv-edges", help="output directory (default tmp/rcv-edges)")
    args = ap.parse_args()
    all_cases = cases()
    names = [case.name for case in all_cases]
    if len(set(names)) != len(names):
        print("edges.py: duplicate case names", file=sys.stderr)
        return 1
    write_files(Path(args.out), all_cases)
    failures = check(reference, all_cases)
    for name, problems in failures.items():
        for problem in problems:
            print(f"{name}: {problem}", file=sys.stderr)
    files = sum(case.data is not None and case.error is None and not case.edited for case in all_cases)
    bad = sum(case.error is not None for case in all_cases)
    edited = [case for case in all_cases if case.edited]
    accepted = sum(not isinstance(reference.read(case.data), reference.Malformed) for case in edited)
    words = sum(case.data is None for case in all_cases)
    stated = sum(bool(case.expect) or case.error is not None or case.result is not None for case in all_cases)
    print(f"{files} well-formed files, {bad} malformed files, {len(edited)} edited files of which the reader "
          f"accepts {accepted}, {words} word arrays, {stated} with hand-stated expectations, "
          f"{len(failures)} failing")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
