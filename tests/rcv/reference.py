# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Reads a canonical ballot file, counts its contest under Oakland City Charter §1105 or 21-A M.R.S. §723-A, and prints the report.

The script transcribes `Demos/Rcv/requirements.md`: the reader of the canonical ballot file and its
error report, the writer, the interpretation of a ballot, the rounds, the report, and the count's
word forms.  The Maine mode transcribes `Demos/Rcv/Maine/requirements.md` with the same reader,
writer, tally, and printer.  Its interpretation adds a rule: an empty position ends the examination
with the reason `exhausted` when the next position is also empty and some later position is marked.
Its initial test elects a counted candidate ranked first alone on more than half of the ballots.
Otherwise each round eliminates the candidate with the fewest votes or, on a tie, the tied candidate
latest in the order, until one candidate continues, two continue with unequal votes, or none
continues.  Its report has the Maine rule line and a line `first i f(i)` for each counted candidate
before round 1, and its result words hold f(1) to f(n) after the number of rounds.

Three further counts serve comparisons and belong to no module: the single count and
the county count, with which the requirements' T10 and T11 compare the charter's count, and the
faulty setting of the comparisons with Alameda County's reports.  The single count is the charter's
count without rule 3.  The county count interprets ballots in the same way, has no majority stop, no
rule 2, and no batch, eliminates by rule 4 while three or more candidates continue, and ends at the
first round with at most two.  The faulty setting is the county count in which round 1 suspends each
ballot whose first position is empty or holds one uncounted candidate and whose interpretation
counts for a candidate or is `overvote`.  Their reports have the report's form with the rule lines
`rule single-count`, `rule alameda-county-count`, and `rule alameda-county-count
first-round-suspension`, and the faulty setting adds `inactive suspended x` after the other inactive
lines of each round.

Commands, where FILE `-` reads standard input:

  reference.py FILE                  the report of the charter's count
  reference.py --single FILE         the report of the single count
  reference.py --county FILE         the report of the county count
  reference.py --suspend FILE        the report of the faulty setting
  reference.py --maine FILE          the report of the Maine count
  reference.py --contest-words FILE  the contest's words, little-endian 64-bit, on standard output
  reference.py --result-words FILE   the count's words, little-endian 64-bit, for the contest words in FILE
  reference.py --maine --result-words FILE
                                     the Maine count's words for the contest words in FILE

--maine leaves the words of --contest-words unchanged, and together with --single, --county, or
--suspend it is a usage error.  A malformed ballot file gives the error report with exit status 0, as
the module returns it.  The exit status is 1 when --contest-words reads a malformed file, and 2 on a
usage error, when FILE cannot be read, or when a word file's length is not a multiple of 8 bytes.
"""

import argparse
import struct
import sys
from collections import Counter
from dataclasses import dataclass, field

RULE = (b"oakland-1105 revision 1, Oakland City Charter sections 1103 and 1105 (February 2007), "
        b"Cal. Elec. Code sections 15341 (updated 1999-01-01) and 15342(d) (updated 2012-01-01), "
        b"texts read 2026-11-09")
MAINE_RULE = (b"maine-723a revision 1, 21-A M.R.S. sections 1, 371, 374-A, 696, 722-A, 723-A, and 732 as "
              b"current through 2026-10-01 (section 723-A as amended by PL 2025 c. 363, effective 2025-09-24), "
              b"29-250 C.M.R. ch. 535 (effective 2018-11-07), texts read 2026-11-10")
RULES = {"charter": RULE, "single": b"single-count", "county": b"alameda-county-count",
         "suspend": b"alameda-county-count first-round-suspension", "maine": MAINE_RULE}
MAX_POSITIONS = 63
MAX_CANDIDATES = 63
MAX_BALLOTS = (1 << 32) - 1
UNNAMED = 1 << 63
KINDS = (b"listed", b"named-writein", b"aggregate-writein", b"excluded")
COUNTED = (b"listed", b"named-writein")
IDENTIFIER_BYTES = frozenset(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.:")
REASONS = ("blank", "uncounted", "overvote", "exhausted")
ELIMINATION_CODES = {None: 0, "lowest": 1, "order": 2, "batch": 3}


@dataclass
class Contest:
    contest: bytes
    positions: int
    candidates: list   # (kind, name) for candidates 1 to n
    order: list        # candidate indices, earliest first
    ballots: list      # (identifier or None, tuple of k position words)


@dataclass
class Malformed:
    line: int
    role: str


@dataclass
class Round:
    number: int
    votes: dict        # continuing candidate -> votes, in increasing index
    inactive: dict     # reason -> ballots
    elimination: str | None = None
    eliminated: list = field(default_factory=list)
    tied: list = field(default_factory=list)

    @property
    def continuing(self):
        return sum(self.votes.values())


def number(text):
    """The value of `text` as a decimal number without leading zeros, or None."""
    if not text or any(c < 0x30 or c > 0x39 for c in text) or (text[0] == 0x30 and len(text) > 1):
        return None
    return int(text)


def is_identifier(text):
    return 1 <= len(text) <= 64 and all(c in IDENTIFIER_BYTES for c in text)


def is_name(text):
    return 1 <= len(text) <= 255 and all(0x20 <= c <= 0x7E or c >= 0x80 for c in text)


def prefixed_number(text, prefix):
    if text is None or not text.startswith(prefix):
        return None
    return number(text[len(prefix):])


def candidate_line(text, i):
    """(kind, name) of the line of candidate `i`, or None."""
    if text is None or not text.startswith(b"candidate "):
        return None
    index, space, rest = text[len(b"candidate "):].partition(b" ")
    if not space or number(index) != i:
        return None
    for kind in KINDS:
        if rest.startswith(kind + b" ") and is_name(rest[len(kind) + 1:]):
            return kind, rest[len(kind) + 1:]
    return None


def order_line(text, n):
    if text is None or not text.startswith(b"order "):
        return None
    order = [number(part) for part in text[len(b"order "):].split(b" ")]
    if None in order or sorted(order) != list(range(1, n + 1)):
        return None
    return order


def position_word(text, n):
    """The word of a position field, or None."""
    if text == b"":
        return 0
    if text == b"*":
        return UNNAMED
    indices = [number(part) for part in text.split(b"|")]
    if None in indices or not all(1 <= i <= n for i in indices):
        return None
    if any(a >= b for a, b in zip(indices, indices[1:])):
        return None
    return sum(1 << (i - 1) for i in indices)


def ballot_line(text, k, n):
    """(identifier or None, position words) of a ballot line, or None."""
    if text is None:
        return None
    fields = text.split(b",")
    if len(fields) == k:
        identifier = None
    elif len(fields) == k + 1 and is_identifier(fields[0]):
        identifier, fields = fields[0], fields[1:]
    else:
        return None
    words = tuple(position_word(f, n) for f in fields)
    if None in words:
        return None
    return identifier, words


def read(data):
    """The contest of a well-formed file, or the Malformed line and role of its first faulty line."""
    *lines, tail = data.split(b"\n")

    def line(j):
        """Line j with its LF removed, or None when it is absent or lacks its LF."""
        return lines[j - 1] if j <= len(lines) else None

    if line(1) != b"rcv-ballots 1":
        return Malformed(1, "format")
    text = line(2)
    if text is None or not text.startswith(b"contest ") or not is_identifier(text[len(b"contest "):]):
        return Malformed(2, "contest")
    contest = text[len(b"contest "):]
    k = prefixed_number(line(3), b"positions ")
    if k is None or not 1 <= k <= MAX_POSITIONS:
        return Malformed(3, "positions")
    n = prefixed_number(line(4), b"candidates ")
    if n is None or not 1 <= n <= MAX_CANDIDATES:
        return Malformed(4, "candidates")
    candidates = []
    for i in range(1, n + 1):
        entry = candidate_line(line(4 + i), i)
        if entry is None:
            return Malformed(4 + i, "candidate")
        candidates.append(entry)
    order = order_line(line(5 + n), n)
    if order is None:
        return Malformed(5 + n, "order")
    count = prefixed_number(line(6 + n), b"ballots ")
    if count is None or count > MAX_BALLOTS:
        return Malformed(6 + n, "ballots")
    ballots = []
    for b in range(1, count + 1):
        entry = ballot_line(line(6 + n + b), k, n)
        if entry is None:
            return Malformed(6 + n + b, "ballot")
        ballots.append(entry)
    if len(lines) > 6 + n + count or tail:
        return Malformed(7 + n + count, "end")
    return Contest(contest, k, candidates, order, ballots)


def position_field(word):
    if word == 0:
        return b""
    if word == UNNAMED:
        return b"*"
    return b"|".join(b"%d" % (i + 1) for i in range(MAX_CANDIDATES) if word >> i & 1)


def write(contest):
    """The canonical file of a contest structure."""
    lines = [b"rcv-ballots 1", b"contest " + contest.contest, b"positions %d" % contest.positions,
             b"candidates %d" % len(contest.candidates)]
    lines += [b"candidate %d %s %s" % (i, kind, name) for i, (kind, name) in enumerate(contest.candidates, 1)]
    lines.append(b"order " + b" ".join(b"%d" % i for i in contest.order))
    lines.append(b"ballots %d" % len(contest.ballots))
    for identifier, words in contest.ballots:
        fields = [position_field(w) for w in words]
        lines.append(b",".join(fields if identifier is None else [identifier] + fields))
    return b"".join(line + b"\n" for line in lines)


def interpret(ballot, counted, continuing, maine=False):
    """The continuing candidate the ballot counts for, or the reason it is inactive.  With `maine`, an
    empty position ends the examination when the next position is also empty and a later one is marked."""
    for p, word in enumerate(ballot):
        if word == 0:
            if maine and p + 1 < len(ballot) and ballot[p + 1] == 0 and any(ballot[p + 2:]):
                return "exhausted"
            continue
        if word == UNNAMED or word & (word - 1):
            return "overvote"
        if word.bit_length() in continuing:
            return word.bit_length()
    marked = [word.bit_length() for word in ballot if word]
    if not marked:
        return "blank"
    if any(i in counted for i in marked):
        return "exhausted"
    return "uncounted"


def suspended(ballot, counted, where):
    """Whether round 1 of the faulty setting suspends a ballot whose interpretation is `where`."""
    first = ballot[0]
    passed = first == 0 or (first != UNNAMED and not first & (first - 1) and first.bit_length() not in counted)
    return passed and (isinstance(where, int) or where == "overvote")


def tally(ballots, counted, continuing, number, suspend=False, maine=False):
    rnd = Round(number, dict.fromkeys(sorted(continuing), 0), dict.fromkeys(REASONS, 0))
    if suspend:
        rnd.inactive["suspended"] = 0
    for ballot, multiplicity in ballots.items():
        where = interpret(ballot, counted, continuing, maine)
        if suspend and number == 1 and suspended(ballot, counted, where):
            rnd.inactive["suspended"] += multiplicity
        elif isinstance(where, int):
            rnd.votes[where] += multiplicity
        else:
            rnd.inactive[where] += multiplicity
    return rnd


def batch(votes):
    """The largest qualifying set of two or more candidates, in increasing index, or []."""
    largest = []
    for x, v in votes.items():
        lower = [y for y, w in votes.items() if w < v]
        if len(lower) >= 2 and v > sum(votes[y] for y in lower) and len(lower) > len(largest):
            largest = lower
    return sorted(largest)


def lowest(rnd, rank):
    """Eliminate the candidate with the fewest votes, a tie going to the latest in the order: the
    charter's rule 4, and Maine's rule "Last place" and tied pair."""
    least = min(rnd.votes.values())
    tied = [i for i, v in rnd.votes.items() if v == least]
    if len(tied) == 1:
        rnd.elimination, rnd.eliminated = "lowest", tied
    else:
        rnd.elimination, rnd.eliminated, rnd.tied = "order", [max(tied, key=rank.get)], tied


def setup(contest):
    counted = {i for i, (kind, _) in enumerate(contest.candidates, 1) if kind in COUNTED}
    rank = {c: p for p, c in enumerate(contest.order)}
    return counted, rank, Counter(words for _, words in contest.ballots)


def charter(contest, batches=True):
    """The rounds of the charter's count, or of the single count without `batches`, and the winner,
    or None for no winner."""
    counted, rank, ballots = setup(contest)
    continuing = set(counted)
    rounds = []
    while True:
        rnd = tally(ballots, counted, continuing, len(rounds) + 1)
        rounds.append(rnd)
        majority = [i for i, v in rnd.votes.items() if 2 * v > rnd.continuing]
        if majority:
            return rounds, majority[0]
        if rnd.continuing == 0:
            return rounds, None
        group = batch(rnd.votes) if batches else []
        if group:
            rnd.elimination, rnd.eliminated = "batch", group
        else:
            lowest(rnd, rank)
        continuing -= set(rnd.eliminated)


def county(contest, suspend=False):
    """The rounds of the county count, or of the faulty setting, and the winner, or None."""
    counted, rank, ballots = setup(contest)
    continuing = set(counted)
    rounds = []
    while True:
        rnd = tally(ballots, counted, continuing, len(rounds) + 1, suspend)
        rounds.append(rnd)
        if len(continuing) <= 2:
            ranked = sorted(rnd.votes.items(), key=lambda iv: -iv[1])
            if not ranked or (len(ranked) == 2 and ranked[0][1] == ranked[1][1]):
                return rounds, None
            return rounds, ranked[0][0]
        lowest(rnd, rank)
        continuing -= set(rnd.eliminated)


def maine_count(contest):
    """The first rankings f(i) of the counted candidates, the rounds of the Maine count, and the winner,
    or None."""
    counted, rank, ballots = setup(contest)
    first = dict.fromkeys(sorted(counted), 0)
    for ballot, multiplicity in ballots.items():
        word = ballot[0]
        if word and word != UNNAMED and not word & (word - 1) and word.bit_length() in counted:
            first[word.bit_length()] += multiplicity
    elected = [i for i, f in first.items() if 2 * f > len(contest.ballots)]
    if elected:
        return first, [], elected[0]
    continuing = set(counted)
    rounds = []
    while True:
        rnd = tally(ballots, counted, continuing, len(rounds) + 1, maine=True)
        rounds.append(rnd)
        tied_pair = len(rnd.votes) == 2 and len(set(rnd.votes.values())) == 1
        if len(rnd.votes) <= 2 and not tied_pair:
            return first, rounds, max(rnd.votes, key=rnd.votes.get, default=None)
        lowest(rnd, rank)
        continuing -= set(rnd.eliminated)


def count(contest, mode="charter"):
    if mode in ("charter", "single"):
        return charter(contest, batches=mode == "charter")
    return county(contest, suspend=mode == "suspend")


def round_lines(rounds, winner):
    lines = []
    for rnd in rounds:
        lines += [b"round %d" % rnd.number, b"continuing %d" % rnd.continuing]
        lines += [b"votes %d %d" % iv for iv in rnd.votes.items()]
        lines += [b"inactive %s %d" % (reason.encode(), x) for reason, x in rnd.inactive.items()]
        if rnd.elimination == "batch":
            lines.append(b"eliminate batch " + b" ".join(b"%d" % i for i in rnd.eliminated))
        elif rnd.elimination == "lowest":
            lines.append(b"eliminate lowest %d" % rnd.eliminated[0])
        elif rnd.elimination == "order":
            lines.append(b"tie " + b" ".join(b"%d" % i for i in rnd.tied))
            lines.append(b"eliminate order %d" % rnd.eliminated[0])
    lines.append(b"winner none" if winner is None else b"winner %d" % winner)
    return lines


def report(data, mode="charter"):
    """The report's bytes for the bytes of a ballot file."""
    contest = read(data)
    lines = [b"rcv-report 1", b"rule " + RULES[mode]]
    if isinstance(contest, Malformed):
        lines.append(b"error %d %s" % (contest.line, contest.role.encode()))
    else:
        lines += data.split(b"\n")[1:6 + len(contest.candidates)]
        if mode == "maine":
            first, rounds, winner = maine_count(contest)
            lines += [b"first %d %d" % iv for iv in first.items()]
        else:
            rounds, winner = count(contest, mode)
        lines += round_lines(rounds, winner)
    return b"".join(line + b"\n" for line in lines)


def contest_words(contest):
    """The contest's words: n, k, N, the kinds, the order, and the position words."""
    words = [len(contest.candidates), contest.positions, len(contest.ballots)]
    words += [KINDS.index(kind) for kind, _ in contest.candidates]
    words += contest.order
    for _, positions in contest.ballots:
        words += positions
    return words


def from_words(words):
    """The contest of a valid word array, with empty identifiers and names, or None."""
    if len(words) < 3:
        return None
    n, k, count = words[:3]
    if not (1 <= n <= MAX_CANDIDATES and 1 <= k <= MAX_POSITIONS and count <= MAX_BALLOTS):
        return None
    if len(words) != 3 + 2 * n + count * k:
        return None
    kinds, order, positions = words[3:3 + n], list(words[3 + n:3 + 2 * n]), words[3 + 2 * n:]
    if any(kind >= len(KINDS) for kind in kinds) or sorted(order) != list(range(1, n + 1)):
        return None
    if not all(w == 0 or w == UNNAMED or 0 < w < 1 << n for w in positions):
        return None
    ballots = [(None, tuple(positions[b * k:(b + 1) * k])) for b in range(count)]
    return Contest(b"", k, [(KINDS[kind], b"") for kind in kinds], order, ballots)


def mask(indices):
    return sum(1 << (i - 1) for i in indices)


def result_words(words, maine=False):
    """The count's words for a contest's words, or [0] for an invalid array.  With `maine`, the words of
    the Maine count, which hold f(1) to f(n), 0 for an uncounted candidate, after the number of rounds."""
    contest = from_words(words)
    if contest is None:
        return [0]
    n = len(contest.candidates)
    if maine:
        first, rounds, winner = maine_count(contest)
        out = [1, len(rounds)] + [first.get(i, 0) for i in range(1, n + 1)]
    else:
        rounds, winner = charter(contest)
        out = [1, len(rounds)]
    for rnd in rounds:
        out += [mask(rnd.votes), rnd.continuing]
        out += [rnd.votes.get(i, 0) for i in range(1, n + 1)]
        out += [rnd.inactive[reason] for reason in REASONS]
        out += [ELIMINATION_CODES[rnd.elimination], mask(rnd.eliminated), mask(rnd.tied)]
    out.append(winner or 0)
    return out


def pack(words):
    return struct.pack(f"<{len(words)}Q", *words)


def unpack(data):
    return list(struct.unpack(f"<{len(data) // 8}Q", data))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--single", action="store_true", help="the charter's count without rule 3")
    mode.add_argument("--county", action="store_true", help="the county count")
    mode.add_argument("--suspend", action="store_true", help="the county count with the first-round suspension")
    mode.add_argument("--contest-words", action="store_true", help="write the contest's words")
    mode.add_argument("--result-words", action="store_true", help="read contest words and write the count's words")
    ap.add_argument("--maine", action="store_true", help="the Maine count of 21-A M.R.S. §723-A")
    ap.add_argument("file", help="input file, or - for standard input")
    args = ap.parse_args()
    if args.maine and (args.single or args.county or args.suspend):
        ap.error("--maine cannot be combined with --single, --county, or --suspend")
    try:
        data = sys.stdin.buffer.read() if args.file == "-" else open(args.file, "rb").read()
    except OSError as e:
        print(f"{args.file}: {e.strerror}", file=sys.stderr)
        return 2
    if args.result_words:
        if len(data) % 8:
            print(f"{args.file}: length {len(data)} bytes is not a multiple of 8", file=sys.stderr)
            return 2
        sys.stdout.buffer.write(pack(result_words(unpack(data), args.maine)))
    elif args.contest_words:
        contest = read(data)
        if isinstance(contest, Malformed):
            print(f"{args.file}: line {contest.line} fails the role {contest.role}", file=sys.stderr)
            return 1
        sys.stdout.buffer.write(pack(contest_words(contest)))
    else:
        mode = ("maine" if args.maine else "single" if args.single else "county" if args.county else
                "suspend" if args.suspend else "charter")
        sys.stdout.buffer.write(report(data, mode))
    return 0


if __name__ == "__main__":
    sys.exit(main())
