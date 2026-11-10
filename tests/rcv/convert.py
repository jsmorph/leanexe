# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Converts D. Otis's CSV cast vote record of an Oakland contest to the canonical ballot file.

The output follows the grammar and the tables of `Demos/Rcv/requirements.md`.  The candidates are
the listed candidates in the order of the County's report, with --report, or else the distinct
candidate names of the record in increasing order of their UTF-8 bytes, each of kind `listed`,
followed by `Write-in` of kind `aggregate-writein`.  The record's `Write-in` marks name no one, and
no County report of the corpus lists a write-in candidate, so the converter assigns no
`named-writein` or `excluded` kind.  The tie-break order is the one given with --order, or else
1 to n.  The contest identifier is the one given with --contest, or else the record file's name
without its extension.

The ranking columns `rank1` to `rankk` give the positions.  A ranking `skipped` writes an empty
field, `overvote` writes `*`, since the record does not name the candidates marked, `Write-in`
writes the index of the aggregate write-in, and a candidate's name writes its index.  Each row of
the record writes one ballot line, with the row's `ballotID` as its identifier unless --no-ids is
given.

The converter refuses, with a message on standard error and exit status 1, a record or a report
that the file cannot represent: a record without ranking columns `rank1` to `rankk` for 1 <= k <=
63, a row of the wrong length, a ranking that names a candidate absent from the report, more than
63 candidates, a name or an identifier outside its alphabet or length, a duplicate candidate name,
an order that is not a permutation, more than 2^32 - 1 ballots, or a file that is not UTF-8.

  convert.py CVR [--report XML] [--contest ID] [--order I ...] [--no-ids] [--out FILE]
"""

import argparse
import csv
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import reports  # noqa: E402

SKIPPED, OVERVOTE, WRITE_IN = "skipped", "overvote", "Write-in"
MAX_POSITIONS = 63
MAX_CANDIDATES = 63
MAX_BALLOTS = (1 << 32) - 1
IDENTIFIER = re.compile(rb"[A-Za-z0-9._:-]{1,64}")
NAME = re.compile(rb"[\x20-\x7e\x80-\xff]{1,255}")


class ConversionError(Exception):
    pass


def read_cvr(path):
    """The header and the rows of a CVR file, each row as long as the header."""
    try:
        with open(path, newline="", encoding="utf-8") as f:
            reader = csv.reader(f)
            header = next(reader, None)
            if header is None:
                raise ConversionError(f"{path}: the file is empty")
            rows = list(reader)
    except UnicodeDecodeError as e:
        raise ConversionError(f"{path}: not UTF-8: {e}") from e
    for row_number, row in enumerate(rows, 2):
        if len(row) != len(header):
            raise ConversionError(f"{path}: row {row_number}: {len(row)} fields against the header's "
                                  f"{len(header)}")
    return header, rows


def rank_columns(header):
    ranks = [i for i, h in enumerate(header) if re.fullmatch(r"rank\d+", h)]
    k = len(ranks)
    if not 1 <= k <= MAX_POSITIONS:
        raise ConversionError(f"{k} ranking columns, outside 1 to {MAX_POSITIONS}")
    if [header[i] for i in ranks] != [f"rank{p}" for p in range(1, k + 1)]:
        columns = ", ".join(header[i] for i in ranks)
        raise ConversionError(f"the ranking columns {columns} are not rank1 to rank{k}")
    return ranks


def names_from_cvr(rows, ranks):
    marks = {row[i] for row in rows for i in ranks} - {SKIPPED, OVERVOTE, WRITE_IN}
    return sorted(marks, key=lambda name: name.encode())


def convert(header, rows, names, contest, order=None, ids=True):
    """The canonical file's bytes for the header and rows of `read_cvr` and the listed candidates' names."""
    ranks = rank_columns(header)
    k = len(ranks)
    if not IDENTIFIER.fullmatch(contest.encode()):
        raise ConversionError(f"contest identifier {contest!r} is outside the identifier alphabet or length")
    candidates = [(b"listed", name) for name in names] + [(b"aggregate-writein", WRITE_IN)]
    n = len(candidates)
    if n > MAX_CANDIDATES:
        raise ConversionError(f"{n} candidates, above {MAX_CANDIDATES}")
    index = {}
    for i, (_, name) in enumerate(candidates, 1):
        if name in index or name in (SKIPPED, OVERVOTE):
            raise ConversionError(f"candidate name {name!r} repeats or equals a ranking mark")
        if not NAME.fullmatch(name.encode()):
            raise ConversionError(f"candidate name {name!r} is outside the name alphabet or length")
        index[name] = i
    order = list(range(1, n + 1)) if order is None else order
    if sorted(order) != list(range(1, n + 1)):
        raise ConversionError(f"order {order} is not a permutation of 1 to {n}")
    if len(rows) > MAX_BALLOTS:
        raise ConversionError(f"{len(rows)} ballots, above {MAX_BALLOTS}")
    if ids:
        if "ballotID" not in header:
            raise ConversionError("the record has no ballotID column")
        id_column = header.index("ballotID")
    fields = {SKIPPED: b"", OVERVOTE: b"*"}
    fields.update((name, b"%d" % i) for name, i in index.items())
    lines = [b"rcv-ballots 1", b"contest " + contest.encode(), b"positions %d" % k, b"candidates %d" % n]
    lines += [b"candidate %d %s %s" % (i, kind, name.encode()) for i, (kind, name) in enumerate(candidates, 1)]
    lines.append(b"order " + b" ".join(b"%d" % i for i in order))
    lines.append(b"ballots %d" % len(rows))
    for row_number, row in enumerate(rows, 2):
        line = []
        if ids:
            identifier = row[id_column].encode()
            if not IDENTIFIER.fullmatch(identifier):
                raise ConversionError(f"row {row_number}: ballotID {row[id_column]!r} is outside the "
                                      "identifier alphabet or length")
            line.append(identifier)
        for i in ranks:
            if row[i] not in fields:
                raise ConversionError(f"row {row_number}: ranking {row[i]!r} names no candidate of the contest")
            line.append(fields[row[i]])
        lines.append(b",".join(line))
    return b"".join(line + b"\n" for line in lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("cvr", help="D. Otis's CSV cast vote record")
    ap.add_argument("--report", help="the County's RcvDetailedReport.xml, whose candidates the file takes in order")
    ap.add_argument("--contest", help="contest identifier (default: the CVR file's name without extension)")
    ap.add_argument("--order", type=int, nargs="+", help="tie-break order, candidate indices earliest first")
    ap.add_argument("--no-ids", action="store_true", help="omit the identifier field of each ballot line")
    ap.add_argument("--out", help="output file (default: standard output)")
    args = ap.parse_args()
    try:
        header, rows = read_cvr(args.cvr)
        if args.report:
            names = reports.parse(args.report)["candidates"]
        else:
            names = names_from_cvr(rows, rank_columns(header))
        contest = args.contest if args.contest is not None else Path(args.cvr).stem
        data = convert(header, rows, names, contest, args.order, not args.no_ids)
    except (OSError, ConversionError, reports.ReportError, ET.ParseError) as e:
        print(f"convert.py: {e}", file=sys.stderr)
        return 1
    if args.out:
        Path(args.out).write_bytes(data)
    else:
        sys.stdout.buffer.write(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
