# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes the canonical ballot file of a contest of the Maine corpus from the Secretary of State's
cast vote record spreadsheets.

The contest is a key of `tests/rcv/maine/manifest.json`, such as `2026-06-09/REP-SR58`, and the
script reads the contest's spreadsheets from the data directory, `tmp/rcv-maine-data` by default, in
the manifest's order, with Python's zip and XML modules.  Each worksheet's first row is its header:
the first column holds the Cast Vote Record number, and the ranking columns are those whose header
holds `Choice`, in their order.  Every worksheet of the contest must have the same ranking columns,
and their number is the file's `positions`.

The candidates are those of the contest's summary report, in the report's order, as
`tests/rcv/maine/recount.py` transcribes them, each of kind `listed`.  An `aggregate-writein`
candidate `Write-in` follows when a spreadsheet ranks `Write-in`, then a `named-writein` candidate
for each `--named-writein NAME`, a declared write-in whom adjudicated records name, and then an
`excluded` candidate for each `--excluded NAME`, from the Secretary of State's notices of
withdrawal, death, or disqualification.  The 2024 records rank the declared write-in candidate
Diane Merenda only inside `Write-in`, which the kind `aggregate-writein` does not admit, so for that
contest the script writes `Write-in` as `aggregate-writein` only with `--practice`, which names the
comparison with the Secretary of State's count, and refuses the contest otherwise.

Each row after the header gives one ballot line.  A ranking cell holding `undervote`, or a missing
cell, gives an empty field, where a cell without a value or with an empty value counts as missing.
`overvote` gives `*`, since the records do not name the candidates marked.  A candidate's name with
its surrounding spaces removed gives the candidate's index, and `Write-in` gives the aggregate's.  The
line's identifier is the spreadsheet's manifest label, a colon, and its Cast Vote Record number
without a trailing `.0`, such as `export-1:15876`.  The contest identifier is the manifest key with
`/` replaced by `:`, and the order is `--order` or 1 to `n`.

The script refuses, with a message on standard error and exit status 1, a ranking that names no
candidate, spreadsheets whose ranking columns differ, more than 63 candidates or positions, a
candidate name or an identifier outside the file's alphabet or length, a repeated candidate name,
an order that is not a permutation, a contest without spreadsheets, and the 2024 contest without
`--practice`.

  convert.py KEY [--data DIR] [--order I ...] [--named-writein NAME ...] [--excluded NAME ...]
             [--practice] [--out FILE]
"""

import argparse
import json
import re
import sys
import zipfile
from pathlib import Path
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import recount  # noqa: E402

NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
RNS = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"
PKG = "{http://schemas.openxmlformats.org/package/2006/relationships}"
WRITEIN = "Write-in"
MAX_INDEX = 63
MAX_BALLOTS = (1 << 32) - 1
IDENTIFIER = re.compile(rb"[A-Za-z0-9_.:-]{1,64}")
DECLARED_IN_AGGREGATE = {"2024-11-05/CG2"}


class Refused(Exception):
    pass


def column(ref):
    """The zero-based column of a cell reference such as `D12`."""
    m = re.match(r"[A-Z]+", ref or "")
    if not m:
        raise Refused(f"cell reference {ref!r} without a column")
    n = 0
    for ch in m.group(0):
        n = n * 26 + ord(ch) - 64
    return n - 1


def text(element):
    return "".join(t.text or "" for t in element.iter(NS + "t"))


def cell_value(c, shared):
    """The value of a cell element as a string, or None when the cell holds no value."""
    kind = c.get("t")
    if kind == "inlineStr":
        inline = c.find(NS + "is")
        return None if inline is None else text(inline)
    v = c.find(NS + "v")
    if v is None or v.text is None:
        return None
    if kind == "s":
        return shared[int(v.text)]
    return v.text


def worksheets(path):
    """The rows of each worksheet of an xlsx file, in the workbook's order, each row a dict from
    zero-based column to the string value of each cell that holds one."""
    with zipfile.ZipFile(path) as z:
        names = set(z.namelist())
        shared = []
        if "xl/sharedStrings.xml" in names:
            shared = [text(si) for si in ET.fromstring(z.read("xl/sharedStrings.xml")).iter(NS + "si")]
        rels = {r.get("Id"): r.get("Target")
                for r in ET.fromstring(z.read("xl/_rels/workbook.xml.rels")).iter(PKG + "Relationship")}
        for sheet in ET.fromstring(z.read("xl/workbook.xml")).iter(NS + "sheet"):
            target = rels[sheet.get(RNS + "id")]
            target = target.lstrip("/") if target.startswith("/") else "xl/" + target
            rows = []
            for row in ET.fromstring(z.read(target)).iter(NS + "row"):
                cells = {}
                for c in row.iter(NS + "c"):
                    value = cell_value(c, shared)
                    if value is not None and value != "":
                        cells[column(c.get("r"))] = value
                rows.append(cells)
            yield rows


def name_ok(name):
    data = name.encode()
    return 1 <= len(data) <= 255 and all(0x20 <= b <= 0x7E or b >= 0x80 for b in data)


def field(value, index):
    """The field of a ranking cell's value, or None for the cell absent."""
    if value is None or value == "undervote":
        return b""
    if value == "overvote":
        return b"*"
    i = index.get(value.strip(" "))
    if i is None:
        raise Refused(f"the ranking {value!r} names no candidate")
    return b"%d" % i


def convert(manifest, key, data, order=None, named=(), excluded=(), practice=False):
    """The canonical file's bytes of the contest `key`."""
    contest = next((c for c in manifest["contests"] if c["key"] == key), None)
    if contest is None or not contest.get("cvr"):
        raise Refused(f"{key}: no contest with spreadsheets in the manifest")
    sheets = []
    ranking = None
    writein = False
    for f in contest["cvr"]:
        for rows in worksheets(data / f["path"]):
            if not rows:
                raise Refused(f"{f['path']}: a worksheet without a header")
            header = rows[0]
            columns = [i for i in sorted(header) if "Choice" in header[i]]
            headings = [header[i] for i in columns]
            if ranking is None:
                ranking = headings
            elif headings != ranking:
                raise Refused(f"{f['path']}: ranking columns {headings} differ from {ranking}")
            writein = writein or any(r.get(i, "").strip(" ") == WRITEIN for r in rows[1:] for i in columns)
            sheets.append((f, columns, rows[1:]))
    k = len(ranking)
    if not 1 <= k <= MAX_INDEX:
        raise Refused(f"{key}: {k} ranking columns, outside 1 to {MAX_INDEX}")
    if writein and key in DECLARED_IN_AGGREGATE and not practice:
        raise Refused(f"{key}: `Write-in` holds a declared write-in candidate's rankings; "
                      "convert with --practice for the comparison with the Secretary of State's count")
    candidates = [(b"listed", name) for name in recount.REPORTS[key][0]]
    if writein:
        candidates.append((b"aggregate-writein", WRITEIN))
    candidates += [(b"named-writein", name) for name in named]
    candidates += [(b"excluded", name) for name in excluded]
    n = len(candidates)
    if n > MAX_INDEX:
        raise Refused(f"{key}: {n} candidates, more than {MAX_INDEX}")
    names = [name for _, name in candidates]
    for name in names:
        if not name_ok(name):
            raise Refused(f"{key}: the name {name!r} is outside the file's alphabet or length")
    if len(set(names)) != n:
        raise Refused(f"{key}: a repeated candidate name")
    order = list(range(1, n + 1)) if order is None else order
    if sorted(order) != list(range(1, n + 1)):
        raise Refused(f"{key}: the order {order} is not a permutation of 1 to {n}")
    index = {name: i for i, name in enumerate(names, 1)}
    lines = []
    for f, columns, rows in sheets:
        for r in rows:
            number = r.get(0, "")
            number = number[:-2] if number.endswith(".0") else number
            ident = f"{f['label']}:{number}".encode()
            if not IDENTIFIER.fullmatch(ident):
                raise Refused(f"{f['path']}: the identifier {ident!r} is outside the file's alphabet or length")
            try:
                fields = [field(r.get(i), index) for i in columns]
            except Refused as e:
                raise Refused(f"{f['path']}: Cast Vote Record {number}: {e}") from None
            lines.append(b",".join([ident] + fields))
    if len(lines) > MAX_BALLOTS:
        raise Refused(f"{key}: {len(lines)} ballots, more than {MAX_BALLOTS}")
    head = [b"rcv-ballots 1", b"contest " + key.replace("/", ":").encode(), b"positions %d" % k,
            b"candidates %d" % n]
    head += [b"candidate %d %s %s" % (i, kind, name.encode()) for i, (kind, name) in enumerate(candidates, 1)]
    head += [b"order " + b" ".join(b"%d" % i for i in order), b"ballots %d" % len(lines)]
    return b"".join(line + b"\n" for line in head + lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("key", help="the contest's manifest key, such as 2026-06-09/REP-SR58")
    ap.add_argument("--data", default="tmp/rcv-maine-data", help="data directory (default tmp/rcv-maine-data)")
    ap.add_argument("--order", type=int, nargs="+", help="the tie-break order (default 1 to n)")
    ap.add_argument("--named-writein", action="append", default=[], metavar="NAME",
                    help="a declared write-in candidate whom adjudicated records name")
    ap.add_argument("--excluded", action="append", default=[], metavar="NAME",
                    help="an excluded candidate from the Secretary of State's notices")
    ap.add_argument("--practice", action="store_true",
                    help="write a declared write-in's rankings inside Write-in as the aggregate write-in")
    ap.add_argument("--out", help="output file (default standard output)")
    args = ap.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    try:
        data = convert(manifest, args.key, Path(args.data), args.order, args.named_writein,
                       args.excluded, args.practice)
    except Refused as e:
        print(e, file=sys.stderr)
        return 1
    if args.out:
        Path(args.out).write_bytes(data)
    else:
        sys.stdout.buffer.write(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
