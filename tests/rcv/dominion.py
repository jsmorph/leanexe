# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Converts one contest of a Dominion Democracy Suite cast vote record export to the canonical ballot file.

The export is the JSON form of Democracy Suite's CVR export: a directory, or a zip archive of one,
that holds the manifests and either `CvrExport.json` or files `CvrExport_N.json`.  The output
follows the grammar and the tables of `Demos/Rcv/requirements.md`.

The contest is the ContestManifest entry whose Id is CONTEST.  Its NumOfRanks gives the positions.
The candidates are the contest's CandidateManifest entries in the manifest's order, named by their
Description, with the kind `listed` for the type Regular, `named-writein` for QualifiedWriteIn, and
`aggregate-writein` for WriteIn or Writein.  The tie-break order is the one given with --order, or
else 1 to n.  The contest identifier is the one given with --contest, or else the export's file name
without its extension, a hyphen, and CONTEST.

The CvrExport files are read in increasing order of N, and each session in its file's order.  Of a
session's Original and Modified elements, the converter reads the one whose IsCurrent is true.  Each
card of that element that lists the contest gives one ballot line, unless the contest carries the
outstack condition that the OutstackConditionManifest describes as InvalidContest.  An element
without Cards is read as a single card.  A mark whose IsAmbiguous is true is passed over, and every
other mark of the contest marks its candidate at the position of its Rank, so that a position with
two or more marks is an overvote that names its candidates.  The converter does not read IsVote,
whose meaning differs between versions.  The identifier of a line is the session's TabulatorId,
BatchId, and RecordId joined by hyphens, unless --no-ids is given.

The converter refuses, with a message on standard error and exit status 1, an export that the file
cannot represent or that departs from the format: a missing manifest or CVR file, both
`CvrExport.json` and `CvrExport_N.json`, a file that is not JSON in UTF-8 with or without a byte
order mark, an entry or a session without a field of the format or with a field of the wrong type,
a contest absent from the manifest, VoteFor other than 1, NumOfRanks outside 1 to 63, no candidate
or more than 63, a candidate type other than the four above, a name or an identifier outside its
alphabet or length, an order that is not a permutation, a session without exactly one current
element, a contest on two cards of one session, a mark whose rank lies outside 1 to NumOfRanks or
whose candidate is not the contest's, a candidate marked twice at one rank, two sessions with the
same TabulatorId, BatchId, and RecordId, or more than 2^32 - 1 ballots.

  dominion.py EXPORT        lists the ranked contests: Id, NumOfRanks, VoteFor, and Description
  dominion.py EXPORT CONTEST [--contest ID] [--order I ...] [--no-ids] [--out FILE]
"""

import argparse
import json
import re
import sys
import zipfile
import zlib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from convert import IDENTIFIER, MAX_BALLOTS, MAX_CANDIDATES, MAX_POSITIONS, NAME, ConversionError  # noqa: E402

KINDS = {"Regular": b"listed", "QualifiedWriteIn": b"named-writein", "WriteIn": b"aggregate-writein",
         "Writein": b"aggregate-writein"}
INVALID_CONTEST = "InvalidContest"
CVR_FILE = re.compile(r"CvrExport(?:_(\d+))?\.json")
WHITESPACE = " \t\n\r"
DECODER = json.JSONDecoder()


class Export:
    """The files of an export, a directory or a zip archive, by their names in the directory of its manifests."""

    def __init__(self, path):
        self.path = Path(path)
        if self.path.is_dir():
            files = {p.relative_to(self.path).as_posix(): p for p in self.path.rglob("*") if p.is_file()}
            names, self._read = list(files), lambda name: files[name].read_bytes()
        else:
            try:
                archive = zipfile.ZipFile(self.path)
            except (OSError, zipfile.BadZipFile) as e:
                raise ConversionError(f"{self.path}: neither a directory nor a zip archive: {e}") from e
            names, self._read = [n for n in archive.namelist() if not n.endswith("/")], archive.read
        homes = {n.rpartition("/")[0] for n in names if n.rpartition("/")[2] == "ContestManifest.json"}
        if len(homes) != 1:
            raise ConversionError(f"{self.path}: {len(homes)} copies of ContestManifest.json")
        home = homes.pop()
        self.prefix = home + "/" if home else ""
        self.names = {n[len(self.prefix):] for n in names
                      if n.startswith(self.prefix) and "/" not in n[len(self.prefix):]}

    def text(self, name):
        if name not in self.names:
            raise ConversionError(f"{self.path}: no {name}")
        try:
            return self._read(self.prefix + name).decode("utf-8-sig")
        except (OSError, zipfile.BadZipFile, zlib.error) as e:
            raise ConversionError(f"{self.path}: {name}: {e}") from e
        except UnicodeDecodeError as e:
            raise ConversionError(f"{self.path}: {name}: not UTF-8: {e}") from e

    def manifest(self, name):
        """The List of a manifest."""
        try:
            data = json.loads(self.text(name))
        except json.JSONDecodeError as e:
            raise ConversionError(f"{self.path}: {name}: {e}") from e
        return field(data, "List", list, name)

    def cvr_files(self):
        """The CvrExport files, CvrExport.json alone or each CvrExport_N.json in increasing order of N."""
        found = sorted((int(m[1]) if m[1] else -1, n) for n in self.names if (m := CVR_FILE.fullmatch(n)))
        if not found:
            raise ConversionError(f"{self.path}: no CvrExport.json or CvrExport_N.json")
        if found[0][0] == -1 and len(found) > 1:
            raise ConversionError(f"{self.path}: both CvrExport.json and CvrExport_N.json")
        return [n for _, n in found]


def field(obj, key, kind, where):
    """obj[key], which must have the type `kind`, where an int is not a bool."""
    if not isinstance(obj, dict) or key not in obj:
        raise ConversionError(f"{where}: no {key}")
    value = obj[key]
    if (kind is int and type(value) is not int) or not isinstance(value, kind):
        raise ConversionError(f"{where}: {key} is {value!r}, not {kind.__name__}")
    return value


def skip(text, pos):
    while pos < len(text) and text[pos] in WHITESPACE:
        pos += 1
    return pos


def punctuation(text, pos, allowed, name):
    """The position after the whitespace and the character of `allowed` at `pos`, and that character."""
    pos = skip(text, pos)
    if pos == len(text) or text[pos] not in allowed:
        raise ConversionError(f"{name}: expected one of {allowed!r} at character {pos}")
    return pos + 1, text[pos]


def value(text, pos, name):
    try:
        return DECODER.raw_decode(text, skip(text, pos))
    except json.JSONDecodeError as e:
        raise ConversionError(f"{name}: {e}") from e


def sessions(text, name):
    """The sessions of a CvrExport file's top-level object, each parsed when it is reached."""
    pos, _ = punctuation(text, 0, "{", name)
    found = False
    while True:
        key, pos = value(text, pos, name)
        if not isinstance(key, str):
            raise ConversionError(f"{name}: a key of the top-level object is {key!r}")
        pos, _ = punctuation(text, pos, ":", name)
        if key != "Sessions":
            _, pos = value(text, pos, name)
        elif found:
            raise ConversionError(f"{name}: two Sessions members")
        else:
            found = True
            pos, _ = punctuation(text, pos, "[", name)
            pos = skip(text, pos)
            if pos < len(text) and text[pos] == "]":
                pos += 1
            else:
                while True:
                    session, pos = value(text, pos, name)
                    yield session
                    pos, char = punctuation(text, pos, ",]", name)
                    if char == "]":
                        break
        pos, char = punctuation(text, pos, ",}", name)
        if char == "}":
            break
    if skip(text, pos) != len(text):
        raise ConversionError(f"{name}: data after the top-level object at character {skip(text, pos)}")
    if not found:
        raise ConversionError(f"{name}: no Sessions")


def ranked_contests(export):
    """(Id, NumOfRanks, VoteFor, Description) of each contest with rankings."""
    rows = []
    for entry in export.manifest("ContestManifest.json"):
        row = tuple(field(entry, key, kind, "ContestManifest.json")
                    for key, kind in (("Id", int), ("NumOfRanks", int), ("VoteFor", int), ("Description", str)))
        if row[1] > 0:
            rows.append(row)
    return rows


def contest_entry(export, contest_id):
    entries = [e for e in export.manifest("ContestManifest.json")
               if field(e, "Id", int, "ContestManifest.json") == contest_id]
    if len(entries) != 1:
        raise ConversionError(f"{len(entries)} entries of ContestManifest.json have the Id {contest_id}")
    where = f"ContestManifest.json, contest {contest_id}"
    if field(entries[0], "VoteFor", int, where) != 1:
        raise ConversionError(f"{where}: VoteFor {entries[0]['VoteFor']}, and the file holds single-winner contests")
    k = field(entries[0], "NumOfRanks", int, where)
    if not 1 <= k <= MAX_POSITIONS:
        raise ConversionError(f"{where}: NumOfRanks {k}, outside 1 to {MAX_POSITIONS}")
    return k


def candidates(export, contest_id):
    """[(Id, kind, name)] of the contest's candidates in the manifest's order."""
    found = []
    for entry in export.manifest("CandidateManifest.json"):
        if field(entry, "ContestId", int, "CandidateManifest.json") != contest_id:
            continue
        ident = field(entry, "Id", int, "CandidateManifest.json")
        where = f"CandidateManifest.json, candidate {ident}"
        kind = KINDS.get(field(entry, "Type", str, where))
        if kind is None:
            raise ConversionError(f"{where}: the type {entry['Type']!r} is none of {', '.join(KINDS)}")
        name = field(entry, "Description", str, where).encode()
        if not NAME.fullmatch(name):
            raise ConversionError(f"{where}: the name {entry['Description']!r} is outside the name alphabet or length")
        found.append((ident, kind, name))
    if not 1 <= len(found) <= MAX_CANDIDATES:
        raise ConversionError(f"contest {contest_id}: {len(found)} candidates, outside 1 to {MAX_CANDIDATES}")
    if len({ident for ident, _, _ in found}) != len(found):
        raise ConversionError(f"contest {contest_id}: a candidate Id repeats in CandidateManifest.json")
    return found


def invalid_conditions(export):
    return {field(e, "Id", int, "OutstackConditionManifest.json")
            for e in export.manifest("OutstackConditionManifest.json")
            if field(e, "Description", str, "OutstackConditionManifest.json") == INVALID_CONTEST}


def current(session, where):
    """The element of the session, Original or Modified, whose IsCurrent is true."""
    elements = [field(session, "Original", dict, where)]
    if "Modified" in session:
        elements.append(field(session, "Modified", dict, where))
    marked = [e for e in elements if field(e, "IsCurrent", bool, where)]
    if len(marked) != 1:
        raise ConversionError(f"{where}: {len(marked)} of the session's elements have IsCurrent true")
    return marked[0]


def ballot(session, contest_id, k, index, invalid, where):
    """The fields of the session's line, or None when no card carries the contest or the contest is invalid."""
    element = current(session, where)
    cards = field(element, "Cards", list, where) if "Cards" in element else [element]
    found = [c for card in cards for c in field(card, "Contests", list, where)
             if field(c, "Id", int, where) == contest_id]
    if not found:
        return None
    if len(found) > 1:
        raise ConversionError(f"{where}: {len(found)} cards list contest {contest_id}")
    contest = found[0]
    if invalid & set(field(contest, "OutstackConditionIds", list, where)):
        return None
    positions = [set() for _ in range(k)]
    for mark in field(contest, "Marks", list, where):
        if field(mark, "IsAmbiguous", bool, where):
            continue
        rank, candidate = field(mark, "Rank", int, where), field(mark, "CandidateId", int, where)
        if not 1 <= rank <= k:
            raise ConversionError(f"{where}: a mark has rank {rank}, outside 1 to {k}")
        if candidate not in index:
            raise ConversionError(f"{where}: a mark names candidate {candidate}, not a candidate of contest "
                                  f"{contest_id}")
        if index[candidate] in positions[rank - 1]:
            raise ConversionError(f"{where}: candidate {candidate} is marked twice at rank {rank}")
        positions[rank - 1].add(index[candidate])
    return [b"|".join(b"%d" % i for i in sorted(p)) for p in positions]


def convert(export, contest_id, contest, order=None, ids=True):
    """The canonical file's bytes for contest `contest_id` of the Export `export`, with the identifier `contest`."""
    if not IDENTIFIER.fullmatch(contest.encode()):
        raise ConversionError(f"contest identifier {contest!r} is outside the identifier alphabet or length")
    k = contest_entry(export, contest_id)
    listed = candidates(export, contest_id)
    n = len(listed)
    order = list(range(1, n + 1)) if order is None else order
    if sorted(order) != list(range(1, n + 1)):
        raise ConversionError(f"order {order} is not a permutation of 1 to {n}")
    index = {ident: i for i, (ident, _, _) in enumerate(listed, 1)}
    invalid = invalid_conditions(export)
    seen = set()
    lines = []
    for name in export.cvr_files():
        for number, session in enumerate(sessions(export.text(name), name), 1):
            where = f"{name}, session {number}"
            key = tuple(field(session, f, int, where) for f in ("TabulatorId", "BatchId", "RecordId"))
            if key in seen:
                raise ConversionError(f"{where}: TabulatorId, BatchId, and RecordId {key} repeat an earlier session")
            seen.add(key)
            fields = ballot(session, contest_id, k, index, invalid, where)
            if fields is not None:
                lines.append(b",".join(([b"%d-%d-%d" % key] if ids else []) + fields))
    if len(lines) > MAX_BALLOTS:
        raise ConversionError(f"{len(lines)} ballots, above {MAX_BALLOTS}")
    header = [b"rcv-ballots 1", b"contest " + contest.encode(), b"positions %d" % k, b"candidates %d" % n]
    header += [b"candidate %d %s %s" % (i, kind, name) for i, (_, kind, name) in enumerate(listed, 1)]
    header += [b"order " + b" ".join(b"%d" % i for i in order), b"ballots %d" % len(lines)]
    return b"".join(line + b"\n" for line in header + lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("export", help="the export's directory or zip archive")
    ap.add_argument("contest_id", nargs="?", type=int, metavar="CONTEST",
                    help="the contest's Id in ContestManifest.json (omitted: list the ranked contests)")
    ap.add_argument("--contest", help="contest identifier (default: the export's name without extension, '-', CONTEST)")
    ap.add_argument("--order", type=int, nargs="+", help="tie-break order, candidate indices earliest first")
    ap.add_argument("--no-ids", action="store_true", help="omit the identifier field of each ballot line")
    ap.add_argument("--out", help="output file (default: standard output)")
    args = ap.parse_args()
    try:
        export = Export(args.export)
        if args.contest_id is None:
            for row in ranked_contests(export):
                print("\t".join(str(x) for x in row))
            return 0
        contest = args.contest if args.contest is not None else f"{Path(args.export).stem}-{args.contest_id}"
        data = convert(export, args.contest_id, contest, args.order, not args.no_ids)
    except ConversionError as e:
        print(f"dominion.py: {e}", file=sys.stderr)
        return 1
    if args.out:
        Path(args.out).write_bytes(data)
    else:
        sys.stdout.buffer.write(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
