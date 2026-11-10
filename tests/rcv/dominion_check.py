# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Tests the Dominion converter on synthetic exports, on Alaska's published exports, and with planted errors.

The synthetic exports, written as zip archives and a directory into SCRATCH over any files of the
same names, test the reading of sessions, cards, current elements, marks, and files against output
stated by hand, and test each refusal of `dominion.py` by its exit status and message.

The published contests are those of the `dominion` section of `manifest.json`, whose files the
script reads from DATA after checking their sizes and SHA-256 digests.  For each contest it runs:

  round trip  the reference reads the converted file back to the candidates of the manifest and to
              the identifiers and marks of the export's sessions, read here without the converter,
              and its writer reproduces the file
  county      the reference's county count of the converted file has the report's continuing
              candidates, eliminations, and winner in every round, and the script prints each
              figure that differs from the report's
  Alaska      after the ballot rules of 6 AAC 25.072 and AS 15.15.350(e)(2), every figure of every
              round of the county count equals the report's

The report's categories map as in Alameda County's reports: Blanks is `blank` plus `uncounted`,
Overvotes is `overvote`, and Exhausted is `exhausted`.  Each planted error is a copy of
`dominion.py` with one change, which must fail the Alaska check of the contests predicted for it.
With --fetch the script first downloads each missing or mismatched file of the section, one
request at a time with a two-second pause.  The script writes each converted contest and the
reference's county report under DATA/canonical, prints one line per contest and per planted error
and each failing check on standard error, and exits with status 1 if a check fails, a planted error
passes a predicted check, or a file is missing or mismatched.

  dominion_check.py [--data DIR] [--scratch DIR] [--fetch]
"""

import argparse
import csv
import hashlib
import io
import json
import re
import shutil
import ssl
import subprocess
import sys
import time
import types
import urllib.request
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dominion  # noqa: E402
import reference  # noqa: E402

USER_AGENT = "leanexe tests/rcv/dominion_check.py (Python urllib)"
PAUSE = 2.0
CATEGORIES = ("blanks", "overvotes", "exhausted")
LOAD_LIMIT = 1 << 26

# The figures of the Division's RCV detailed report of 2024-11-30 for the U.S. Representative contest
# of 2024-11-05, RCV-USRep.pdf, which the Division publishes only as a PDF.
USREP_2024 = [
    {"tallies": {"Begich, Nick": 159777, "Hafner, Eric": 3558, "Howe, John Wayne": 13210,
                 "Peltola, Mary S.": 152948}, "blanks": 5788, "exhausted": 0, "overvotes": 572,
     "eliminated": ["Hafner, Eric"]},
    {"tallies": {"Begich, Nick": 160044, "Hafner, Eric": 0, "Howe, John Wayne": 13871,
                 "Peltola, Mary S.": 154261}, "blanks": 5788, "exhausted": 1300, "overvotes": 589,
     "eliminated": ["Howe, John Wayne"]},
    {"tallies": {"Begich, Nick": 164861, "Hafner, Eric": 0, "Howe, John Wayne": 0,
                 "Peltola, Mary S.": 156985}, "blanks": 5788, "exhausted": 7595, "overvotes": 624,
     "eliminated": [], "elected": ["Begich, Nick"]},
]
FIGURES = {"alaska/24GENR/7": USREP_2024}

PLANTED = [
    ("ambiguous marks read as marks",
     'if field(mark, "IsAmbiguous", bool, where):',
     "if False:",
     ["alaska/22SSPG/69", "alaska/22GENR/3", "alaska/22GENR/4", "alaska/24GENR/7"]),
    ("the Original element read whatever IsCurrent says",
     'marked = [e for e in elements if field(e, "IsCurrent", bool, where)]',
     "marked = elements[:1]",
     ["alaska/22SSPG/69", "alaska/22GENR/3", "alaska/22GENR/4"]),
    ("invalid contests written",
     'if invalid & set(field(contest, "OutstackConditionIds", list, where)):',
     "if False:",
     ["alaska/24GENR/7"]),
    ("marks whose IsVote is false passed over",
     'if field(mark, "IsAmbiguous", bool, where):',
     'if field(mark, "IsAmbiguous", bool, where) or not mark["IsVote"]:',
     ["alaska/22SSPG/69", "alaska/22GENR/3", "alaska/22GENR/4"]),
]


# Synthetic exports

def mark(candidate, rank, ambiguous=False, vote=True):
    return {"CandidateId": candidate, "Rank": rank, "IsAmbiguous": ambiguous, "IsVote": vote,
            "OutstackConditionIds": []}


def contest(marks, ident=1, conditions=()):
    return {"Id": ident, "Marks": list(marks), "OutstackConditionIds": list(conditions)}


def element(contests, current=True, cards=True):
    if not cards:
        return {"IsCurrent": current, "Contests": contests}
    return {"IsCurrent": current, "Cards": [{"Id": 1, "Contests": contests}]}


def session(record, original, modified=None, tabulator=1, batch=1):
    s = {"TabulatorId": tabulator, "BatchId": batch, "RecordId": record, "Original": original}
    if modified is not None:
        s["Modified"] = modified
    return s


def base():
    """The files of the synthetic export `basic`, as JSON values."""
    candidates = [(11, "Able, Ann", 1, "Regular"), (12, "Baker, Bo", 1, "Regular"),
                  (13, "Cruz, Cy", 1, "QualifiedWriteIn"), (14, "Write-in", 1, "WriteIn"), (21, "Yes", 2, "Regular")]
    two_cards = element([])
    two_cards["Cards"] = [{"Id": 1, "Contests": [contest([mark(21, 1)], 2)]},
                          {"Id": 2, "Contests": [contest([mark(12, 3)])]}]
    first = [
        session(1, element([contest([mark(11, 1), mark(12, 2)])])),
        session(2, element([contest([mark(11, 1)])], current=False), element([contest([mark(12, 1)])])),
        session(3, element([contest([mark(11, 1)])]), element([contest([mark(13, 1)])], current=False)),
        session(4, element([contest([mark(11, 1, ambiguous=True, vote=False), mark(12, 2, vote=False)])])),
        session(5, element([contest([mark(11, 1), mark(12, 1), mark(14, 2)])])),
        session(6, element([contest([mark(13, 1), mark(14, 2), mark(11, 3)])])),
    ]
    second = [
        session(7, element([contest([mark(11, 1)], conditions=[7])])),
        session(8, element([contest([mark(21, 1)], 2)])),
        session(9, two_cards),
        session(10, element([contest([mark(11, 2)])], cards=False)),
        session(11, element([contest([])])),
        session(1, element([contest([mark(11, 1), mark(12, 1), mark(13, 1), mark(14, 1)])]), tabulator=2, batch=3),
    ]
    return {
        "ContestManifest.json": {"Version": "5.17.18.1", "List": [
            {"Description": "Mayor", "Id": 1, "ExternalId": "", "VoteFor": 1, "NumOfRanks": 3},
            {"Description": "Measure A", "Id": 2, "ExternalId": "", "VoteFor": 1, "NumOfRanks": 0}]},
        "CandidateManifest.json": {"Version": "5.17.18.1", "List": [
            {"Description": name, "Id": ident, "ExternalId": "", "ContestId": c, "Type": kind}
            for ident, name, c, kind in candidates]},
        "OutstackConditionManifest.json": {"Version": "5.17.18.1", "List": [
            {"Description": "Ambiguous", "Id": 0}, {"Description": "Writein", "Id": 1},
            {"Description": "InvalidContest", "Id": 7}]},
        "CvrExport_9.json": {"Version": "5.17.18.1", "ElectionId": "Test", "Sessions": first},
        "CvrExport_10.json": {"Version": "5.17.18.1", "ElectionId": "Test", "Sessions": second},
    }


BASIC_HEADER = (b"positions 3\ncandidates 4\ncandidate 1 listed Able, Ann\ncandidate 2 listed Baker, Bo\n"
                b"candidate 3 named-writein Cruz, Cy\ncandidate 4 aggregate-writein Write-in\n")
BASIC_LINES = [b"1-1-1,1,2,", b"1-1-2,2,,", b"1-1-3,1,,", b"1-1-4,,2,", b"1-1-5,1|2,4,", b"1-1-6,3,4,1",
               b"1-1-9,,,2", b"1-1-10,,1,", b"1-1-11,,,", b"2-3-1,1|2|3|4,,"]


def expected(contest_id, lines=BASIC_LINES, order=b"1 2 3 4", ids=True):
    body = [line if ids else line.split(b",", 1)[1] for line in lines]
    return (b"rcv-ballots 1\ncontest " + contest_id + b"\n" + BASIC_HEADER + b"order " + order +
            b"\nballots %d\n" % len(body) + b"".join(line + b"\n" for line in body))


def encoded(value):
    return value if isinstance(value, bytes) else json.dumps(value).encode()


def write_zip(path, files, prefix=""):
    with zipfile.ZipFile(path, "w") as z:
        for name, value in files.items():
            z.writestr(prefix + name, encoded(value))
    return path


def edited(change):
    files = base()
    change(files)
    return files


def sessions_of(files, name="CvrExport_9.json"):
    return files[name]["Sessions"]


def first_marks(files):
    return sessions_of(files)[0]["Original"]["Cards"][0]["Contests"][0]["Marks"]


MALFORMED = [
    ("no ContestManifest.json", lambda f: f.pop("ContestManifest.json"), [], "0 copies of ContestManifest.json"),
    ("two ContestManifest.json", lambda f: f.update({"other/ContestManifest.json": f["ContestManifest.json"]}),
     [], "2 copies of ContestManifest.json"),
    ("no CandidateManifest.json", lambda f: f.pop("CandidateManifest.json"), [], "no CandidateManifest.json"),
    ("no OutstackConditionManifest.json", lambda f: f.pop("OutstackConditionManifest.json"), [],
     "no OutstackConditionManifest.json"),
    ("no CVR file", lambda f: [f.pop("CvrExport_9.json"), f.pop("CvrExport_10.json")], [],
     "no CvrExport.json or CvrExport_N.json"),
    ("both CVR file forms", lambda f: f.update({"CvrExport.json": f["CvrExport_9.json"]}), [],
     "both CvrExport.json and CvrExport_N.json"),
    ("truncated JSON", lambda f: f.update({"CvrExport_10.json": encoded(f["CvrExport_10.json"])[:-40]}), [],
     "CvrExport_10.json: "),
    ("not UTF-8", lambda f: f.update(
        {"CvrExport_9.json": encoded(f["CvrExport_9.json"]).replace(b"Test", b"T\xffst")}), [], "not UTF-8"),
    ("data after the top-level object", lambda f: f.update(
        {"CvrExport_9.json": encoded(f["CvrExport_9.json"]) + b"{}"}), [], "data after the top-level object"),
    ("no Sessions", lambda f: f.update({"CvrExport_9.json": {"Version": "5.17.18.1"}}), [], "no Sessions"),
    ("two Sessions", lambda f: f.update({"CvrExport_9.json": b'{"Sessions": [], "Sessions": []}'}), [],
     "two Sessions members"),
    ("no List", lambda f: f.update({"ContestManifest.json": {"Version": "5.17.18.1"}}), [], "no List"),
    ("contest absent", lambda f: None, ["3"], "0 entries of ContestManifest.json have the Id 3"),
    ("VoteFor 2", lambda f: f["ContestManifest.json"]["List"][0].update(VoteFor=2), [], "VoteFor 2"),
    ("NumOfRanks 0", lambda f: None, ["2"], "NumOfRanks 0"),
    ("NumOfRanks 64", lambda f: f["ContestManifest.json"]["List"][0].update(NumOfRanks=64), [], "NumOfRanks 64"),
    ("candidate type NoPreference", lambda f: f["CandidateManifest.json"]["List"][1].update(Type="NoPreference"),
     [], "the type 'NoPreference'"),
    ("name with a tab", lambda f: f["CandidateManifest.json"]["List"][0].update(Description="Able,\tAnn"), [],
     "outside the name alphabet"),
    ("empty name", lambda f: f["CandidateManifest.json"]["List"][0].update(Description=""), [],
     "outside the name alphabet"),
    ("no candidate", lambda f: f["CandidateManifest.json"].update(List=[]), [], "0 candidates"),
    ("64 candidates", lambda f: f["CandidateManifest.json"]["List"].extend(
        {"Description": f"C{i}", "Id": 100 + i, "ExternalId": "", "ContestId": 1, "Type": "Regular"}
        for i in range(60)), [], "64 candidates"),
    ("repeated candidate Id", lambda f: f["CandidateManifest.json"]["List"][1].update(Id=11), [],
     "a candidate Id repeats"),
    ("session without Original", lambda f: sessions_of(f)[0].pop("Original"), [], "no Original"),
    ("no current element", lambda f: sessions_of(f)[0]["Original"].update(IsCurrent=False), [],
     "0 of the session's elements have IsCurrent true"),
    ("two current elements", lambda f: sessions_of(f)[1]["Original"].update(IsCurrent=True), [],
     "2 of the session's elements have IsCurrent true"),
    ("contest on two cards", lambda f: sessions_of(f)[0]["Original"]["Cards"].append(
        {"Id": 2, "Contests": [contest([])]}), [], "2 cards list contest 1"),
    ("rank 0", lambda f: first_marks(f).append(mark(13, 0)), [], "rank 0, outside 1 to 3"),
    ("rank 4", lambda f: first_marks(f).append(mark(13, 4)), [], "rank 4, outside 1 to 3"),
    ("candidate of another contest", lambda f: first_marks(f).append(mark(21, 3)), [], "names candidate 21"),
    ("candidate marked twice at one rank", lambda f: first_marks(f).append(mark(11, 1)), [],
     "candidate 11 is marked twice at rank 1"),
    ("repeated session", lambda f: sessions_of(f).append(sessions_of(f)[0]), [], "repeat an earlier session"),
    ("mark without IsAmbiguous", lambda f: first_marks(f)[0].pop("IsAmbiguous"), [], "no IsAmbiguous"),
    ("rank as text", lambda f: first_marks(f)[0].update(Rank="1"), [], "Rank is '1', not int"),
    ("RecordId as a Boolean", lambda f: sessions_of(f)[0].update(RecordId=True), [], "RecordId is True, not int"),
    ("IsCurrent as a number", lambda f: sessions_of(f)[0]["Original"].update(IsCurrent=1), [],
     "IsCurrent is 1, not bool"),
    ("order not a permutation", lambda f: None, ["1", "--order", "1", "1", "2", "3"], "is not a permutation"),
    ("contest identifier with a space", lambda f: None, ["1", "--contest", "a b"], "outside the identifier alphabet"),
]


def run(args):
    return subprocess.run([sys.executable, "-I", str(HERE / "dominion.py"), *args], capture_output=True)


def synthetic_checks(scratch):
    """Problems of the synthetic exports, by check name."""
    scratch.mkdir(parents=True, exist_ok=True)
    results = {}
    basic = write_zip(scratch / "basic.zip", base())
    nested = write_zip(scratch / "nested.zip", base(), "CVR_Export_20261103/")
    directory = scratch / "dir"
    for name, value in base().items():
        (directory / name).parent.mkdir(parents=True, exist_ok=True)
        (directory / name).write_bytes(encoded(value))
    single = base()
    single["CvrExport.json"] = b"\xef\xbb\xbf" + encoded(single.pop("CvrExport_9.json"))
    single.pop("CvrExport_10.json")
    bom = write_zip(scratch / "bom.zip", single)
    cases = [
        ("basic", [basic, "1"], expected(b"basic-1")),
        ("options", [basic, "1", "--no-ids", "--order", "2", "1", "3", "4", "--contest", "x:y"],
         expected(b"x:y", order=b"2 1 3 4", ids=False)),
        ("nested directory", [nested, "1"], expected(b"nested-1")),
        ("directory", [directory, "1"], expected(b"dir-1")),
        ("one CvrExport.json with a byte order mark", [bom, "1"], expected(b"bom-1", BASIC_LINES[:6])),
        ("listing", [basic], b"1\t3\t1\tMayor\n"),
    ]
    for name, args, want in cases:
        done = run([str(a) for a in args])
        results[f"synthetic {name}"] = ([] if done.returncode == 0 and done.stdout == want and not done.stderr
                                        else [f"status {done.returncode}, stderr {done.stderr!r}, output "
                                              f"{done.stdout!r}, expected {want!r}"])
    not_export = scratch / "not-an-export.txt"
    not_export.write_bytes(b"rcv-ballots 1\n")
    malformed = [(name, write_zip(scratch / f"malformed-{i}.zip", edited(change)), args, message)
                 for i, (name, change, args, message) in enumerate(MALFORMED)]
    malformed.append(("not an export", not_export, ["1"], "neither a directory nor a zip archive"))
    for name, path, args, message in malformed:
        done = run([str(path), *(args or ["1"])])
        ok = (done.returncode == 1 and not done.stdout and done.stderr.startswith(b"dominion.py: ")
              and message.encode() in done.stderr)
        results[f"malformed {name}"] = [] if ok else [f"status {done.returncode}, stderr {done.stderr!r}"]
    return results


# Published contests

def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while chunk := f.read(1 << 20):
            h.update(chunk)
    return path.stat().st_size, h.hexdigest()


def pinned(section):
    """Each pinned file of the section once: the documents, then each export and report."""
    entries = {e["path"]: e for e in section["documents"]}
    for c in section["contests"]:
        entries.setdefault(c["export"]["path"], c["export"])
        entries.setdefault(c["report"]["path"], c["report"])
    return list(entries.values())


def fetch(section, data):
    """Downloads each missing or mismatched file, and returns the failures."""
    context = ssl.create_default_context()
    failures = []
    for entry in pinned(section):
        target = data / entry["path"]
        if target.exists() and digest(target) == (entry["size"], entry["sha256"]):
            if entry.get("certificate"):
                context.load_verify_locations(cadata=target.read_bytes())
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        partial = target.with_name(target.name + ".part")
        request = urllib.request.Request(entry["url"], headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=300, context=context) as response, open(partial, "wb") as f:
                shutil.copyfileobj(response, f, 1 << 20)
        except OSError as e:
            failures.append(f"{entry['path']}: {entry['url']}: {e}")
            partial.unlink(missing_ok=True)
            time.sleep(PAUSE)
            continue
        time.sleep(PAUSE)
        received = digest(partial)
        if received != (entry["size"], entry["sha256"]):
            partial.replace(target.with_name(target.name + ".mismatch"))
            failures.append(f"{entry['path']}: expected size {entry['size']} sha256 {entry['sha256']}, "
                            f"received size {received[0]} sha256 {received[1]}")
            continue
        partial.replace(target)
        if entry.get("certificate"):
            context.load_verify_locations(cadata=target.read_bytes())
    return failures


def text_report(path):
    """The rounds of a Dominion RCV detailed report in its tab-separated UTF-16 text form."""
    rounds, eliminated, elected = {}, [], []
    for row in csv.reader(io.StringIO(path.read_bytes().decode("utf-16")), delimiter="\t"):
        if len(row) > 3 and re.fullmatch(r"Round \d+", row[1]) and row[2]:
            rnd = rounds.setdefault(int(row[1].split()[1]), {"tallies": {}})
            votes = int(row[3].replace(",", ""))
            if row[2] in ("Blanks", "Exhausted", "Overvotes"):
                rnd[row[2].lower()] = votes
            elif row[2] != "Remainder Points":
                rnd["tallies"][row[2]] = votes
        elif len(row) > 17 and (m := re.fullmatch(r"(.*) is eliminated because the candidate had the least "
                                                  r"amount of votes\.", row[17])):
            eliminated.append(m[1])
        elif len(row) > 17 and (m := re.fullmatch(r"(.*) is elected because .*", row[17])):
            elected.append(m[1])
    out = [rounds[r] for r in sorted(rounds)]
    for i, rnd in enumerate(out):
        rnd["eliminated"] = eliminated[i:i + 1]
    out[-1]["elected"] = elected
    return out


def independent_ballots(path, contest_id, k, index, invalid):
    """(identifier, position words) of each ballot of the contest, read from the sessions of the export's
    CVR files, which `json` parses whole below LOAD_LIMIT characters and the converter's parser above."""
    with zipfile.ZipFile(path) as z:
        names = [n for n in z.namelist() if re.fullmatch(r"CvrExport(_\d+)?\.json", n)]
        for name in sorted(names, key=lambda n: int(re.sub(r"\D", "", n) or -1)):
            text = z.read(name).decode("utf-8")
            whole = len(text) < LOAD_LIMIT
            for s in json.loads(text)["Sessions"] if whole else dominion.sessions(text, name):
                current = s["Modified"] if "Modified" in s and s["Modified"]["IsCurrent"] else s["Original"]
                for card in current.get("Cards", [current]):
                    for c in card["Contests"]:
                        if c["Id"] != contest_id or invalid & set(c["OutstackConditionIds"]):
                            continue
                        words = [0] * k
                        for m in c["Marks"]:
                            if not m["IsAmbiguous"]:
                                words[m["Rank"] - 1] |= 1 << (index[m["CandidateId"]] - 1)
                        yield f"{s['TabulatorId']}-{s['BatchId']}-{s['RecordId']}".encode(), tuple(words)


def round_trip(entry, path, data):
    contest = reference.read(data)
    if isinstance(contest, reference.Malformed):
        return [f"the file fails at line {contest.line} with the role {contest.role}"]
    export = dominion.Export(path)
    listed = dominion.candidates(export, entry["contest_id"])
    problems = []
    if contest.candidates != [(kind, name) for _, kind, name in listed]:
        problems.append("the candidates differ from the manifest's")
    k = dominion.contest_entry(export, entry["contest_id"])
    index = {ident: i for i, (ident, _, _) in enumerate(listed, 1)}
    ballots = iter(contest.ballots)
    for number, want in enumerate(independent_ballots(path, entry["contest_id"], k, index,
                                                      dominion.invalid_conditions(export)), 1):
        got = next(ballots, None)
        if want != got:
            problems.append(f"ballot {number} reads back as {got}, the export gives {want}")
            break
    else:
        if next(ballots, None) is not None:
            problems.append("the file holds more ballots than the export")
    if reference.write(contest) != data:
        problems.append("the reference's writer does not reproduce the file")
    return problems


def alaska_rules(words):
    """The ballot after 6 AAC 25.072, which disregards each later ranking of a candidate, and AS
    15.15.350(e)(2), which makes a ballot inactive at the second of two sequential skipped rankings,
    with whether each rule changed it."""
    out, earlier = [], 0
    for w in words:
        single = w and w != reference.UNNAMED and w & (w - 1) == 0
        out.append(0 if single and w & earlier else w)
        earlier |= w if single else 0
    duplicate = out != list(words)
    for p in range(1, len(out)):
        if out[p - 1] == out[p] == 0 and any(out[p + 1:]):
            return tuple(out[:p] + [0] * (len(out) - p)), duplicate, True
    return tuple(out), duplicate, False


def compare(contest, rounds, winner, official, exact):
    """Problems of the county count against the report: structure always, figures when `exact`."""
    names = {i: name.decode() for i, (_, name) in enumerate(contest.candidates, 1)}
    problems = [f"{len(rounds)} rounds, the report {len(official)}"] if len(rounds) != len(official) else []
    for rnd, pub in zip(rounds, official):
        ours = {names[i]: v for i, v in rnd.votes.items()}
        ours.update(blanks=rnd.inactive["blank"] + rnd.inactive["uncounted"], overvotes=rnd.inactive["overvote"],
                    exhausted=rnd.inactive["exhausted"])
        theirs = {name: v for name, v in pub["tallies"].items() if name in ours or v}
        theirs.update((k, pub[k]) for k in CATEGORIES)
        if set(theirs) != set(ours):
            problems.append(f"round {rnd.number}: candidates {sorted(set(ours) - set(CATEGORIES))}, the report "
                            f"{sorted(set(theirs) - set(CATEGORIES))}")
            continue
        if [names[i] for i in rnd.eliminated] != pub["eliminated"]:
            problems.append(f"round {rnd.number}: eliminates {[names[i] for i in rnd.eliminated]}, the report "
                            f"{pub['eliminated']}")
        if exact:
            problems += [f"round {rnd.number}: {k} {ours[k]} against {theirs[k]}"
                         for k in theirs if ours[k] != theirs[k]]
    if ([names[winner]] if winner else []) != official[-1].get("elected", []):
        problems.append(f"winner {names.get(winner)}, the report {official[-1].get('elected')}")
    return problems


def differences(contest, rounds, official):
    names = {i: name.decode() for i, (_, name) in enumerate(contest.candidates, 1)}
    out = []
    for rnd, pub in zip(rounds, official):
        ours = {names[i]: v for i, v in rnd.votes.items()}
        ours.update(blanks=rnd.inactive["blank"] + rnd.inactive["uncounted"], overvotes=rnd.inactive["overvote"],
                    exhausted=rnd.inactive["exhausted"])
        out += [f"r{rnd.number} {k} {ours[k] - pub['tallies'].get(k, pub.get(k)):+d}" for k in ours
                if ours[k] != pub["tallies"].get(k, pub.get(k))]
    return out


def official_rounds(entry, data):
    if entry["key"] in FIGURES:
        return FIGURES[entry["key"]]
    return text_report(data / entry["report"]["path"])


def alaska_check(entry, data_bytes, official):
    contest = reference.read(data_bytes)
    if isinstance(contest, reference.Malformed):
        return [f"the file fails at line {contest.line}"], 0
    rewritten = [(ident, alaska_rules(words)) for ident, words in contest.ballots]
    changed = [sum(rule[i] for _, rule in rewritten) for i in (1, 2)]
    contest.ballots = [(ident, rule[0]) for ident, rule in rewritten]
    return compare(contest, *reference.count(contest, "county"), official, exact=True), changed


def planted(old, new):
    source = (HERE / "dominion.py").read_text()
    if source.count(old) != 1:
        raise SystemExit(f"dominion_check.py: the planted change's text occurs {source.count(old)} times: {old!r}")
    module = types.ModuleType("planted_dominion")
    module.__file__ = str(HERE / "dominion.py")
    sys.modules[module.__name__] = module
    exec(compile(source.replace(old, new), module.__file__, "exec"), module.__dict__)
    return module


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data", default="tmp/rcv-dominion-data", help="data directory (default tmp/rcv-dominion-data)")
    ap.add_argument("--scratch", default="tmp/rcv-dominion-tests", help="directory for the synthetic exports")
    ap.add_argument("--fetch", action="store_true", help="download missing or mismatched files first")
    args = ap.parse_args()
    data = Path(args.data)
    section = json.loads((HERE / "manifest.json").read_text())["dominion"]
    failed = 0
    if args.fetch:
        for failure in fetch(section, data):
            print(failure, file=sys.stderr)
            failed += 1
    results = synthetic_checks(Path(args.scratch))
    for entry in pinned(section):
        path = data / entry["path"]
        if not path.exists() or digest(path) != (entry["size"], entry["sha256"]):
            results[f"file {entry['path']}"] = ["missing or mismatched; run with --fetch"]
    converted = {}
    for entry in section["contests"]:
        export, key = data / entry["export"]["path"], entry["key"]
        if f"file {entry['export']['path']}" in results or f"file {entry['report']['path']}" in results:
            continue
        try:
            converted[key] = dominion.convert(dominion.Export(export), entry["contest_id"], entry["identifier"])
        except dominion.ConversionError as e:
            results[f"convert {key}"] = [str(e)]
            continue
        out = data / "canonical"
        out.mkdir(exist_ok=True)
        (out / f"{entry['identifier']}.rcv").write_bytes(converted[key])
        (out / f"{entry['identifier']}.county").write_bytes(reference.report(converted[key], "county"))
        official = official_rounds(entry, data)
        contest = reference.read(converted[key])
        rounds, winner = reference.count(contest, "county")
        results[f"round trip {key}"] = round_trip(entry, export, converted[key])
        results[f"county {key}"] = compare(contest, rounds, winner, official, exact=False)
        results[f"Alaska {key}"], changed = alaska_check(entry, converted[key], official)
        print(f"{key}: {len(contest.ballots)} ballots, {len(rounds)} rounds, winner "
              f"{contest.candidates[winner - 1][1].decode() if winner else 'none'}; county count against the "
              f"report: {', '.join(differences(contest, rounds, official)) or 'equal'}; 6 AAC 25.072 changes "
              f"{changed[0]} ballots and AS 15.15.350(e)(2) {changed[1]}")
    for name, problems in results.items():
        for p in problems:
            print(f"{name}: {p}", file=sys.stderr)
        failed += bool(problems)
    print(f"{len(results)} checks, {sum(bool(p) for p in results.values())} failing")
    for title, old, new, predicted in PLANTED:
        module = planted(old, new)
        caught = []
        for entry in section["contests"]:
            if entry["key"] not in converted:
                continue
            try:
                data_bytes = module.convert(module.Export(data / entry["export"]["path"]), entry["contest_id"],
                                            entry["identifier"])
            except module.ConversionError:
                caught.append(entry["key"])
                continue
            if alaska_check(entry, data_bytes, official_rounds(entry, data))[0]:
                caught.append(entry["key"])
        missed = [key for key in predicted if key in converted and key not in caught]
        print(f"planted error, {title}: fails the Alaska check of {', '.join(caught) or 'no contest'}")
        if missed:
            print(f"planted error, {title}: passes the Alaska check of {', '.join(missed)}", file=sys.stderr)
            failed += 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
