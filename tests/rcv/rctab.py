# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes a canonical ballot file as RCTab's input and compares RCTab's rounds with the reference's and the County's.

RCTab v2.1.0 runs on a Linux x86-64 host through `rctab.sh`, and this script prepares its input and
reads its detailed report.

  rctab.py cdf FILE OUT
  rctab.py compare FILE CONFIG RESULT [--county XML]

`cdf` writes the contest of the canonical ballot file FILE to OUT as a cast vote record report in
the JSON form of NIST SP 1500-103 that RCTab's `cdf` provider reads.  Each candidate of the file,
of every kind, becomes a candidate selection under its own name, and the configuration decides how
RCTab treats it.  Each mark of a position becomes the selection of its candidate at the position's
rank, so that a position with marks for several candidates gives several selections at one rank,
and the unnamed overvote `*` gives the selection of the candidate `overvote`, which a configuration
names as the source's `overvoteLabel`.  A ballot's identifier becomes its `BallotPrePrintedId`.
The script refuses a file in which a candidate is named `overvote`.

`compare` compares RCTab's detailed report RESULT, the `detailed_report.json` of a tabulation with
the configuration CONFIG, with the reference's count of FILE.  The rules of CONFIG choose the count:
`batchElimination` true with `continueUntilTwoCandidatesRemain` false gives the charter's count,
and the reverse gives the county count.  CONFIG must list the candidates of FILE in its tie-break
order, with `excluded` true exactly for the kinds `aggregate-writein` and `excluded`.

Round by round, RCTab's tally must equal the votes of the continuing candidates, its overvotes the
reason `overvote`, its exhausted choices the reasons `exhausted` and `uncounted` together, and its
skipped and repeated rankings 0, and the candidates that RCTab eliminates must be the round's
eliminated candidates.  RCTab's undervotes must equal the reason `blank`, and RCTab must elect the
reference's winner.  With --county, which applies to the county count, the rounds are compared in
the same way with the County's report: its Overvotes with RCTab's overvotes, and its Blanks and
Exhausted together with RCTab's undervotes and exhausted choices together.  With
`continueUntilTwoCandidatesRemain`, the round in which RCTab elects a candidate before two remain
eliminates no one, and the next round repeats its figures and eliminates.  The comparison omits
such a round when the next round's tally and inactive ballots equal its own, and prints a line
that names it.

The script prints each difference and a summary line per comparison.  The exit status is 0 when
every comparison passes, 1 when one fails, and 2 when an input cannot be read or CONFIG does not
match FILE.
"""

import argparse
import json
import sys
from decimal import Decimal
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import reference  # noqa: E402
import reports  # noqa: E402

OVERVOTE = "overvote"
UNCOUNTED = (b"aggregate-writein", b"excluded")


def fail(message):
    print(f"rctab.py: {message}", file=sys.stderr)
    sys.exit(2)


def read(path):
    contest = reference.read(Path(path).read_bytes())
    if isinstance(contest, reference.Malformed):
        fail(f"{path}: error {contest.line} {contest.role}")
    return contest


def cdf(contest):
    """The cast vote record report of a contest, as a JSON value."""
    names = [name.decode() for _, name in contest.candidates]
    if OVERVOTE in names:
        fail(f"a candidate is named {OVERVOTE}")
    ids = [f"c{i}" for i in range(1, len(names) + 1)] + ["c-overvote"]
    selection = {i: f"s{i}" for i in range(1, len(names) + 1)}
    cvrs = []
    for b, (identifier, words) in enumerate(contest.ballots, 1):
        marks = []
        for rank, word in enumerate(words, 1):
            if word == reference.UNNAMED:
                marks.append(("s-overvote", rank))
            else:
                marks += [(selection[i], rank) for i in selection if word >> (i - 1) & 1]
        cvr = {"@type": "CVR.CVR", "CurrentSnapshotId": f"b{b}", "ElectionId": "election",
               "CVRSnapshot": [{"@id": f"b{b}", "@type": "CVR.CVRSnapshot", "Type": "original",
                                "CVRContest": [{"@type": "CVR.CVRContest", "ContestId": "contest",
                                                "CVRContestSelection": [
                                                    {"@type": "CVR.CVRContestSelection", "ContestSelectionId": s,
                                                     "SelectionPosition": [{"@type": "CVR.SelectionPosition",
                                                                            "HasIndication": "yes",
                                                                            "NumberVotes": 1, "Rank": rank}]}
                                                    for s, rank in marks]}]}]}
        if identifier is not None:
            cvr["BallotPrePrintedId"] = identifier.decode()
        cvrs.append(cvr)
    return {
        "@type": "CVR.CastVoteRecordReport",
        "Version": "1.0.0",
        "GpUnit": [{"@id": "scope", "@type": "CVR.GpUnit", "Type": "other", "Name": contest.contest.decode()}],
        "Election": [{
            "@id": "election", "@type": "CVR.Election", "ElectionScopeId": "scope",
            "Candidate": [{"@id": c, "Name": name} for c, name in zip(ids, names + [OVERVOTE])],
            "Contest": [{"@id": "contest", "@type": "CandidateContest", "Name": contest.contest.decode(),
                         "ContestSelection": [{"@id": s, "@type": "CVR.CandidateSelection", "CandidateIds": [c]}
                                              for s, c in zip(list(selection.values()) + ["s-overvote"], ids)]}],
        }],
        "CVR": cvrs,
    }


def whole(text):
    value = Decimal(text)
    if value != value.to_integral_value():
        fail(f"{text} is not a whole number of ballots")
    return int(value)


def rctab_rounds(result):
    """RCTab's rounds, its undervotes, and the candidates it elects."""
    rounds = []
    for rnd in result["results"]:
        inactive = {k: whole(v) for k, v in rnd["inactiveBallots"].items()}
        rounds.append({
            "tally": {name: whole(v) for name, v in rnd["tally"].items()},
            "overvotes": inactive.pop("overvotes"),
            "exhausted": inactive.pop("exhaustedChoices"),
            "other": inactive,
            "eliminated": {a["eliminated"] for a in rnd["tallyResults"] if "eliminated" in a},
            "elected": {a["elected"] for a in rnd["tallyResults"] if "elected" in a},
        })
    elected = set().union(*(rnd["elected"] for rnd in rounds))
    return rounds, whole(result["summary"]["undervotes"]), elected


def omit_repeat(rounds):
    """The rounds without one that elects, eliminates no one, and repeats as the next, and its number."""
    figures = ("tally", "overvotes", "exhausted", "other")
    for k, (a, b) in enumerate(zip(rounds, rounds[1:]), 1):
        if a["elected"] and not a["eliminated"] and all(a[f] == b[f] for f in figures):
            return rounds[:k - 1] + rounds[k:], k
    return rounds, None


def check_config(config, contest):
    """The count that CONFIG's rules express, after checking its candidates against the file."""
    expected = [{"name": contest.candidates[i - 1][1].decode(), "excluded": contest.candidates[i - 1][0] in UNCOUNTED}
                for i in contest.order]
    listed = [{"name": c["name"], "excluded": c.get("excluded", False)} for c in config["candidates"]]
    if listed != expected:
        fail(f"the configuration's candidates {listed} differ from the file's {expected}")
    rules = config["rules"]
    modes = {(True, False): "charter", (False, True): "county"}
    key = (rules.get("batchElimination", False), rules.get("continueUntilTwoCandidatesRemain", False))
    if key not in modes:
        fail("the configuration's rules express neither the charter's count nor the county count")
    return modes[key]


def compare_reference(contest, mode, rounds, undervotes, elected):
    names = [name.decode() for _, name in contest.candidates]
    ref_rounds, winner = reference.count(contest, mode)
    problems = []
    if len(rounds) != len(ref_rounds):
        problems.append(f"{len(rounds)} rounds, the reference {len(ref_rounds)}")
    if undervotes != ref_rounds[0].inactive["blank"]:
        problems.append(f"undervotes {undervotes}, the reference's blank {ref_rounds[0].inactive['blank']}")
    for r, (ours, ref) in enumerate(zip(rounds, ref_rounds), 1):
        inactive = ref.inactive
        tally = {names[i - 1]: v for i, v in ref.votes.items()}
        if ours["tally"] != tally:
            problems.append(f"round {r}: tally {ours['tally']}, the reference {tally}")
        if ours["overvotes"] != inactive["overvote"]:
            problems.append(f"round {r}: overvotes {ours['overvotes']}, the reference {inactive['overvote']}")
        if ours["exhausted"] != inactive["exhausted"] + inactive["uncounted"]:
            problems.append(f"round {r}: exhausted choices {ours['exhausted']}, the reference's exhausted "
                            f"{inactive['exhausted']} and uncounted {inactive['uncounted']}")
        if any(ours["other"].values()):
            problems.append(f"round {r}: inactive ballots {ours['other']}")
        eliminated = {names[i - 1] for i in ref.eliminated}
        if ours["eliminated"] != eliminated:
            problems.append(f"round {r}: eliminates {sorted(ours['eliminated'])}, the reference {sorted(eliminated)}")
    expected = {names[winner - 1]} if winner else set()
    if elected != expected:
        problems.append(f"elects {sorted(elected)}, the reference {sorted(expected)}")
    return problems, len(ref_rounds)


def compare_county(report, rounds, undervotes, elected):
    problems = []
    if len(rounds) != len(report["rounds"]):
        problems.append(f"{len(rounds)} rounds, the report {len(report['rounds'])}")
    sets = reports.continuing_sets(report)
    for r, (ours, pub, continuing) in enumerate(zip(rounds, report["rounds"], sets), 1):
        if ours["tally"] != {name: pub["tallies"][name] for name in continuing}:
            problems.append(f"round {r}: tally {ours['tally']}, the report {pub['tallies']}")
        if ours["overvotes"] != pub["overvotes"]:
            problems.append(f"round {r}: overvotes {ours['overvotes']}, the report {pub['overvotes']}")
        if undervotes + ours["exhausted"] != pub["blanks"] + pub["exhausted"]:
            problems.append(f"round {r}: undervotes {undervotes} and exhausted choices {ours['exhausted']}, "
                            f"the report's Blanks {pub['blanks']} and Exhausted {pub['exhausted']}")
        if ours["eliminated"] != set(pub["eliminated"]):
            problems.append(f"round {r}: eliminates {sorted(ours['eliminated'])}, the report {pub['eliminated']}")
    if elected != set(report["rounds"][-1]["elected"]):
        problems.append(f"elects {sorted(elected)}, the report {report['rounds'][-1]['elected']}")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("cdf", help="write the cast vote record report of a canonical ballot file")
    p.add_argument("file")
    p.add_argument("out")
    p = sub.add_parser("compare", help="compare RCTab's detailed report with the reference and the County")
    p.add_argument("file")
    p.add_argument("config")
    p.add_argument("result")
    p.add_argument("--county", help="the County's RcvDetailedReport.xml, for the county count")
    args = ap.parse_args()

    try:
        contest = read(args.file)
        if args.command == "cdf":
            with open(args.out, "w", encoding="utf-8") as out:
                json.dump(cdf(contest), out, ensure_ascii=False, separators=(",", ":"))
                out.write("\n")
            return 0
        config = json.loads(Path(args.config).read_text(encoding="utf-8"))
        result = json.loads(Path(args.result).read_text(encoding="utf-8"))
        report = reports.parse(args.county) if args.county else None
    except (OSError, ValueError, reports.ReportError) as e:
        fail(e)

    mode = check_config(config, contest)
    if report is not None and mode != "county":
        fail("--county applies to the county count")
    rounds, undervotes, elected = rctab_rounds(result)
    label = contest.contest.decode()
    rounds, omitted = omit_repeat(rounds)
    if omitted is not None:
        print(f"{label} {mode}: RCTab's round {omitted} elects {', '.join(sorted(elected))} and eliminates no one, "
              f"and round {omitted + 1} repeats it, so the comparison omits round {omitted}")
    problems, n = compare_reference(contest, mode, rounds, undervotes, elected)
    for p in problems:
        print(f"{label} {mode} against the reference: {p}")
    print(f"{label} {mode} against the reference: {n} rounds, {'equal' if not problems else 'different'}")
    if report is not None:
        county = compare_county(report, rounds, undervotes, elected)
        for p in county:
            print(f"{label} {mode} against the County's report: {p}")
        print(f"{label} {mode} against the County's report: {len(report['rounds'])} rounds, "
              f"{'equal' if not county else 'different'}")
        problems += county
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
