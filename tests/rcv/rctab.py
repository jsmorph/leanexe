# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes canonical ballot files as RCTab's input and compares RCTab's rounds with the reference's and the County's.

RCTab v2.1.0 runs on a Linux x86-64 host through `rctab.sh`, and this script writes its input and
its configurations and reads its results.

  rctab.py prepare RUN FILE ... [--date DATE] [--jurisdiction TEXT] [--office TEXT]
  rctab.py compare FILE CONFIG RESULTS [--county XML]

`prepare` writes, for each canonical ballot file FILE named `STEM.rcv`, its contest as a cast vote
record report `RUN/STEM.cdf.json` and RCTab's configurations `RUN/STEM-charter.json` and
`RUN/STEM-county.json`, and it appends to the file `RUN/runs` a line `STEM-MODE.json
results/STEM-MODE` for each configuration, the form that `rctab.sh batch` reads.  The date,
jurisdiction, and office label RCTab's reports.

The cast vote record report has the JSON form of NIST SP 1500-103 that RCTab's `cdf` provider
reads.  Each candidate of the file, of every kind, becomes a candidate selection under its name as
RCTab holds it, and the configuration decides how RCTab treats it.  RCTab holds a name as text, so
each byte of a name that is not part of UTF-8 text appears as `\\xhh`.  Each mark of a position
becomes the selection of its candidate at the position's rank, so that a position with marks for
several candidates gives several selections at one rank, and the unnamed overvote `*` gives the
selection of the candidate `overvote`, which a configuration names as the source's
`overvoteLabel`.  A ballot's identifier becomes its `BallotPrePrintedId`.  The script refuses a
file in which two names coincide as RCTab holds them, or in which a name equals, ignoring case,
`overvote` or a word that RCTab reserves (`ContestConfig.java` lines 468 to 490 at the tag
v2.1.0).

The configuration for MODE, `charter` or `county`, reads `STEM.cdf.json` from its own directory
and writes RCTab's results into the directory `STEM-MODE` there, so that tabulations run at the
same time write apart.  It lists the candidates in FILE's tie-break order, with `excluded` true
exactly for the kinds `aggregate-writein` and `excluded`.  The charter's configuration sets
`batchElimination` and the county count's `continueUntilTwoCandidatesRemain`.

`compare` compares the tabulation of FILE with the configuration CONFIG, whose results `rctab.sh
run` collected in the directory RESULTS, with the reference's count of FILE in the mode that
CONFIG's rules express.  CONFIG must list the candidates of FILE as `prepare` writes them.  The
reference's count, changed by each of the rules below that applies, predicts what RCTab does.
Each rule states a behavior of RCTab v2.1.0 that the count does not share, with the lines of
RCTab's source at the tag that give it.

  no-counted-candidate  RCTab refuses a configuration whose candidates are all excluded
                        (ContestConfig.java 693-695, TabulatorSession.java 194).
  no-ballots            RCTab refuses a contest without ballots (TabulatorSession.java 442-444).
  one-counted-candidate With continueUntilTwoCandidatesRemain and one counted candidate, RCTab
                        tabulates no round (Tabulator.java 516-521) and then stops with a
                        NullPointerException where it writes its reports (855), so it writes none.
  no-continuing-ballot  Where the charter's count ends by rule 2, without a continuing ballot,
                        RCTab counts as the county count does: no candidate reaches the threshold
                        of 1 (Tabulator.java 476-481, 699-700), no batch qualifies (912), and each
                        round eliminates the tied candidate latest in the list (802-818,
                        Tiebreak.java 127-131), until one candidate continues, whom RCTab elects
                        (Tabulator.java 589-593), or two, to whom final-tie applies.
  final-tie             In a round with two continuing candidates with equal votes, RCTab elects
                        the one earlier in the list (Tabulator.java 630-663, Tiebreak.java
                        123-143).  The charter's count eliminates the other there and elects the
                        same candidate in a further round, which RCTab lacks, and the county count
                        names none.
  repeated-round        With continueUntilTwoCandidatesRemain, the round in which a candidate first
                        holds a majority while three or more candidates continue elects it and
                        eliminates no one (Tabulator.java 212-217, 241-243), and the next round
                        repeats its figures, the winner continuing (540-544), and eliminates.

Round by round, RCTab's tally must equal the votes of the continuing candidates, its overvotes the
reason `overvote`, its exhausted choices the reasons `exhausted` and `uncounted` together, and its
skipped and repeated rankings 0, and the candidates that RCTab eliminates and elects must be the
round's.  RCTab's undervotes must equal the reason `blank` of round 1.  Where a rule predicts that
RCTab writes no report, RESULTS must hold RCTab's console output with the rule's message and no
report.

With --county, which applies to the county count, the rounds are compared in the same way with
the County's report, without the round that the next repeats: its Overvotes with RCTab's
overvotes, and its Blanks and Exhausted together with RCTab's undervotes and exhausted choices
together.  Where FILE lacks ballots of the report, a round passes under the rule missing-ballots
of `check.py`: each of the County's figures equals or exceeds RCTab's, and the excesses sum to the
missing ballots.

The script prints each difference and a line per comparison that classifies it as equal, equal
under the rules that applied, or different.  The exit status is 0 when no comparison is
different, 1 when one is, and 2 when an input cannot be read or CONFIG does not match FILE.
"""

import argparse
import json
import re
import sys
from decimal import Decimal
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check  # noqa: E402
import reference  # noqa: E402
import reports  # noqa: E402

VERSION = "2.1.0"
OVERVOTE = "overvote"
RESERVED = (OVERVOTE, "exhausted", "uncounted", "residual surplus")
UNCOUNTED = (b"aggregate-writein", b"excluded")
MODES = {"charter": (True, False, "Oakland City Charter section 1105"),
         "county": (False, True, "Alameda County practice")}
FAILURES = {"no-counted-candidate": "Contest config must contain at least 1 non-excluded candidate!",
            "no-ballots": "No cast vote records found!",
            "one-counted-candidate": 'Cannot invoke "network.brightspots.rcv.RoundTally.getSortedCandidatesByTally()"'}
REPORT, CONSOLE = "detailed_report.json", "console.txt"


def fail(message):
    print(f"rctab.py: {message}", file=sys.stderr)
    sys.exit(2)


def read(path):
    contest = reference.read(Path(path).read_bytes())
    if isinstance(contest, reference.Malformed):
        fail(f"{path}: error {contest.line} {contest.role}")
    return contest


def names(contest):
    """The candidates' names as RCTab holds them."""
    out = [name.decode("utf-8", "backslashreplace") for _, name in contest.candidates]
    if len(set(out)) != len(out):
        fail("two candidates' names coincide as RCTab holds them")
    for name in out:
        if name.lower() in RESERVED:
            fail(f"the candidate name {name} is reserved in RCTab")
    return out


def cdf(contest):
    """The cast vote record report of a contest, as a JSON value."""
    listed = names(contest)
    ids = [f"c{i}" for i in range(1, len(listed) + 1)] + ["c-overvote"]
    selection = {i: f"s{i}" for i in range(1, len(listed) + 1)}
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
            "Candidate": [{"@id": c, "Name": name} for c, name in zip(ids, listed + [OVERVOTE])],
            "Contest": [{"@id": "contest", "@type": "CandidateContest", "Name": contest.contest.decode(),
                         "ContestSelection": [{"@id": s, "@type": "CVR.CandidateSelection", "CandidateIds": [c]}
                                              for s, c in zip(list(selection.values()) + ["s-overvote"], ids)]}],
        }],
        "CVR": cvrs,
    }


def configuration(contest, stem, mode, date, jurisdiction, office):
    """RCTab's configuration of a contest for the charter's count or the county count, as JSON text."""
    batch, until_two, description = MODES[mode]
    listed = names(contest)
    value = {
        "tabulatorVersion": VERSION,
        "outputSettings": {
            "contestName": f"{stem} {mode}", "outputDirectory": f"{stem}-{mode}", "contestDate": date,
            "contestJurisdiction": jurisdiction, "contestOffice": office, "tabulateByBatch": False,
            "tabulateByPrecinct": False, "generateCdfJson": False},
        "cvrFileSources": [{"filePath": f"{stem}.cdf.json", "contestId": contest.contest.decode(),
                            "provider": "cdf", "overvoteLabel": OVERVOTE}],
        "candidates": [{"name": listed[i - 1], "excluded": contest.candidates[i - 1][0] in UNCOUNTED}
                       for i in contest.order],
        "rules": {
            "tiebreakMode": "useCandidateOrder", "overvoteRule": "exhaustImmediately",
            "winnerElectionMode": "singleWinnerMajority", "numberOfWinners": "1",
            "decimalPlacesForVoteArithmetic": "4", "minimumVoteThreshold": "0",
            "maxSkippedRanksAllowed": "unlimited", "maxRankingsAllowed": "max",
            "nonIntegerWinningThreshold": False, "doesFirstRoundDetermineThreshold": False, "hareQuota": False,
            "batchElimination": batch, "cutoffElimination": False, "continueUntilTwoCandidatesRemain": until_two,
            "stopTabulationEarlyAfterRound": "", "exhaustOnDuplicateCandidate": False,
            "rulesDescription": description},
    }
    text = json.dumps(value, indent=2, ensure_ascii=False)
    return re.sub(r'\{\n +("name": [^\n]*),\n +("excluded": (?:true|false))\n +\}', r"{\1, \2}", text) + "\n"


def prepare(run, files, date, jurisdiction, office):
    run.mkdir(parents=True, exist_ok=True)
    for file in files:
        contest, stem = read(file), Path(file).stem
        with open(run / f"{stem}.cdf.json", "w", encoding="utf-8") as out:
            json.dump(cdf(contest), out, ensure_ascii=False, separators=(",", ":"))
            out.write("\n")
        for mode in MODES:
            (run / f"{stem}-{mode}.json").write_text(configuration(contest, stem, mode, date, jurisdiction, office),
                                                    encoding="utf-8")
        with open(run / "runs", "a", encoding="utf-8") as runs:
            runs.writelines(f"{stem}-{mode}.json results/{stem}-{mode}\n" for mode in MODES)


def whole(value):
    number = Decimal(value)
    if number != number.to_integral_value():
        fail(f"{value} is not a whole number of ballots")
    return int(number)


def rctab_rounds(result):
    """RCTab's rounds and its undervotes."""
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
    return rounds, whole(result["summary"]["undervotes"])


def check_config(config, contest):
    """The count that CONFIG's rules express, after checking its candidates against the file."""
    listed = names(contest)
    expected = [{"name": listed[i - 1], "excluded": contest.candidates[i - 1][0] in UNCOUNTED} for i in contest.order]
    found = [{"name": c["name"], "excluded": c.get("excluded", False)} for c in config["candidates"]]
    if found != expected:
        fail(f"the configuration's candidates {found} differ from the file's {expected}")
    rules = config["rules"]
    key = (rules.get("batchElimination", False), rules.get("continueUntilTwoCandidatesRemain", False))
    modes = {(batch, until_two): mode for mode, (batch, until_two, _) in MODES.items()}
    if key not in modes:
        fail("the configuration's rules express neither the charter's count nor the county count")
    return modes[key]


def predicted_round(rnd, listed):
    return {"tally": {listed[i - 1]: v for i, v in rnd.votes.items()}, "overvotes": rnd.inactive["overvote"],
            "exhausted": rnd.inactive["exhausted"] + rnd.inactive["uncounted"],
            "eliminated": {listed[i - 1] for i in rnd.eliminated}, "elected": set()}


def predict(contest, mode):
    """The rules that apply, and RCTab's predicted message without a report, or its predicted rounds
    with the index of the round that the next repeats."""
    counted = [kind for kind, _ in contest.candidates if kind not in UNCOUNTED]
    for rule, applies in (("no-counted-candidate", not counted), ("no-ballots", not contest.ballots),
                          ("one-counted-candidate", mode == "county" and len(counted) == 1)):
        if applies:
            return [rule], FAILURES[rule], None
    listed = names(contest)
    rules = []
    rounds, winner = reference.count(contest, mode)
    if mode == "charter" and winner is None:
        rules.append("no-continuing-ballot")
        rounds, winner = reference.count(contest, "county")
    expected = [predicted_round(rnd, listed) for rnd in rounds]
    if len(rounds) > 1 and len(rounds[-1].votes) == 1:
        rules.append("final-tie")
        expected.pop()
        expected[-1]["eliminated"] = set()
    elif winner is None:
        rules.append("final-tie")
        winner = min(rounds[-1].votes, key=contest.order.index)
    elect, repeat = len(expected) - 1, None
    if mode == "county":
        for k, rnd in enumerate(rounds):
            if len(rnd.votes) >= 3 and any(2 * v > rnd.continuing for v in rnd.votes.values()):
                rules.append("repeated-round")
                expected.insert(k, dict(expected[k], eliminated=set()))
                elect = repeat = k
                break
    expected[elect]["elected"] = {listed[winner - 1]}
    return rules, expected, repeat


def shown(value):
    return sorted(value) if isinstance(value, set) else value


def compare_reference(expected, rounds, undervotes, blank):
    problems = []
    if len(rounds) != len(expected):
        problems.append(f"{len(rounds)} rounds, expected {len(expected)}")
    if undervotes != blank:
        problems.append(f"undervotes {undervotes}, expected the reference's blank {blank}")
    for r, (ours, exp) in enumerate(zip(rounds, expected), 1):
        for key in ("tally", "overvotes", "exhausted", "eliminated", "elected"):
            if ours[key] != exp[key]:
                problems.append(f"round {r}: {key} {shown(ours[key])}, expected {shown(exp[key])}")
        if any(ours["other"].values()):
            problems.append(f"round {r}: inactive ballots {ours['other']}")
    return problems


def compare_county(report, rounds, undervotes, elected, missing):
    problems = []
    if len(rounds) != len(report["rounds"]):
        problems.append(f"{len(rounds)} rounds, the report {len(report['rounds'])}")
    for r, (ours, pub, continuing) in enumerate(zip(rounds, report["rounds"], reports.continuing_sets(report)), 1):
        if set(ours["tally"]) != set(continuing):
            problems.append(f"round {r}: continuing {sorted(ours['tally'])}, the report {continuing}")
            continue
        mine = dict(ours["tally"], Overvotes=ours["overvotes"])
        mine["Blanks and Exhausted"] = undervotes + ours["exhausted"]
        theirs = {name: pub["tallies"][name] for name in continuing}
        theirs.update({"Overvotes": pub["overvotes"], "Blanks and Exhausted": pub["blanks"] + pub["exhausted"]})
        problems += [f"round {r}: {p}" for p in check.differences(mine, theirs, missing)]
        if ours["eliminated"] != set(pub["eliminated"]):
            problems.append(f"round {r}: eliminates {sorted(ours['eliminated'])}, the report {pub['eliminated']}")
    if elected != set(report["rounds"][-1]["elected"]):
        problems.append(f"elects {sorted(elected)}, the report {report['rounds'][-1]['elected']}")
    return problems


def verdict(problems, rules):
    if problems:
        return "different"
    return f"equal under {', '.join(rules)}" if rules else "equal"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare", help="write RCTab's input and configurations of canonical ballot files")
    p.add_argument("run", help="the directory that receives the files")
    p.add_argument("files", nargs="+", metavar="file")
    p.add_argument("--date", default="", help="the contest's date")
    p.add_argument("--jurisdiction", default="", help="the contest's jurisdiction")
    p.add_argument("--office", default="", help="the contest's office")
    p = sub.add_parser("compare", help="compare RCTab's results with the reference and the County")
    p.add_argument("file")
    p.add_argument("config")
    p.add_argument("results", help="the directory of a tabulation's results that rctab.sh run collected")
    p.add_argument("--county", help="the County's RcvDetailedReport.xml, for the county count")
    args = ap.parse_args()

    try:
        if args.command == "prepare":
            prepare(Path(args.run), args.files, args.date, args.jurisdiction, args.office)
            return 0
        contest = read(args.file)
        config = json.loads(Path(args.config).read_text(encoding="utf-8"))
        results = Path(args.results)
        result = None
        if (results / REPORT).exists():
            result = json.loads((results / REPORT).read_text(encoding="utf-8"), parse_float=Decimal)
        console = (results / CONSOLE).read_text(encoding="utf-8", errors="replace")
        report = reports.parse(args.county) if args.county else None
    except (OSError, ValueError, reports.ReportError) as e:
        fail(e)

    mode = check_config(config, contest)
    if report is not None and mode != "county":
        fail("--county applies to the county count")
    label = Path(args.file).stem
    rules, expected, repeat = predict(contest, mode)
    problems = []
    if isinstance(expected, str):
        what = "no report"
        if result is not None:
            problems.append(f"RCTab wrote a report, where {rules[0]} predicts none")
        elif expected not in console:
            problems.append(f"the console output lacks the message {expected!r} of {rules[0]}")
    elif result is None:
        what = "no report"
        severe = [line for line in console.splitlines() if "SEVERE" in line]
        problems.append(f"RCTab wrote no report: {severe[0] if severe else 'the console output holds no SEVERE line'}")
    else:
        rounds, undervotes = rctab_rounds(result)
        what = f"{len(rounds)} rounds"
        blank = sum(not any(words) for _, words in contest.ballots)
        problems = compare_reference(expected, rounds, undervotes, blank)
    for p in problems:
        print(f"{label} {mode} against the reference: {p}")
    print(f"{label} {mode} against the reference: {what}, {verdict(problems, rules)}")
    if report is not None and result is not None:
        first = report["rounds"][0]
        missing = first["continuing"] + first["non_transferable"] - len(contest.ballots)
        elected = set().union(*(rnd["elected"] for rnd in rounds))
        kept = [rnd for k, rnd in enumerate(rounds) if k != repeat]
        county = compare_county(report, kept, undervotes, elected, missing)
        county_rules = (["repeated-round"] if repeat is not None else []) + (["missing-ballots"] if missing else [])
        for p in county:
            print(f"{label} {mode} against the County's report: {p}")
        print(f"{label} {mode} against the County's report: {len(report['rounds'])} rounds, "
              f"{verdict(county, county_rules)}")
        problems += county
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
