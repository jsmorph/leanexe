# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes canonical ballot files as RCTab's input with configurations of the Maine count and compares
RCTab's rounds with the reference's Maine count.

RCTab v2.1.0 runs on a Linux x86-64 host through `tests/rcv/rctab.sh`, and this script writes its
input and its configurations and reads its results, with the functions of `tests/rcv/rctab.py`.

  rctab.py prepare RUN FILE ...
  rctab.py compare FILE CONFIG RESULTS

`prepare` writes, for each canonical ballot file FILE named `STEM.rcv`, its contest as the cast vote
record report `RUN/STEM.cdf.json` that `tests/rcv/rctab.py` writes and the configuration
`RUN/STEM-maine.json`, and it appends the line `STEM-maine.json results/STEM-maine` to the file
`RUN/runs`, the form that `rctab.sh batch` reads.  When the contest identifier, with `:` read as
`/`, is a key of `tests/rcv/maine/manifest.json`, the manifest's date and office label RCTab's
reports.

The configuration reads `STEM.cdf.json` from its own directory, writes RCTab's results into the
directory `STEM-maine` there, and lists the candidates in FILE's tie-break order, with `excluded`
true exactly for the kinds `aggregate-writein` and `excluded`.  Its rules are the Oakland charter's
configuration with `batchElimination` false, `continueUntilTwoCandidatesRemain` true, and
`maxSkippedRanksAllowed` 1.

`compare` compares the tabulation of FILE with the configuration CONFIG, whose results `rctab.sh
run` collected in the directory RESULTS, with the reference's Maine count of FILE.  CONFIG must be
the configuration that `prepare` writes for FILE, apart from its labels.  The reference's count,
changed by each of the rules below that applies, predicts what RCTab does.  Each rule states a
behavior of RCTab v2.1.0 that the count does not share, with the lines of RCTab's source at the tag
that give it, or, for initial-test, a provision that no setting expresses.

  no-counted-candidate  RCTab refuses a configuration whose candidates are all excluded
                        (ContestConfig.java 693-695, TabulatorSession.java 194).
  no-ballots            RCTab refuses a contest without ballots (TabulatorSession.java 442-444).
  one-counted-candidate With continueUntilTwoCandidatesRemain and one counted candidate, RCTab
                        tabulates no round (Tabulator.java 516-521) and then stops with a
                        NullPointerException where it writes its reports (855), so it writes none.
  initial-test          RCTab has no initial test of 21-A M.R.S. section 723-A(2).  Where the
                        initial test elects, RCTab counts the rounds of the count without the
                        initial test, whose winner is the test's winner by T11(c).
  final-tie             In a round with two continuing candidates with equal votes, RCTab elects the
                        one earlier in the list (Tabulator.java 630-663, Tiebreak.java 123-143).
                        The Maine count eliminates the other there and elects the same candidate in
                        a further round, which RCTab lacks.
  repeated-round        With continueUntilTwoCandidatesRemain, the round in which a candidate first
                        holds a majority while three or more candidates continue elects it and
                        eliminates no one (Tabulator.java 212-217, 241-243), and the next round
                        repeats its figures, the winner continuing (540-544), and eliminates.

Round by round, RCTab's tally must equal the votes of the continuing candidates, its overvotes the
reason `overvote`, its skipped rankings the ballots whose examination ends by rule 1 of the
interpretation, two empty positions before a marked one, its exhausted choices the other ballots of
the reasons `exhausted` and `uncounted`, and its repeated rankings 0, and the candidates that RCTab
eliminates and elects must be the round's.  RCTab's undervotes must equal the reason `blank` of
round 1.  Where a rule predicts that RCTab writes no report, RESULTS must hold RCTab's console
output with the rule's message and no report.

The script prints each difference and a line that classifies the comparison as equal, equal under
the rules that applied, or different.  The exit status is 0 when the comparison is not different,
1 when it is, and 2 when an input cannot be read or CONFIG does not match FILE.
"""

import argparse
import json
import re
import sys
from decimal import Decimal
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import rctab as oakland  # noqa: E402
import reference  # noqa: E402

MANIFEST = HERE / "manifest.json"
RULES = {
    "tiebreakMode": "useCandidateOrder", "overvoteRule": "exhaustImmediately",
    "winnerElectionMode": "singleWinnerMajority", "numberOfWinners": "1",
    "decimalPlacesForVoteArithmetic": "4", "minimumVoteThreshold": "0",
    "maxSkippedRanksAllowed": "1", "maxRankingsAllowed": "max",
    "nonIntegerWinningThreshold": False, "doesFirstRoundDetermineThreshold": False, "hareQuota": False,
    "batchElimination": False, "cutoffElimination": False, "continueUntilTwoCandidatesRemain": True,
    "stopTabulationEarlyAfterRound": "", "exhaustOnDuplicateCandidate": False,
    "rulesDescription": "Maine, 21-A M.R.S. section 723-A and 29-250 C.M.R. ch. 535"}


def candidates(contest):
    listed = oakland.names(contest)
    return [{"name": listed[i - 1], "excluded": contest.candidates[i - 1][0] in oakland.UNCOUNTED}
            for i in contest.order]


def configuration(contest, stem, date, office):
    """RCTab's configuration of a contest for the Maine count, as JSON text."""
    value = {
        "tabulatorVersion": oakland.VERSION,
        "outputSettings": {
            "contestName": f"{stem} maine", "outputDirectory": f"{stem}-maine", "contestDate": date,
            "contestJurisdiction": "Maine", "contestOffice": office, "tabulateByBatch": False,
            "tabulateByPrecinct": False, "generateCdfJson": False},
        "cvrFileSources": [{"filePath": f"{stem}.cdf.json", "contestId": contest.contest.decode(),
                            "provider": "cdf", "overvoteLabel": oakland.OVERVOTE}],
        "candidates": candidates(contest),
        "rules": RULES,
    }
    text = json.dumps(value, indent=2, ensure_ascii=False)
    return re.sub(r'\{\n +("name": [^\n]*),\n +("excluded": (?:true|false))\n +\}', r"{\1, \2}", text) + "\n"


def prepare(run, files):
    run.mkdir(parents=True, exist_ok=True)
    labels = {c["key"]: (c["date"], c["office"]) for c in json.loads(MANIFEST.read_text())["contests"]}
    for file in files:
        contest, stem = oakland.read(file), Path(file).stem
        date, office = labels.get(contest.contest.decode().replace(":", "/"), ("", ""))
        with open(run / f"{stem}.cdf.json", "w", encoding="utf-8") as out:
            json.dump(oakland.cdf(contest), out, ensure_ascii=False, separators=(",", ":"))
            out.write("\n")
        (run / f"{stem}-maine.json").write_text(configuration(contest, stem, date, office), encoding="utf-8")
        with open(run / "runs", "a", encoding="utf-8") as runs:
            runs.write(f"{stem}-maine.json results/{stem}-maine\n")


def rule_one(ballot, continuing):
    """Whether the examination of the Maine requirements' interpretation against `continuing` ends by
    rule 1: at an empty position whose next position is also empty, with a later position marked."""
    for p, word in enumerate(ballot):
        if word == 0:
            if p + 1 < len(ballot) and ballot[p + 1] == 0 and any(ballot[p + 2:]):
                return True
            continue
        if word == reference.UNNAMED or word & (word - 1) or word.bit_length() in continuing:
            return False
    return False


def predicted_round(rnd, listed, ballots):
    skipped = sum(m for ballot, m in ballots.items() if rule_one(ballot, set(rnd.votes)))
    return {"tally": {listed[i - 1]: v for i, v in rnd.votes.items()}, "overvotes": rnd.inactive["overvote"],
            "skipped": skipped, "exhausted": rnd.inactive["exhausted"] + rnd.inactive["uncounted"] - skipped,
            "eliminated": {listed[i - 1] for i in rnd.eliminated}, "elected": set()}


def predict(contest):
    """The rules that apply, and RCTab's predicted message without a report or its predicted rounds."""
    counted = [kind for kind, _ in contest.candidates if kind not in oakland.UNCOUNTED]
    for rule, applies in (("no-counted-candidate", not counted), ("no-ballots", not contest.ballots),
                          ("one-counted-candidate", len(counted) == 1)):
        if applies:
            return [rule], oakland.FAILURES[rule]
    listed = oakland.names(contest)
    _, _, ballots = reference.setup(contest)
    rules = []
    _, rounds, winner = reference.maine_count(contest)
    if not rounds:
        rules.append("initial-test")
        rounds, rounds_winner = reference.maine_rounds(contest)
        if rounds_winner != winner:
            oakland.fail(f"the count without the initial test names {rounds_winner}, the test {winner}")
    expected = [predicted_round(rnd, listed, ballots) for rnd in rounds]
    if len(rounds) > 1 and len(rounds[-1].votes) == 1:
        rules.append("final-tie")
        expected.pop()
        expected[-1]["eliminated"] = set()
    elect = len(expected) - 1
    for k, rnd in enumerate(rounds):
        if len(rnd.votes) >= 3 and any(2 * v > rnd.continuing for v in rnd.votes.values()):
            rules.append("repeated-round")
            expected.insert(k, dict(expected[k], eliminated=set()))
            elect = k
            break
    expected[elect]["elected"] = {listed[winner - 1]}
    return rules, expected


def compare(expected, rounds, undervotes, blank):
    problems = []
    if len(rounds) != len(expected):
        problems.append(f"{len(rounds)} rounds, expected {len(expected)}")
    if undervotes != blank:
        problems.append(f"undervotes {undervotes}, expected the reference's blank {blank}")
    for r, (ours, exp) in enumerate(zip(rounds, expected), 1):
        for key in ("tally", "overvotes", "skipped", "exhausted", "eliminated", "elected"):
            if ours[key] != exp[key]:
                problems.append(f"round {r}: {key} {oakland.shown(ours[key])}, expected {oakland.shown(exp[key])}")
        if any(ours["other"].values()):
            problems.append(f"round {r}: inactive ballots {ours['other']}")
    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare", help="write RCTab's input and Maine configurations of canonical ballot files")
    p.add_argument("run", help="the directory that receives the files")
    p.add_argument("files", nargs="+", metavar="file")
    p = sub.add_parser("compare", help="compare RCTab's results with the reference's Maine count")
    p.add_argument("file")
    p.add_argument("config")
    p.add_argument("results", help="the directory of a tabulation's results that rctab.sh run collected")
    args = ap.parse_args()

    try:
        if args.command == "prepare":
            prepare(Path(args.run), args.files)
            return 0
        contest = oakland.read(args.file)
        config = json.loads(Path(args.config).read_text(encoding="utf-8"))
        results = Path(args.results)
        result = None
        if (results / oakland.REPORT).exists():
            result = json.loads((results / oakland.REPORT).read_text(encoding="utf-8"), parse_float=Decimal)
        console = (results / oakland.CONSOLE).read_text(encoding="utf-8", errors="replace")
    except (OSError, ValueError) as e:
        oakland.fail(e)

    if config["candidates"] != candidates(contest) or config["rules"] != RULES:
        oakland.fail("the configuration's candidates or rules differ from those that prepare writes")
    label = Path(args.file).stem
    rules, expected = predict(contest)
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
        rounds, undervotes = oakland.rctab_rounds(result)
        for rnd in rounds:
            rnd["skipped"] = rnd["other"].pop("skippedRankings")
        what = f"{len(rounds)} rounds"
        blank = sum(not any(words) for _, words in contest.ballots)
        problems = compare(expected, rounds, undervotes, blank)
    for p in problems:
        print(f"{label} maine against the reference: {p}")
    print(f"{label} maine against the reference: {what}, {oakland.verdict(problems, rules)}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
