# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Normalizes Alameda County's RCV detailed reports and applies Oakland Charter §1105 to their tallies.

For each contest of `manifest.json`, the script parses the report's XML under the data directory,
checks its arithmetic, and writes `normalized/<election>/<race>.json` there.  The JSON gives the
report's title fields and settings, the candidates, and every round's tallies, inactive categories,
eliminations, and transfers.  Its `charter` member applies §1105(d)(2) and (f) to the published
tallies: the first round at which a candidate holds more than half of the continuing ballots, and
the charter's count read off the published rounds, with each batch that §1105(f) eliminates.  The
script prints a Markdown table of the corpus on stdout and exits with status 1 if a report is
missing or fails a check.
"""

import argparse
import csv
import json
import re
import sys
import xml.etree.ElementTree as ET
from decimal import Decimal
from pathlib import Path

HERE = Path(__file__).resolve().parent
NS = "{RcvDetailedReport}"
CATEGORIES = {"Blanks": "blanks", "Overvotes": "overvotes", "Exhausted": "exhausted",
              "Suspended": "suspended", "Remainder Points": "remainder_points"}
STATUS = re.compile(r"^(.*) is (eliminated|elected) because (.*)$")
EMPTY_STATUS = re.compile(r"^.* is  because $")


class ReportError(Exception):
    pass


def count(text):
    value = Decimal(text)
    if value != value.to_integral_value() or value < 0:
        raise ReportError(f"{text} is not a whole number of ballots")
    return int(value)


def parse(path):
    """The normalized form of one RcvDetailedReport.xml."""
    root = ET.parse(path).getroot()
    title = root.find(f"{NS}Title/{NS}Report").attrib
    static = root.find(f"{NS}RcvStaticData/{NS}Report")
    head = static.find(f"{NS}Tablix2").attrib
    settings = dict(static.find(f"{NS}Tablix3").attrib)
    candidates = []
    rounds = []
    for number, group in enumerate(root.iter(f"{NS}roundGroup"), start=1):
        box = group.find(f"{NS}Tablix5")
        name, _, threshold = box.get("Textbox86").partition("Threshold:")
        if name.strip() != f"Round {number}":
            raise ReportError(f"round {number} is labelled {name.strip()!r}")
        rnd = {"round": number, "tallies": {}, "continuing": count(box.get("continuingVotes")),
               "non_transferable": count(box.get("nonTransferableVotes"))}
        rnd.update({key: 0 for key in CATEGORIES.values()})
        if threshold.strip():
            rnd["threshold"] = int(threshold.strip().replace(",", ""))
        for choice in box.iter(f"{NS}choiceGroup"):
            label, votes = choice.get("choiceName2"), count(choice.get("votes"))
            if label in CATEGORIES:
                rnd[CATEGORIES[label]] = votes
            else:
                if number == 1:
                    candidates.append(label)
                elif label not in candidates:
                    raise ReportError(f"round {number} names {label!r}, absent from round 1")
                rnd["tallies"][label] = votes
        rnd["eliminated"], rnd["elected"], rnd["defeated"] = [], [], []
        for status in group.iter(f"{NS}StatusGroup"):
            text = status.get("Textbox21", "")
            if EMPTY_STATUS.match(text):
                continue
            m = STATUS.match(text)
            if m is None:
                raise ReportError(f"round {number}: unknown status {text!r}")
            who, verb, reason = m.groups()
            if verb == "elected":
                kind = "elected"
            elif reason.startswith("the candidate had the least amount of votes"):
                kind = "eliminated"
            elif reason.startswith("the candidate was not elected in the last round"):
                kind = "defeated"
            else:
                raise ReportError(f"round {number}: unknown status {text!r}")
            if who not in rnd[kind]:
                rnd[kind].append(who)
        for tie in group.iter(f"{NS}TieReason"):
            if tie.get("Textbox14", "").strip() != "A tie occurred during":
                rnd.setdefault("ties", []).append(tie.get("Textbox14"))
        rnd["transfers"] = []
        for source in group.iter(f"{NS}sourceChoiceId"):
            moves = {}
            origin = None
            for move in source.iter(f"{NS}choiceId"):
                if move.get("sourceChoiceName") is None:
                    continue
                origin = move.get("sourceChoiceName")
                moves[move.get("choiceName")] = count(move.get("votes5").lstrip("-"))
            if origin is not None:
                if origin not in moves:
                    raise ReportError(f"round {number}: the transfer from {origin} omits its own total")
                moved = moves.pop(origin)
                if sum(moves.values()) != moved:
                    raise ReportError(f"round {number}: transfers from {origin} do not sum to {moved}")
                rnd["transfers"].append({"from": origin, "ballots": moved, "to": moves})
        rounds.append(rnd)
    report = {
        "election_name": title.get("Textbox3"),
        "election_date": title.get("Textbox9", "")[:10],
        "status": title.get("Textbox8"),
        "contest": head.get("Textbox24"),
        "results": head.get("Textbox21"),
        "positions": head.get("Textbox53"),
        "state": head.get("state"),
        "timestamp": head.get("timeStamp"),
        "settings": settings,
        "candidates": candidates,
        "rounds": rounds,
    }
    check(report)
    return report


def check(report):
    """Raises ReportError unless every round's figures agree with each other and with the next round."""
    rounds = report["rounds"]
    if not rounds:
        raise ReportError("no rounds")
    total = rounds[0]["continuing"] + rounds[0]["non_transferable"]
    for i, rnd in enumerate(rounds):
        n = rnd["round"]
        if sum(rnd["tallies"].values()) != rnd["continuing"]:
            raise ReportError(f"round {n}: tallies do not sum to continuingVotes")
        inactive = sum(rnd[k] for k in ("blanks", "overvotes", "exhausted", "suspended"))
        if inactive != rnd["non_transferable"] or rnd["remainder_points"] != 0:
            raise ReportError(f"round {n}: inactive categories do not sum to nonTransferableVotes")
        if rnd["continuing"] + rnd["non_transferable"] != total:
            raise ReportError(f"round {n}: ballot total differs from round 1")
        if i + 1 < len(rounds):
            nxt = rounds[i + 1]
            change = {**{c: nxt["tallies"][c] - rnd["tallies"][c] for c in report["candidates"]},
                      **{label: nxt[key] - rnd[key] for label, key in CATEGORIES.items()}}
            for t in rnd["transfers"]:
                change[t["from"]] += t["ballots"]
                for to, k in t["to"].items():
                    change[to] -= k
            if any(change.values()):
                raise ReportError(f"round {n}: transfers do not account for round {n + 1}")
            if len(rnd["eliminated"]) != 1:
                raise ReportError(f"round {n}: {len(rnd['eliminated'])} eliminations")


def continuing_sets(report):
    """The candidates that the report treats as continuing in each round."""
    current = list(report["candidates"])
    sets = []
    for rnd in report["rounds"]:
        sets.append(list(current))
        current = [c for c in current if c not in rnd["eliminated"]]
    return sets


def majority(tallies):
    total = sum(tallies.values())
    return [c for c, v in tallies.items() if 2 * v > total]


def batch(tallies):
    """The largest set of two or more candidates that §1105(f) eliminates, or [] if none qualifies.

    For a continuing candidate c, the set is every continuing candidate with fewer votes than c, and
    it qualifies when c's votes exceed the set's combined total.
    """
    best = []
    for c, v in tallies.items():
        lower = [d for d, w in tallies.items() if w < v]
        if len(lower) >= 2 and v > sum(tallies[d] for d in lower) and len(lower) > len(best):
            best = lower
    return sorted(best, key=lambda d: (tallies[d], d))


def charter(report):
    """§1105(d)(2) and (f) applied to the report's tallies.

    The charter's count is read off the published rounds.  After a batch of k candidates at report
    round r, the charter's next round is report round r + k, provided the report eliminates the
    batch's members one per round in rounds r to r + k - 1; a member of the batch always has fewer
    votes than every candidate outside it, so single elimination takes the batch first.
    """
    rounds = report["rounds"]
    sets = continuing_sets(report)
    first = next((r["round"] for r, s in zip(rounds, sets)
                  if majority({c: r["tallies"][c] for c in s})), None)
    result = {"majority_round": first, "report_rounds": len(rounds), "rounds": [], "batches": []}
    p, k = 0, 1
    while True:
        if p >= len(rounds):
            result["incomplete"] = "the report ends before the charter's count"
            break
        tallies = {c: rounds[p]["tallies"][c] for c in sets[p]}
        step = {"charter_round": k, "report_round": p + 1}
        winners = majority(tallies)
        if winners:
            step["winner"] = winners[0]
            result["rounds"].append(step)
            result["stop"] = step
            break
        group = batch(tallies)
        if group:
            above = min((d for d in tallies if d not in group), key=lambda d: (tallies[d], d))
            result["batches"].append({**step, "members": group,
                                      "combined": sum(tallies[d] for d in group),
                                      "next": above, "next_votes": tallies[above]})
            step["eliminate"] = group
        else:
            least = min(tallies.values())
            lowest = sorted(c for c, v in tallies.items() if v == least)
            if len(lowest) > 1:
                step["tie"] = lowest
            step["eliminate"] = rounds[p]["eliminated"] if len(lowest) > 1 else lowest
        published = [x for r in rounds[p:p + len(step["eliminate"])] for x in r["eliminated"]]
        result["rounds"].append(step)
        if sorted(published) != sorted(step["eliminate"]):
            result["incomplete"] = (f"report rounds {p + 1} to {p + len(step['eliminate'])} eliminate "
                                    f"{published}, the charter {step['eliminate']}")
            break
        p += len(step["eliminate"])
        k += 1
    result["first_batch_round"] = result["batches"][0]["report_round"] if result["batches"] else None
    final = rounds[-1]
    result["report_winner"] = final["elected"][0] if final["elected"] else None
    return result


def cvr_shape(path):
    """The number of ballots and of ranking columns in an Otis CVR file."""
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.reader(f)
        header = next(reader)
        return sum(1 for _ in reader), sum(1 for h in header if re.fullmatch(r"rank\d+", h))


def table(rows):
    head = ["Election", "Contest", "Candidates", "Rankings", "CVR", "CVR ballots", "Report ballots",
            "Elimination", "Suspension", "Previous rounds", "Threshold stop",
            "Report rounds", "Majority round", "Charter stop (charter round)", "First batch (size)"]
    lines = ["| " + " | ".join(head) + " |", "|" + "---|" * len(head)]
    for r in rows:
        lines.append("| " + " | ".join(str(x) for x in r) + " |")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("data", nargs="?", default="tmp/rcv-data", help="data directory (default tmp/rcv-data)")
    args = ap.parse_args()
    data = Path(args.data)
    manifest = json.loads((HERE / "manifest.json").read_text())
    rows, failed = [], 0
    for contest in manifest["contests"]:
        src = data / contest["report"]["path"]
        if not src.exists():
            print(f"{contest['key']}: {src} is missing", file=sys.stderr)
            failed += 1
            continue
        try:
            report = parse(src)
        except (ReportError, ET.ParseError) as e:
            print(f"{contest['key']}: {e}", file=sys.stderr)
            failed += 1
            continue
        report["key"] = contest["key"]
        report["source"] = {"path": contest["report"]["path"], "sha256": contest["report"]["sha256"]}
        report["charter"] = charter(report)
        out = data / "normalized" / Path(contest["report"]["path"]).relative_to("reports").with_suffix(".json")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
        r1 = report["rounds"][0]
        ballots = r1["continuing"] + r1["non_transferable"]
        if "cvr" in contest and (data / contest["cvr"]["path"]).exists():
            n, ranks = cvr_shape(data / contest["cvr"]["path"])
            source, counted = "Otis", f"{n:,}"
        else:
            source, ranks, counted = "none", "n/a", "n/a"
        s, ch = report["settings"], report["charter"]
        stop = ch.get("stop")
        first = ch["batches"][0] if ch["batches"] else None
        rows.append([
            f"{contest['election']} ({contest['date']})", contest["office"], len(report["candidates"]),
            ranks, source, counted, f"{ballots:,}", s.get("eliminationType"),
            s.get("useFirstRoundSuspension"), s.get("previousRoundsEvaluation"),
            s.get("winnersByThreshold"), ch["report_rounds"], ch["majority_round"] or "none",
            f"{stop['report_round']} ({stop['charter_round']})" if stop else ch.get("incomplete", "none"),
            f"{first['report_round']} ({len(first['members'])})" if first else "none",
        ])
    print(table(rows))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
