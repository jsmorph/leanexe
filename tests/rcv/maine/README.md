# Maine RCV corpus

This directory holds the corpus of the tabulator's Maine module and the scripts that verify, convert, and check it.  [The manifest](manifest.json) pins by URL, size, and SHA-256 the Secretary of State's summary reports, first-choice results, and cast vote record spreadsheets of the contests that [the Maine requirements](../../../Demos/Rcv/Maine/requirements.md#tests) name, with the 2026 primary candidate and withdrawal lists.  The repository holds none of the files, which the scripts read from `tmp/rcv-maine-data` unless a command names another directory, and [the notice](NOTICE) records the publisher's terms of use.  The scripts run from the repository root with `uv run` and use only Python's standard library, and a script that reads the downloaded files runs with Python's `-I`, since the files are untrusted data.

| File | Command | Behavior |
|---|---|---|
| [`fetch.py`](fetch.py) | `uv run python -I tests/rcv/maine/fetch.py [DIR]` | Verifies each file of the manifest by size and SHA-256 and downloads a missing or mismatched one under its own user-agent string.  www.maine.gov answers the script with HTTP 403, so a person saves missing files from a browser at their manifest paths |
| [`recount.py`](recount.py) | `uv run python -I tests/rcv/maine/recount.py [KEY ...] [--residual LABEL] [--writein empty] [--no-skip-rule] [--data DIR]` | Recounts each contest by the requirements' reading and prints the differences from the summary report, the figures behind [the review's facts](../../../Demos/Rcv/Maine/review.md#facts-behind-the-requirements) |
| [`convert.py`](convert.py) | `uv run python -I tests/rcv/maine/convert.py KEY [--data DIR] [--order I ...] [--named-writein NAME] [--excluded NAME] [--practice] [--out FILE]` | Writes the canonical ballot file of a contest ([The converter](#the-converter)) |
| [`check.py`](check.py) | `uv run python -I tests/rcv/maine/check.py [--data DIR] [--out DIR]` | Converts every contest, writes the canonical files with the reference's Maine report and words, and checks them against the summary reports ([Checks](#checks)) |
| [`edges.py`](edges.py) | `uv run tests/rcv/maine/edges.py [OUT]` | Writes the Maine edge cases and the shared ones with the reference's Maine outputs into `OUT`, `tmp/rcv-maine-edges` by default ([Edge cases](#edge-cases)) |
| [`rctab.py`](rctab.py) | `uv run tests/rcv/maine/rctab.py prepare RUN FILE ...` or `compare FILE CONFIG RESULTS` | Writes RCTab's input and configuration of the Maine count for canonical files, and compares RCTab's rounds with the reference's Maine count ([RCTab](#rctab)) |
| [`tabulate.py`](tabulate.py) | `uv run tests/rcv/maine/tabulate.py [--module PATH] [--host PATH] [--maine PATH] [--process PATH] [--lean-process PATH] [--native PATH] DIR ...` | Compares the exports `tabulate` and `count` of the Maine module in the Wasmtime host, the specification and the programs in native Lean, the outputs stored beside each file, and with its options the WASI process, the native process, and the C executable, with the reference's Maine report and result words |

## The converter

`convert.py` reads a contest's spreadsheets in the manifest's order with Python's zip and XML modules.  The first row of each worksheet is its header, the first column holds the Cast Vote Record number, and the ranking columns are those whose header holds `Choice`, which must be the same in every worksheet of the contest.  The candidates are the summary report's, in the report's order, as `recount.py` transcribes them, each of kind `listed`, followed by the aggregate write-in `Write-in` when a spreadsheet ranks it, by `named-writein` candidates that `--named-writein` names, and by `excluded` candidates that `--excluded` names.  A ranking cell `undervote`, or a cell without a value, gives an empty field, `overvote` gives `*`, a candidate's name with its surrounding spaces removed gives its index, and `Write-in` gives the aggregate's.  Each line's identifier is the spreadsheet's manifest label, a colon, and the Cast Vote Record number without a trailing `.0`, such as `export-1:15876`, the contest identifier is the manifest key with `/` replaced by `:`, and the order is `--order` or 1 to `n`.

The 2024 records rank the declared write-in candidate Diane Merenda only inside `Write-in`, which the kind `aggregate-writein` does not admit, so the converter refuses that contest unless `--practice` names the comparison with the Secretary of State's count, as [the review's departures](../../../Demos/Rcv/Maine/review.md#departures-of-official-practice) describe.  The script's docstring lists the other spreadsheets that it refuses with a message on standard error and exit status 1.  The ranking cells of the corpus hold `undervote`, `overvote`, the candidates' names, some with a trailing space, and, in 2024 alone, `Write-in`, and the State Senate District 4 and House District 58 spreadsheets of uniformed-service and overseas voters omit the cells of trailing rankings.

## Checks

`check.py` converts each contest of the manifest that has spreadsheets, writes the canonical file under `DATA/canonical` or `--out` with the reference's Maine report, contest words, and Maine result words, and checks the reference's count against the summary reports' figures that `recount.py` transcribes.  The round trip reads each file back with the reference's reader and compares it with the spreadsheets read again with `recount.py`'s reader, and the reference's writer must reproduce the file.  For the three contests whose figures differ, the residual check counts every spreadsheet but the third manual-entry one with the report's continuing sets: the report's figures minus that count must be nonnegative, sum to that spreadsheet's rows, and not decrease from round to round for a continuing candidate or for the inactive ballots.  The House District 58 report after its header lines must equal the requirements' block.

| Contest | Ballots | Rounds and winner | Against the summary report |
|---|---|---|---|
| 2026 Democratic, Representative to Congress, District 2 | 83,480 | 3, Dunlap | Every elimination and the winner equal, each figure within 21 votes, and the differences consistent with the 77 rows of the third manual-entry spreadsheet |
| 2026 Democratic, Governor | 222,405 | 4, Pingree | The same, within 17 votes and with 78 rows |
| 2026 Republican, Governor | 137,981 | 7, Charles | The same, within 4 votes and with 18 rows |
| 2026 Republican, State Senate District 4 | 6,399 | 3, Perkins | Every figure equal |
| 2026 Republican, House District 58 | 1,407 | 2, Bridges | Every figure equal, and the report equals the requirements' block |
| 2024 general, Representative to Congress, District 2 | 402,936 | 1, Golden | Every figure equal, converted with `--practice` |

The initial test elects no one in any of the six contests, whose largest first-ranking share is Golden's 196,349 of 402,936.  Each planted error is a copy of `convert.py` with one change, and each fails the round trip of all six contests: an overvote written as an empty field, the candidates' indices reversed, and the first ranking column dropped.  The script prints one line per contest and per planted error, ends with `0 checks failing`, and took about two minutes on one core.

## Edge cases

`edges.py` writes the Maine edge cases of the requirements' Tests section, the requirements' 17-ballot and five-ballot examples, and every case of `tests/rcv/edges.py` with the prefix `shared-`, each with the reference's Maine report and Maine result words.  The script's docstring lists the cases.  The small Maine cases carry report lines or result words derived by hand from the requirements, the pattern contests compare each ballot's interpretation against every subset of the counted candidates with a second statement of the rule, and the script checks that the writer reproduces every file that the reader accepts and that the result words agree with the report.  It prints `36 Maine and 269 shared well-formed files, 64 malformed files, 300 edited files of which the reader accepts 15, 17 word arrays, 110 with hand-stated expectations, 18720 interpretations compared with the second reading, 0 failing`.

## RCTab

RCTab v2.1.0, which [the corpus's RCTab section](../README.md#rctab) pins and runs with `tests/rcv/rctab.sh`, counts the Maine corpus's contests and the Maine edge cases as a second tabulator, with a configuration of the Maine count.  `rctab.py prepare` writes each canonical file as the cast vote record report of `tests/rcv/rctab.py`, writes the file's configuration `STEM-maine.json` beside it, and adds its line to the list that `rctab.sh batch` reads.  [The configurations](../rctab/maine/) are those that `prepare` writes for the six contests of the corpus.  Each lists the candidates in the file's tie-break order, with `Write-in` excluded in the 2024 contest, and takes its date and office from the manifest.  The table maps each setting to the provision that it expresses, with the lines of RCTab's source at the tag v2.1.0 where the configuration documentation leaves the behavior open.

| Setting | Value | Provision |
|---|---|---|
| `candidates`, `tiebreakMode` | The file's candidates in its tie-break order, and `useCandidateOrder` | §723-A(3) and §732(1), by decision 3 of [the review](../../../Demos/Rcv/Maine/review.md): the order encodes the recorded drawings.  Of the candidates tied for the fewest votes, RCTab eliminates the one latest in the list, as rule 2 of the rounds does |
| `excluded` | `true` for the candidates of kinds `aggregate-writein` and `excluded`, and `false` for the others | §723-A(1)(C-1) and (2-A), §371(5) and (6), §374-A(3)(C), and §696(2)(E).  RCTab passes over a ranking of an excluded candidate, as rule 5 of the interpretation passes over an uncounted candidate ([`Tabulator.java` 540–552](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L540-L552)).  The ranking stays in the cast vote record ([`CommonDataFormatReader.java` 485–512](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/CommonDataFormatReader.java#L485-L512)), so it ends a run of skipped rankings and makes a ranking an overvote when another mark shares it, as the requirements read those provisions |
| `overvoteRule`, `overvoteLabel` | `exhaustImmediately`, `overvote` | §723-A(1)(H) and §4(2)(B)(1) of the rules, in the rules' reading that difference (c) of the review records.  A ballot that reaches a ranking with two or more marks, or with the unnamed overvote, is inactive whether or not the marked candidates continue |
| `maxSkippedRanksAllowed` | `1` | §723-A(1)(D) and (K) and §4(2)(B)(2) and (3), rules 1 and 2 of the interpretation.  RCTab makes a ballot inactive when the ranking that it reaches lies more than two rankings after the last ranking that it read, or after the start, so that two or more empty positions precede it, and it tests this before the overvote ([`Tabulator.java` 1162–1175](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1162-L1175) and [1201–1211](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1201-L1211)).  Trailing empty positions precede no ranking and make no ballot inactive |
| `exhaustOnDuplicateCandidate` | `false` | §4(2)(B)(4).  RCTab passes over a repeated ranking of an eliminated candidate, which still counts as a ranking read for skipped rankings |
| `maxRankingsAllowed` | `max` | §723-A(4)(A), with the review's reading.  RCTab accepts a ranking at every position ([`ContestConfig.java` 1108–1118](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/ContestConfig.java#L1108-L1118)), as the module accepts any number of positions |
| `winnerElectionMode`, `numberOfWinners`, `doesFirstRoundDetermineThreshold`, `nonIntegerWinningThreshold`, `hareQuota` | `singleWinnerMajority`, `1`, `false`, `false`, `false` | §723-A(2)(A).  Each round's threshold is ⌊T/2⌋ + 1 for the round's continuing ballots T, so that of two continuing candidates RCTab elects the one with more votes |
| `batchElimination` | `false` | §723-A(2)(B), since PL 2023 c. 304 repealed batch elimination.  RCTab eliminates one candidate with the fewest votes per round |
| `continueUntilTwoCandidatesRemain` | `true` | §723-A(2), which continues the rounds until two or fewer candidates continue and has no stop at a majority |
| `minimumVoteThreshold`, `cutoffElimination`, `stopTabulationEarlyAfterRound` | `0`, `false`, empty | None.  Each value turns off an elimination or a stop that the statute does not have |
| `decimalPlacesForVoteArithmetic` | `4` | None.  RCTab requires it and uses it only for the fractional transfers of contests with several winners |
| `outputDirectory` | The configuration's file name without `.json` | None.  Tabulations that run at the same time write their results apart |

RCTab's test configuration of the 2018 Democratic primary for Governor, at the tag v2.1.0, sets `maxSkippedRanksAllowed` to 1, `overvoteRule` to `exhaustImmediately`, and `tiebreakMode` to `useCandidateOrder`, as this configuration does.  It also sets `batchElimination`, lists `Write-in` as a candidate, limits the rankings to 8, and leaves `continueUntilTwoCandidatesRemain` off, and [the review](../../../Demos/Rcv/Maine/review.md#departures-of-official-practice) records the first two as practice under the text of 2018.

No setting expresses the provisions of the next table, in which RCTab's count differs from the module's.  `rctab.py compare` predicts RCTab's rounds from the reference's Maine count by each named rule that applies and compares every round with the prediction, so that it reports every difference that no rule states.  Each rule but `initial-test` restates the behavior of the lines of RCTab's source at the tag v2.1.0 that the last column cites.

| Rule | Provision | RCTab | Source at v2.1.0 |
|---|---|---|---|
| None | The four reasons of an inactive ballot | RCTab reports undervotes, the ballots without rankings, and in each round overvotes, skipped rankings, exhausted choices, and repeated rankings.  `compare` compares the undervotes with the reason `blank` of round 1, the overvotes with `overvote`, the skipped rankings with the ballots whose examination ends by rule 1 of the interpretation, which the script states a second time, the exhausted choices with the other ballots of the reasons `exhausted` and `uncounted`, and the repeated rankings with 0 | [`Tabulator.java` 1118–1127](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1118-L1127), [1162–1175](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1162-L1175), and [1256–1259](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1256-L1259), [`OutputWriter.java` 85–89](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/OutputWriter.java#L85-L89) and [1140–1151](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/OutputWriter.java#L1140-L1151) |
| `initial-test` | The initial test of §723-A(2), which ends the count with no rounds | RCTab has no initial test and counts the rounds of the count without it.  T11(c) states that the count without the initial test names the test's winner, and `compare` predicts RCTab's rounds from that count | None |
| `repeated-round` | Rule 2 of the rounds in the round in which a candidate first holds a majority while three or more candidates continue | With `continueUntilTwoCandidatesRemain`, RCTab elects the candidate in that round and eliminates no one, and its next round repeats the round's figures, the winner continuing, and eliminates.  The module's rounds are RCTab's without the electing round, and T11(b) names the same winner | [`Tabulator.java` 212–217](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L212-L217), [241–243](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L241-L243), and [540–544](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L540-L544) |
| `final-tie` | Rule 1 of the rounds for two continuing candidates with equal votes, which eliminates the one later in the order and names the other in the next round | RCTab elects the tied candidate earliest in the list in that round, the same candidate, and its count has one round fewer | [`Tabulator.java` 630–663](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L630-L663), [`Tiebreak.java` 123–143](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tiebreak.java#L123-L143) |
| `one-counted-candidate` | A contest with one counted candidate, which rule 1 of the rounds names in round 1 | With `continueUntilTwoCandidatesRemain`, RCTab tabulates no round and stops with a `NullPointerException` where it reads round 1 to write its reports, and it writes none | [`Tabulator.java` 516–521](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L516-L521) and [855](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L855) |
| `no-ballots` | A contest without ballots | RCTab refuses the contest with the message "No cast vote records found!" and writes no report | [`TabulatorSession.java` 442–444](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/TabulatorSession.java#L442-L444) |
| `no-counted-candidate` | A contest without a counted candidate, which round 1 ends without a winner | RCTab refuses a configuration whose candidates are all excluded, with the message "Contest config must contain at least 1 non-excluded candidate!", and writes no report | [`ContestConfig.java` 693–695](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/ContestConfig.java#L693-L695), [`TabulatorSession.java` 194](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/TabulatorSession.java#L194) |

`rctab.py compare` classifies each comparison as equal, equal under the rules that applied, or different.  Every well-formed file that `edges.py` writes, the edited files that the reader accepts included, and every contest of the corpus ran in the Maine configuration, and no comparison is different.  The table counts the comparisons of the 320 edge files by the rules that applied.

| Result | Edge files |
|---|---|
| Equal | 133 |
| Equal under `final-tie` | 77 |
| Equal under `repeated-round` | 23 |
| Equal under `initial-test` | 6 |
| Equal under `initial-test` and `repeated-round` | 9 |
| Equal under `one-counted-candidate` | 44 |
| Equal under `no-ballots` | 4 |
| Equal under `no-counted-candidate` | 24 |
| Different | 0 |

In 128 of the files RCTab reports skipped rankings, and in every round of each they equal the ballots that rule 1 of the interpretation ends.  Among these files are `marks-end-runs`, in which a write-in's ranking and an excluded candidate's ranking end runs of empty positions, `skip-after-elimination`, in which rule 1 applies only after an elimination, `overvotes`, in which a run of two empty positions precedes a multiple position, and the pattern contests of every ballot of up to four positions.  `final-tie` applies to the tied final pairs, among them `example-maine`, `tie-final`, `tie-final-zero`, and `no-continuing-three`, to 24 exhaustive and 29 random contests, and to the pattern contests, in each of which RCTab elects in the tied round the candidate that the module names one round later.  `initial-test` applies to `initial-test-example`, `test-plus-one`, `shared-identifiers`, `shared-names`, two random contests, and nine edited files, and `repeated-round` to nine of these, in which three or more candidates are counted, to `tie-lowest-reversed`, `shared-batch-nested`, `shared-batch-single-count-majority`, `shared-max-size`, and 19 random contests.  `test-equal`, in which the leading candidate is ranked first alone on exactly half of the ballots, and `test-excluded-majority`, in which an excluded candidate is, are equal without a rule, since the initial test elects no one there.

In the corpus, every round of the six contests equals RCTab's, with no rule.  RCTab elects the summary reports' winners, and in the 2024 contest it gives Golden 197,151 and Theriault 194,445 with 9,473 undervotes, 279 overvotes, 382 skipped rankings, and 1,206 exhausted choices, whose sum, 11,340, is the report's inactive figure.  The 1,206 exhausted choices are the ballots of reason `uncounted`, which rank only write-ins.

| Contest | RCTab's rounds | Winner | Against the reference |
|---|---|---|---|
| 2026 Democratic, Representative to Congress, District 2 | 3 | Dunlap | Equal |
| 2026 Democratic, Governor | 4 | Pingree | Equal |
| 2026 Republican, Governor | 7 | Charles | Equal |
| 2026 Republican, State Senate District 4 | 3 | Perkins | Equal |
| 2026 Republican, House District 58 | 2 | Bridges | Equal |
| 2024 general, Representative to Congress, District 2 | 1 | Golden | Equal |

RCTab ran on Debian 13 on x86-64 under a quota of 200 percent of a CPU and `MemoryMax` of 10 GB for the edge cases, two runs at a time, and of 12 GB for the corpus, one run at a time.  The edge cases took 19 minutes, most of it in the 24 exhaustive contests of `tests/rcv/edges.py`, and the corpus 57 seconds, of which the 2024 contest, the largest, took 24.  The steps below write the inputs, where `RUN` and `CORPUS` are directories and `DIR` is RCTab's installation, and the commands of the RCTab host run after copying `RUN`, `CORPUS`, and `tests/rcv/rctab.sh` there.

```
uv run tests/rcv/maine/edges.py
uv run python -I tests/rcv/maine/check.py
grep -aL '^error ' tmp/rcv-maine-edges/*.report | sed 's/report$/rcv/' | xargs uv run tests/rcv/maine/rctab.py prepare RUN
uv run tests/rcv/maine/rctab.py prepare CORPUS tmp/rcv-maine-data/canonical/*.rcv

# on the RCTab host
systemd-run --user --scope -p CPUQuota=200% -p MemoryMax=10G tests/rcv/rctab.sh batch DIR RUN/runs 2
systemd-run --user --scope -p CPUQuota=200% -p MemoryMax=12G tests/rcv/rctab.sh batch DIR CORPUS/runs 1

# after copying RUN and CORPUS back
while read config results; do
  uv run tests/rcv/maine/rctab.py compare tmp/rcv-maine-edges/${config%-maine.json}.rcv RUN/$config RUN/$results
done < RUN/runs
while read config results; do
  uv run tests/rcv/maine/rctab.py compare tmp/rcv-maine-data/canonical/${config%-maine.json}.rcv CORPUS/$config CORPUS/$results
done < CORPUS/runs
```
