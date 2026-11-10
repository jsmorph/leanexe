# Oakland RCV corpus

This directory holds the test corpus of the ranked-choice tabulator for Oakland, California, and the scripts that fetch and check it.  The corpus covers every Oakland contest on Alameda County's RCV results site from the general election of November 8, 2022 through the general election of November 3, 2026.  For each contest it lists the County's RCV detailed report and, where one exists, D. Otis's standardized cast vote record (CVR), and it adds the Registrar's presentation on the 2022 District 4 error.  [The manifest](manifest.json) gives each file's URL, size, and SHA-256, and [the notice](NOTICE) records each source's terms of use.  The repository holds none of the files.

## Scripts

The Python scripts run from the repository root through `uv run` and use only Python's standard library, and `rctab.sh` runs on the host that runs RCTab.  `fetch.py`, `reports.py`, `recount.py`, `district4.py`, and `check.py` read `tests/rcv/manifest.json` and work in the data directory `tmp/rcv-data`, which Git ignores, unless the command names another.  Each script's docstring or header states its rules and its exit status.

| File | Command | Behavior |
|---|---|---|
| [`fetch.py`](fetch.py) | `uv run tests/rcv/fetch.py [DIR] [--no-cvr]` | Downloads each file of the manifest to its path under `DIR`, one request at a time with a two-second pause, and keeps a present file whose size and SHA-256 match.  A download that does not match stays beside its target as `PATH.mismatch`, the script prints the expected and the received size and digest, and the exit status is 1.  `--no-cvr` skips the CVRs, about 194 MB. |
| [`reports.py`](reports.py) | `uv run tests/rcv/reports.py [DIR]` | Parses each report, checks that its tallies, inactive categories, and transfers agree within and between rounds, writes `DIR/normalized/<election>/<race>.json`, and prints the table of [the corpus](#corpus). |
| [`recount.py`](recount.py) | `uv run tests/rcv/recount.py [KEY ...] [--suspend] [--data DIR]` | Recounts each contest that has a CVR, or the contests named by their manifest keys, and prints each round that differs from the report and a summary line per contest ([Recount](#recount)). |
| [`district4.py`](district4.py) | `uv run tests/rcv/district4.py [--data DIR]` | Checks the 2022 District 4 counts against the County's figures ([District 4](#district-4)) and exits with status 1 on a difference. |
| [`convert.py`](convert.py) | `uv run tests/rcv/convert.py CVR [--report XML] [--contest ID] [--order I ...] [--no-ids] [--out FILE]` | Writes the canonical ballot file of a CVR ([The converter](#the-converter)). |
| [`dominion.py`](dominion.py) | `uv run tests/rcv/dominion.py EXPORT [CONTEST] [--contest ID] [--order I ...] [--no-ids] [--out FILE]` | Writes the canonical ballot file of one contest of a Dominion CVR export, a directory or a zip archive ([The Dominion converter](#the-dominion-converter)). |
| [`dominion_check.py`](dominion_check.py) | `uv run tests/rcv/dominion_check.py [--data DIR] [--scratch DIR] [--fetch]` | Converts the Alaska exports and compares them with the Division's reports, and runs the synthetic, malformed, and planted-error tests of the Dominion converter ([The Dominion converter](#the-dominion-converter)). |
| [`reference.py`](reference.py) | `uv run tests/rcv/reference.py [--single \| --county \| --suspend \| --contest-words \| --result-words] FILE` | Prints the report of a canonical file, or writes the count's word forms ([The reference](#the-reference)). |
| [`edges.py`](edges.py) | `uv run tests/rcv/edges.py [OUT]` | Writes the edge cases with the reference's outputs into `OUT`, `tmp/rcv-edges` by default, and checks the reference against the expectations stated by hand ([Edge cases](#edge-cases)). |
| [`reader_edges.py`](reader_edges.py) | `uv run tests/rcv/reader_edges.py [OUT]` | Writes edge cases of the reader with the reference's reports into `OUT`, `tmp/rcv-reader` by default: an absent line and a final run without LF in each role from `contest` to `ballot`, numbers of up to 21 digits next to 2^32 and 2^64 in each place that holds a number, and names of spaces alone ([the reader](../../Demos/Rcv/README.md#the-reader)) |
| [`check.py`](check.py) | `uv run tests/rcv/check.py [--data DIR]` | Converts each CVR, checks the converter and the reference against the requirements and the County's reports, writes `DIR/canonical`, and runs the planted errors ([Checks](#checks)). |
| [`compare.py`](compare.py) | `uv run tests/rcv/compare.py [--module PATH] [--host PATH] [--spec PATH] DIR ...` | Computes the reference's result words for each word array `NAME.words` of each directory and compares them with the module's export `count`, `rcv-spec array`, `rcv-spec program`, and `NAME.result`, and exits with status 1 on a disagreement ([the tests of the count over words](../../Demos/Rcv/README.md#testing-the-count-over-words)) |
| [`tabulate.py`](tabulate.py) | `uv run tests/rcv/tabulate.py [--module PATH] [--host PATH] [--tabulate PATH] DIR ...` | Computes the reference's report of each canonical file `NAME.rcv` of each directory and compares it with the module's export `tabulate`, `rcv-tabulate report`, and `NAME.report`, and exits with status 1 on a disagreement ([the tests of the tabulator](../../Demos/Rcv/README.md#testing-the-tabulator)) |
| [`variants.py`](variants.py) | `uv run tests/rcv/variants.py [--stability PATH] DIR ...` | Compares the round lines and the winner line of the count, the single count, and the county count that `rcv-stability rounds` writes for each word array `NAME.words` of each directory with the reference's, and exits with status 1 on a disagreement ([the stability tests](../../Demos/Rcv/README.md#stability-batches-and-the-county-count)) |
| [`rctab.sh`](rctab.sh) | `tests/rcv/rctab.sh install DIR`, `selftest DIR WORK`, `run DIR CONFIG OUT`, or `batch DIR LIST JOBS` | Installs RCTab at its pinned release, runs RCTab's own test contest, tabulates a configuration and collects RCTab's reports, or tabulates each configuration of a list, several at once ([RCTab](#rctab)). |
| [`rctab.py`](rctab.py) | `uv run tests/rcv/rctab.py prepare RUN FILE ... [--date DATE] [--jurisdiction TEXT] [--office TEXT]` or `compare FILE CONFIG RESULTS [--county XML]` | Writes canonical files as RCTab's input with their configurations, or compares RCTab's rounds with the reference's and the County's ([RCTab](#rctab)). |

A normalized report holds the report's title fields (`election_name`, `election_date`, `status`, `contest`, `timestamp`), every attribute of its settings element verbatim in `settings`, the candidates in the report's order, and one object per round.  A round holds each candidate's tally, the counts `blanks`, `overvotes`, `exhausted`, `suspended`, `continuing`, and `non_transferable`, the candidates that the report eliminates or elects in the round or defeats in its final round, and the transfers that the round lists.  The member `charter` applies [the charter's rules](#charter-rules) to the published tallies.  It gives `majority_round`, the charter's rounds with the report round that each one corresponds to, the charter's `stop`, its `batches`, and `first_batch_round`.

## Sources

Alameda County publishes each report at `https://www.alamedacountyca.gov/rovresults/rcv/<election>/<race>/RcvDetailedReport.xml`, in the XML form of Dominion's RCV detailed report.  The County numbers the elections: 248 for November 8, 2022, 253 for the Oakland Unified School District, District 5, special election of November 7, 2023, 251 for the primary of March 5, 2024, which held a short-term City Auditor contest, 252 for November 5, 2024, 257 for the special municipal election of April 15, 2025, and 260 for November 3, 2026.  The reports of election 260 are marked "PRELIMINARY/UNOFFICIAL - POST ELECTION UPDATE #2" and time-stamped 2026-11-09.  Their digests change with each update until certification, and `fetch.py` then fails for them and prints the new sizes and digests for the manifest.

D. Otis's dataset on Harvard Dataverse, version 25, holds one CSV per contest with ballot fields and the columns `rank1` to `rank5`.  A ranking holds a candidate's name, `skipped`, `overvote` without the candidates marked, or `Write-in` for any write-in.  The dataset has no file for the 2022 City Council, District 2, contest, the 2023 and March 2024 contests, or the 2026 contests.  The County releases its own CVRs of the corpus's elections only on request, as [the notice](NOTICE) records.

The Registrar's presentation "Ranked-Choice Voting Tally, November 8, 2022 – General Election" gives the originally certified District 4 count in Table A of slide 6 and the distribution of the ballots that the 2022 configuration suspended on slide 5.  The tables of both slides are images, so `district4.py` holds their figures as constants and compares its counts with them.

## Corpus

| Election | Contest | Candidates | Rankings | CVR | CVR ballots | Report ballots | Elimination | Suspension | Previous rounds | Threshold stop | Report rounds | Majority round | Charter stop (charter round) | First batch (size) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 248 (2022-11-08) | Mayor | 10 | 5 | Otis | 133,527 | 133,527 | Single | True | False | False | 9 | 9 | 9 (4) | 1 (3) |
| 248 (2022-11-08) | City Council, District 2 | 2 | n/a | none | n/a | 17,851 | Single | True | False | False | 1 | 1 | 1 (1) | none |
| 248 (2022-11-08) | City Council, District 4 | 2 | 5 | Otis | 30,983 | 30,983 | Single | True | False | False | 1 | 1 | 1 (1) | none |
| 248 (2022-11-08) | City Council, District 6 | 4 | 5 | Otis | 16,903 | 16,903 | Single | True | False | False | 3 | 1 | 1 (1) | none |
| 248 (2022-11-08) | City Auditor | 1 | 5 | Otis | 133,527 | 133,527 | Single | True | False | True | 1 | 1 | 1 (1) | none |
| 248 (2022-11-08) | School Director, District 2 | 3 | 5 | Otis | 17,851 | 17,851 | Single | True | False | False | 2 | 1 | 1 (1) | none |
| 248 (2022-11-08) | School Director, District 4 | 3 | 5 | Otis | 30,983 | 30,983 | Single | False | False | False | 2 | 2 | 2 (2) | none |
| 248 (2022-11-08) | School Director, District 6 | 3 | 5 | Otis | 16,898 | 16,898 | Single | True | False | False | 2 | 2 | 2 (2) | none |
| 253 (2023-11-07) | School Director, District 5 | 2 | n/a | none | n/a | 3,590 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 251 (2024-03-05) | City Auditor, Short Term | 1 | n/a | none | n/a | 88,531 | Single | False | False | True | 1 | 1 | 1 (1) | none |
| 252 (2024-11-05) | City Council, At Large | 10 | 5 | Otis | 173,002 | 173,010 | Single | False | False | False | 9 | 9 | 9 (5) | 3 (5) |
| 252 (2024-11-05) | City Council, District 1 | 3 | 5 | Otis | 35,257 | 35,257 | Single | False | False | False | 2 | 1 | 1 (1) | none |
| 252 (2024-11-05) | City Council, District 3 | 6 | 5 | Otis | 24,597 | 24,597 | Single | False | False | False | 5 | 4 | 5 (2) | 1 (4) |
| 252 (2024-11-05) | City Council, District 5 | 3 | 5 | Otis | 14,752 | 14,752 | Single | False | False | False | 2 | 1 | 1 (1) | none |
| 252 (2024-11-05) | City Council, District 7 | 4 | 5 | Otis | 15,874 | 15,876 | Single | False | False | False | 3 | 3 | 3 (3) | none |
| 252 (2024-11-05) | City Attorney | 2 | 5 | Otis | 173,002 | 173,010 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 252 (2024-11-05) | School Director, District 1 | 2 | 5 | Otis | 35,367 | 35,367 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 252 (2024-11-05) | School Director, District 3 | 2 | 5 | Otis | 24,632 | 24,632 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 252 (2024-11-05) | School Director, District 5 | 2 | 5 | Otis | 14,806 | 14,806 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 252 (2024-11-05) | School Director, District 7 | 2 | 5 | Otis | 15,301 | 15,301 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 257 (2025-04-15) | Mayor | 10 | 5 | Otis | 95,033 | 95,046 | Single | False | False | False | 9 | 1 | 1 (1) | none |
| 257 (2025-04-15) | City Council, District 2 | 6 | 5 | Otis | 13,097 | 13,097 | Single | False | False | False | 5 | 4 | 5 (2) | 1 (4) |
| 260 (2026-11-03) | Mayor | 4 | n/a | none | n/a | 149,688 | Single | False | False | False | 3 | 1 | 1 (1) | none |
| 260 (2026-11-03) | City Council, District 2 | 2 | n/a | none | n/a | 19,828 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 260 (2026-11-03) | City Council, District 4 | 1 | n/a | none | n/a | 32,546 | Single | False | False | True | 1 | 1 | 1 (1) | none |
| 260 (2026-11-03) | City Council, District 6 | 2 | n/a | none | n/a | 19,105 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 260 (2026-11-03) | City Auditor | 1 | n/a | none | n/a | 149,688 | Single | False | False | True | 1 | 1 | 1 (1) | none |
| 260 (2026-11-03) | School Director, District 2 | 2 | n/a | none | n/a | 19,893 | Single | False | False | False | 1 | 1 | 1 (1) | none |
| 260 (2026-11-03) | School Director, District 4 | 3 | n/a | none | n/a | 32,663 | Single | False | False | False | 2 | 2 | 2 (2) | none |
| 260 (2026-11-03) | School Director, District 6 | 3 | n/a | none | n/a | 19,156 | Single | False | False | False | 2 | 2 | 2 (2) | none |

`reports.py` prints the table.  Candidates counts the report's candidates, and no Oakland report lists a write-in candidate.  Rankings counts the CVR's ranking columns.  The ballot columns give the CVR's lines and the report's round-1 sum of continuing and non-transferable ballots.  Elimination, Suspension, Previous rounds, and Threshold stop are the report's `eliminationType`, `useFirstRoundSuspension`, `previousRoundsEvaluation`, and `winnersByThreshold`, and Suspension is the 2022 setting that withheld ballots with a blank first ranking from round 1.  Majority round is the first report round in which a candidate holds more than half of the continuing ballots.  Charter stop is the report round at which the charter's count stops, with the charter's own round number in parentheses, and First batch is the report round of the first batch that §1105(f) eliminates, with its size.  The last three columns come from the published tallies, whose round 1 omits the suspended ballots wherever Suspension is True.

## Recount

`recount.py` counts each ballot for its first ranked continuing candidate.  It passes over skipped rankings, `Write-in` rankings, and rankings of eliminated candidates, and a ballot that reaches an `overvote` ranking first is an overvote from then on.  A ballot without a candidate or overvote mark is a blank, and every other inactive ballot is exhausted.  Each round eliminates the candidate that the report eliminates, and the script checks that this candidate has the fewest votes in the recount.  With `--suspend`, round 1 sets aside as suspended every ballot whose first ranking is skipped or a write-in and that has a later candidate or overvote mark.

| Contest | Suspension | Report rounds | Rounds equal without `--suspend` | Rounds equal with `--suspend` | Report ballots missing from the CVR |
|---|---|---|---|---|---|
| 2022 Mayor | True | 9 | 2 to 9 | all | 0 |
| 2022 City Council, District 4 | True | 1 | none | all | 0 |
| 2022 City Council, District 6 | True | 3 | 2 and 3 | all | 0 |
| 2022 City Auditor | True | 1 | none | all | 0 |
| 2022 School Director, District 2 | True | 2 | 2 | all | 0 |
| 2022 School Director, District 4 | False | 2 | all | 2 | 0 |
| 2022 School Director, District 6 | True | 2 | 2 | all | 0 |
| 2024 City Council, At Large | False | 9 | none | none | 8 |
| 2024 City Council, District 1 | False | 2 | all | 2 | 0 |
| 2024 City Council, District 3 | False | 5 | all | 2 to 5 | 0 |
| 2024 City Council, District 5 | False | 2 | all | 2 | 0 |
| 2024 City Council, District 7 | False | 3 | none | none | 2 |
| 2024 City Attorney | False | 1 | none | none | 8 |
| 2024 School Director, District 1 | False | 1 | all | none | 0 |
| 2024 School Director, District 3 | False | 1 | all | none | 0 |
| 2024 School Director, District 5 | False | 1 | all | none | 0 |
| 2024 School Director, District 7 | False | 1 | all | none | 0 |
| 2025 Mayor | False | 9 | none | none | 13 |
| 2025 City Council, District 2 | False | 5 | all | 2 to 5 | 0 |

Under the rule that a report's own suspension setting names, the recount equals every round of every report whose CVR holds all of the report's ballots.  The CVRs of the 2024 At-Large, City Attorney, and District 7 contests and of the 2025 Mayor contest lack a few of the report's ballots.  In every round of those contests, each candidate's tally and each inactive category of the report equals or exceeds the recount's, and the excesses sum to the missing ballots.  The County's first JSON release of 2024 CVRs, on November 15, 2024, redacted precincts with few voters, according to the County of Alameda Elections Commission's agenda of November 21, 2024.  The dataset does not state which release its files come from.

## Charter rules

Charter §1105(a)(3) and (d)(2) declare the winner after any round in which a candidate receives more than half of the votes from continuing ballots, and a continuing ballot is one that counts for some candidate.  §1105(f) eliminates at once all candidates with fewer votes than a candidate whose votes exceed their combined total.  `reports.py` reads the test for each continuing candidate, with the set of candidates holding strictly fewer votes, and eliminates the largest qualifying set of two or more candidates.  A single-elimination count removes the members of such a set first, one per round, because each member has fewer votes than every candidate outside the set.  The charter's round after a batch of k candidates at report round r therefore corresponds to report round r + k, and `reports.py` checks that the report eliminates the batch's members in rounds r to r + k − 1.  No round of the corpus has a tie for last place.

## Where the charter and the reports differ

The County's reports continue until one candidate remains, and §1105(d)(2) stops the count at a majority.  The charter's count stops before the report's last round in the 2022 City Council, District 6, contest (Jenkins, round 1 of 3), the 2024 City Council, District 1 and District 5, contests (round 1 of 2), the 2025 Mayor contest (Lee, 47,177 of 94,305 continuing ballots, round 1 of 9), and the preliminary 2026 Mayor contest (round 1 of 3).  In the 2022 School Director, District 2, contest, the published round 1, which omits 135 suspended ballots, gives Brouhard 7,463 of 14,924 continuing ballots, a majority.  The recount's round 1 gives her 7,509 of 15,048, short of a majority, so the charter's count stops at round 2, the report's last.  In every contest the charter's winner is the report's winner.

§1105(f) eliminates a batch in rounds where the County eliminates one candidate per round.  The table gives each batch with the published tallies, and with the recount's tallies in parentheses where they differ.  The County's count reaches the charter's next round once it has eliminated the batch's last member, so the charter's count has fewer rounds than the report.

| Contest | Report round | Batch | Combined votes | Next candidate | Charter rounds against report rounds |
|---|---|---|---|---|---|
| 2022 Mayor | 1 | Jordan, Liu, Reimann | 3,091 (3,139 in the recount) | Scott, 3,745 (3,789) | 4 against 9 |
| 2022 Mayor | 5 | Hodge, Reid, Villanueva, De La Fuente | 40,893 | Thao, 41,079 | |
| 2024 City Council, At Large | 3 | Robinson, Pechenuk, Tostado, Matoury, Danino | 30,253 | Wang, 31,161 | 5 against 9 |
| 2024 City Council, District 3 | 1 | Hirsch, Semedar, Hailey, Afolabi | 4,574 | Logan, 6,262 | 2 against 5 |
| 2025 City Council, District 2 | 1 | Anderson, Thomas, Matoury, Lowe | 2,455 | Murray-Badal, 4,223 | 2 against 5 |

In the 2024 District 3 and 2025 District 2 contests, a candidate first holds a majority in report round 4, inside the span of the round-1 batch.  Fife holds 10,643 of 20,039 continuing ballots and Wang 6,272 of 12,309.  The charter's count passes from report round 1 to report round 5, where the same candidates hold majorities, so its stop falls one report round after the report's first majority.

## District 4

`district4.py` counts the 2022 School Director, District 4, contest from the CVR with the rules of [Recount](#recount), eliminating the candidate with the fewest votes until two remain.  The count equals both rounds of the report that the County re-ran on 2023-03-10: Hutchinson 8,227, Manigo 8,190, and Resnick 10,015, with 4,403 blanks and 148 overvotes, in round 1, and Hutchinson 12,421 and Resnick 12,165, with 173 overvotes and 1,821 exhausted, in round 2.  With the first-round suspension, the count suspends 235 ballots and gives Hutchinson 8,112, Manigo 8,153, and Resnick 9,954 in round 1, and Manigo 11,753 and Resnick 12,352 in round 2.  These figures equal Table A of the Registrar's presentation, the count the County certified first.  Under the correct rules, the 235 suspended ballots count 115 for Hutchinson, 37 for Manigo, and 61 for Resnick, and 22 are overvotes, as slide 5 shows.  Counting the aggregate write-in as a candidate gives Hutchinson 8,147, Manigo 8,176, Resnick 9,977, and the write-in 269 in round 1, which differs from both reports.

## The converter

`convert.py` writes the canonical ballot file of [the requirements](../../Demos/Rcv/requirements.md#the-canonical-ballot-file) from one of D. Otis's CVRs.  With `--report`, the candidates are the report's in the report's order, each of kind `listed`, followed by `Write-in` of kind `aggregate-writein`.  Without it, the listed candidates are the CVR's distinct names in increasing order of their UTF-8 bytes, so that the header does not depend on the order of the rows.  The CVR's `Write-in` rankings name no one, and no report of the corpus lists a write-in candidate, so the converter writes no `named-writein` or `excluded` candidate.  It writes the aggregate write-in whether or not the CVR ranks it, since an Oakland ballot lets every voter rank a write-in under §1105(c), and the header then depends on the report alone.  The tie-break order is `--order` or 1 to `n`, and the contest identifier is `--contest` or the CVR's file name without its extension, such as `Oakland_20221108_SchoolBoardD4`.

Each row of the CVR gives one ballot line, whose identifier is the row's `ballotID` unless `--no-ids` is given.  The ranking `skipped` gives an empty field, `overvote` gives `*`, since the CVR does not name the candidates marked, and a candidate's name or `Write-in` gives its index.  The converter refuses a CVR that the file cannot represent, with a message on standard error and exit status 1: ranking columns other than `rank1` to `rankk` with `k` from 1 to 63, a row whose length differs from the header's, a ranking that names a candidate absent from the report, more than 63 candidates, a name or an identifier outside its alphabet or length, a repeated name, an order that is not a permutation, more than 2^32 − 1 ballots, or a file that is not UTF-8.

## The Dominion converter

`dominion.py` writes the canonical ballot file of one contest from the JSON form of the cast vote record export of Dominion's Democracy Suite, the system of Alameda County, San Francisco, and the State of Alaska.  The export is a directory, or a zip archive of one, that holds manifests of the contests, candidates, outstack conditions, and other items, and the records in `CvrExport.json` or in files `CvrExport_N.json`.  `dominion.py EXPORT` lists each contest with rankings by its manifest Id, number of rankings, number to elect, and description, and `dominion.py EXPORT CONTEST` converts the contest whose Id is `CONTEST`.  The candidates are the contest's entries of the candidate manifest in the manifest's order, under their descriptions, and the manifest's types give their kinds: `Regular` gives `listed`, `QualifiedWriteIn` gives `named-writein`, and `WriteIn`, or `Writein` as the format document spells it, gives `aggregate-writein`.  `--order`, `--no-ids`, and `--out` act as in `convert.py`, and the contest identifier is `--contest` or the export's file name without its extension, a hyphen, and the Id.  The script's docstring lists the exports that it refuses with a message on standard error and exit status 1.

The format document is Dominion's ["CVR export file format"](https://web.archive.org/web/20250826234510/https://www.sfelections.org/results/20221108/data/N22_DSuite_CVRExportFormat.pdf), a Word document printed to PDF on 2020-10-21, which San Francisco published beside the CVR export of its election of November 8, 2022.  San Francisco's site answers scripted requests with HTTP 403, so the manifest pins the Internet Archive's copy of 2025-08-26, and the tests read no San Francisco export.  The exports read are the State of Alaska's for the special general election of August 16, 2022, written by Democracy Suite 5.5.52.6, and for the general elections of November 8, 2022 and November 5, 2024, written by 5.5.52.6 and 5.17.18.1, from [the Division of Elections' results pages](https://www.elections.alaska.gov/election-results/).  The table gives the converter's reading of each case, the document's statement, and, where the document does not settle the case, the evidence of these exports and of [RCTab's Dominion reader at v2.1.0](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/DominionCvrReader.java).

| Case | Format document | Converter |
|---|---|---|
| CVR files | The option SplitFilesPerBatch writes one file per batch | Reads `CvrExport.json`, or each `CvrExport_N.json` in increasing order of `N`, whose values in the 2024 export start at 18 and have gaps.  Refuses an export with both forms |
| Session | TabulatorId, BatchId, "unique for a given tabulator id", and RecordId, "the CVR id within the batch" | Writes one ballot line for each session whose current element lists the contest, with the three numbers joined by hyphens as its identifier, as RCTab does.  Refuses a repeated triple |
| Original and Modified | Original holds "the original state of the CVR data", Modified, when present, "the modified state", and IsCurrent is true for the element that "represents the current state" | Reads the element whose IsCurrent is true, as RCTab does, and refuses a session with none or two.  Modified is current in 172 sessions of the 2022 special general and 484 of the 2022 general |
| Cards | The element lists the contests | The exports of both versions list the contests in the element's list `Cards`, and each of their sessions holds one card.  The converter reads both forms, writes a line for the card that lists the contest, and refuses a session in which two cards list it |
| Contest not listed, or listed without marks | The element lists "all contests for the current ballot type" | No line for a session without the contest, and a blank ballot for a listed contest without marks |
| Outstack condition InvalidContest | Absent from the document.  The outstack condition manifest of 5.17.18.1 gives it the Id 7, and that of 5.5.52.6 omits it | No line.  In the 2024 export, 4,925 of the 340,778 sessions carry it on the U.S. Representative contest, and the Division's report counts 335,853 ballots, the difference.  RCTab also skips these contests |
| Other outstack conditions | Overvotes, undervotes, blank contests, write-ins, skipped and duplicated rankings, and others | Not read, since they describe the marks, which the converter reads |
| Ambiguous mark | IsAmbiguous states "whether mark is ambiguous" | Passed over, as RCTab does.  Every ambiguous mark of the exports, in Original and Modified elements alike, has IsVote false |
| IsVote | "Any mark above the max threshold will be true in a ranked choice voting contest" | Not read.  The 5.17.18.1 export follows the document, but in the 5.5.52.6 export of the special general IsVote is true only for the single mark of a first ranking that holds one mark |
| Mark | CandidateId and Rank, among other attributes | Marks the candidate at the position of the rank, so that a position with two or more marks names its candidates and the converter never writes the unnamed overvote `*`.  Refuses a rank outside 1 to NumOfRanks, a candidate of another contest, and a candidate marked twice at one rank |
| Write-in | A write-in mark names the contest's write-in candidate, or a qualified write-in candidate once the write-in "is resolved" | The candidate's kind, `aggregate-writein` or `named-writein`.  No Alaska export holds a qualified write-in |
| Contest and candidate types | VoteFor is the number to elect, NumOfRanks the rankings allowed, and the candidate types are Regular, Writein, NoPreference, and QualifiedWriteIn | Refuses VoteFor other than 1, NumOfRanks outside 1 to 63, and the type NoPreference, which have no place in the canonical file |
| `Configuration.json` | Records the export's filters by tabulator, batch, precinct portion, ballot type, and contest | Not read.  An export made with a filter, or with the suppression of low-turnout precincts that 5.17.18.1 records there, holds part of a contest, and the converted file then holds that part |

The Division counts under [AS 15.15.350](https://www.akleg.gov/basis/statutes.asp#15.15.350) and [6 AAC 25.071 and 25.072](https://www.akleg.gov/basis/aac.asp#6.25.071).  Subsection (d) elects a candidate who holds a majority in the first round and otherwise defeats the candidate with the fewest votes until two remain, (e)(1) makes a ballot inactive at an overvote, and (e)(2) makes it inactive "once the second skipped ranking is encountered", where a skipped ranking is a blank ranking followed by a ranked candidate.  6 AAC 25.071 defeats every write-in candidate before the tabulation when the ballots that rank write-ins highest trail the leading candidate's by at least 0.5 percent, and 25.072 counts a candidate's highest ranking and disregards the others.  No contest below has a first-round majority, so the reference's county count follows (d), its interpretation follows (e)(1), and it passes over the aggregate write-in, which no report lists, as it passes over a defeated candidate.  It departs from (e)(2), which the charter does not have.  `dominion_check.py` therefore compares each contest twice: the county count of the converted file against the report's eliminations, winner, and figures, and the county count after the script rewrites each ballot by 25.072 and (e)(2), which must equal every figure.  The rewrite empties each later ranking of a candidate and then, at the second of two sequential empty positions followed by a mark, empties that position and every later one.  The report's categories map as in Alameda County's: Blanks is `blank` plus `uncounted`, Overvotes `overvote`, and Exhausted `exhausted`.

| Contest | Ballots | Rounds and winner | County count against the report | Ballots that 25.072 and (e)(2) change | After the rewrite |
|---|---|---|---|---|---|
| 2022 special general, U.S. Representative | 192,289 | 2, Peltola | Same eliminations and winner.  Every figure but round 1's Exhausted differs, by 20 to 159 ballots | 4,097 and 687 | Equal |
| 2022 general, U.S. Senator | 266,797 | 3, Murkowski | The same, by 12 to 184 ballots | 3,175 and 1,340 | Equal |
| 2022 general, U.S. Representative | 266,797 | 3, Peltola | The same, by 4 to 140 ballots | 2,640 and 1,050 | Equal |
| 2024 general, U.S. Representative | 335,853 | 3, Begich | The same, by 11 to 162 ballots | 5,186 and 1,874 | Equal |

The county count gives more votes and overvotes and fewer Blanks and Exhausted than the reports, because it counts the ballots that (e)(2) makes inactive.  A ballot that (e)(2) makes inactive before it counts for anyone appears among the reports' Blanks, which the rewrite reproduces as `blank` or `uncounted`.  The rewrite reads a ranking that 25.072 disregards as blank, so that `1,1,1,2` becomes inactive when candidate 1 is defeated.  Without that reading, the figures of the 2022 special general differ from the report's by 1 or 2 ballots in round 1 and by up to 28 in round 2.

`dominion_check.py` also writes synthetic exports into a scratch directory, `tmp/rcv-dominion-tests` by default.  A well-formed export covers a current Modified element, a current Original beside a Modified element, an ambiguous mark, marks with IsVote false, a named overvote, both write-in kinds, an invalid contest, a session without the contest, a contest on a session's second card, an element without `Cards`, a blank contest, and `CvrExport_9.json` before `CvrExport_10.json`, and the script compares the converter's output with lines stated by hand, for a zip archive, a directory, an archive whose files lie in a subdirectory, and one `CvrExport.json` with a byte order mark.  Each of 38 malformed exports must give exit status 1 and its own message.  For each Alaska contest the script converts the export, writes the file and the reference's county report under `DATA/canonical`, and checks the round trip: the reference reads the file back to the manifest's candidates and to the identifiers and marks of the export's sessions, read again by the script without the converter, and the reference's writer reproduces the file.  Each planted error is a copy of `dominion.py` with one change, and each must fail the comparison after the rewrite for the contests in the table, so that the reports reject each alternative reading.

| Planted error | Contests whose comparison fails |
|---|---|
| Ambiguous marks read as marks | All four |
| The Original element read whatever IsCurrent says | The three of 2022, which hold current Modified elements |
| Invalid contests written | 2024 |
| Marks whose IsVote is false passed over | The three of 2022, whose exports come from 5.5.52.6 |

The manifest's `dominion` section pins each export, report, and the format document by URL, date, size, and SHA-256, and `--fetch` downloads them into `tmp/rcv-dominion-data`.  The Division's server does not send the intermediate certificate that issued its own, so `--fetch` adds GlobalSign's certificate, pinned in the same section, to the system's roots for its requests.  The Division publishes the 2024 report only as a PDF, whose figures the script holds, and the 2022 reports as tab-separated UTF-16 text, which it parses.  The script prints `56 checks, 0 failing` and one line per contest and planted error, and it took about three minutes on a four-core host.

```
uv run tests/rcv/dominion_check.py --fetch
uv run tests/rcv/dominion.py tmp/rcv-dominion-data/alaska/22GENR/CVR_Export.zip
uv run tests/rcv/dominion.py tmp/rcv-dominion-data/alaska/22GENR/CVR_Export.zip 3 --contest AK-20221108-USSen --out FILE
```

## The reference

`reference.py` transcribes the reader of the canonical file with its error report, the writer, the interpretation of a ballot, the rounds, the report, and the count's word forms from [the requirements](../../Demos/Rcv/requirements.md) alone, without the Lean specification.  `reference.py FILE` prints the report of the charter's count, or the error report of a malformed file, with exit status 0 in both cases, as the module returns either report.  `--contest-words` writes the contest's words and `--result-words` reads contest words and writes the count's, each as little-endian 64-bit words.

`--single` gives the single count, the charter's count without rule 3, with which the requirements' T10 compares the charter's count.  `--county` gives the county count, with which T11 compares it, and `--suspend` the faulty setting of the 2022 case study, both of which the requirements also define for comparisons with the County's reports.  No module carries any of the three.  Their reports have the report's form with the rule lines `rule single-count`, `rule alameda-county-count`, and `rule alameda-county-count first-round-suspension`, so that none can be taken for the charter's report.  The faulty setting adds the line `inactive suspended x` after the other inactive lines of each round.

`--maine` gives the report of [the Maine module](../../Demos/Rcv/Maine/requirements.md), and with `--result-words` its words, transcribed from the Maine requirements alone with the same reader, writer, tally, and printer.  `--contest-words` gives the same words with or without it, and it cannot be combined with `--single`, `--county`, or `--suspend`.  [The Maine corpus](maine/README.md) describes the Maine edge cases, the converter of the Secretary of State's spreadsheets, and the checks of the Maine count against the summary reports.

## Edge cases

`edges.py` writes the edge cases of the requirements' Tests section into a directory.  A well-formed case `NAME` gives `NAME.rcv`, the reference's report `NAME.report`, and the contest's and the count's words `NAME.words` and `NAME.result`.  A malformed case gives `NAME.rcv` and its error report, and a case of the word forms alone gives `NAME.words` and `NAME.result`.  Running the script again writes the same bytes.

| Cases | Content |
|---|---|
| Hand-stated contests | The worked example; every reason; overvotes, named and unnamed, at each position; duplicate rankings; every kind of candidate; ties at the fewest votes among three candidates and in the final round, under both orders; batches at the boundary of the strict test, where the votes equal the sum and exceed it by one, with tied members, nested, and inside which the single count reaches a majority; every ballot inactive; no ballots; one candidate with and without a continuing ballot; no counted candidate; 63 candidates and 63 positions; identifiers of 1 and 64 bytes and the blank ballot with an identifier; names with spaces at either end, commas, bars, stars, every byte from `0x20` to `0x7E` and from `0x80` to `0xFF`, and 255 bytes; the two contests of T15; and a contest whose ballots the faulty setting suspends in each way |
| Exhaustive contests | Every ballot of `k` positions, for `k` from 1 to 4, over the fields empty, each of five candidates of all four kinds, `1\|3`, `2\|4`, and `*`, under each of the six orders of the counted candidates |
| Random contests | 220 seeded contests of up to 12 candidates of every kind, 6 positions, and 2,000 ballots, with identifiers on about three lines in ten |
| Malformed files | A failure of each role: leading zeros, an index of 0 or above `n`, decreasing and repeated indices, too few and too many fields, an empty identifier, identifiers and contest identifiers of 65 bytes or with a byte outside the alphabet, names of 0 and 256 bytes or with `0x09` or `0x7F`, a carriage return, a NUL, a missing final LF, ballot counts above and below the number of lines, a bad line before the missing ones, an empty line after the last ballot when `k` is 1, and bytes without LF after the last line |
| Edited files | 300 seeded edits of one to three bytes of the hand-stated files |
| Word arrays | Invalid arrays of every kind that the requirements list, each with the result `[0]`, and one valid array |

The hand-stated contests, the malformed files, and the word arrays carry the report lines, the error line, or the result words that the reference's author derived by hand from the requirements before running the reference on them.  The script checks the reference against them, checks that the writer reproduces every file that the reader accepts, which is T2(b), and checks that each result array describes the rounds of the report.  It prints `268 well-formed files, 64 malformed files, 300 edited files of which the reader accepts 15, 17 word arrays, 105 with hand-stated expectations, 0 failing`.  A scratch test of the same kind on 200,000 edited files found T2(a) and T2(b) to hold on the 36,511 that the reader accepts.

## Checks

`check.py` converts each of the 19 CVRs with the report's candidates and the order 1 to `n`, writes the file under `DATA/canonical` with the reference's report, contest words, and result words, and runs the checks of the table on the reference.  Each check takes its expected values from a source other than the reference.  Where a CVR lacks ballots of the report, a compared round passes when each of the County's figures equals or exceeds the reference's and the excesses sum to the missing ballots, which is the statement of [Recount](#recount) made into a check.

| Check | Expected values | Result |
|---|---|---|
| Rule identifier | The requirements' block | Equal |
| Worked example | The requirements' report | Equal byte for byte |
| District 4 | The requirements' rounds of the converted CVR | Equal byte for byte |
| Table A | The faulty setting on District 4 against `district4.py`'s figures of Table A | Equal: Hutchinson 8,112, Manigo 8,153, Resnick 9,954, and 235 suspended, then Manigo 11,753 and Resnick 12,352 |
| Edge cases | The expectations stated by hand | All 646 pass |
| Round trip | The CVR's identifiers and rankings, read back from the canonical file by the reference, and the reference's writer on the file | All 19 contests and their 1,015,392 ballots |
| Charter count | The County's report by the requirements' comparison rule, for the 13 reports without the 2022 suspension | 9 contests exact and the 4 short CVRs within their missing ballots |
| Charter count | The County's winner, for the 6 reports with the suspension | Equal |
| County count | Every round of the 13 reports without the suspension | 9 contests exact and the 4 short CVRs within their missing ballots |
| Faulty setting | Every round of the 6 reports with the suspension, Suspended included | Equal |

In the charter's counts of the CVRs, the 2022 mayoral contest eliminates Jordan, Liu, and Reimann in round 1 and Hodge, Reid, Villanueva, and De La Fuente in round 3, and it elects Thao in round 4.  The 2024 at-large contest eliminates five candidates in round 3 and elects Brown in round 5 with 72,313 votes against Armstrong's 54,776, and District 3 of 2024 and District 2 of 2025 eliminate four candidates in round 1 and end in round 2.  District 7 of 2024 ends in round 3 and every other contest in round 1 or 2, and each winner is the County's.

Each planted error is a copy of the reference or the converter with one change of its text, which must occur once in the script.  The reference's copies change the batch test, the tie rule, the overvote rule, and the counted kinds, and the converter's copies change the fields that rankings give.  The script runs every check of the table except the round trips on each copy of the reference, and the round trips on each copy of the converter, and it fails unless each copy fails every check predicted for it.

| Planted error | Checks that fail |
|---|---|
| A non-strict batch test, `>=` for `>` | The edge cases `tie-lowest-and-final`, `batch-boundary-equal`, `batch-nested`, `overvote-positions`, and `suspension`, in each of which some candidate's votes equal the sum of the votes of the candidates with fewer |
| The smallest qualifying set instead of the largest | The edge case `batch-nested` |
| A tie that eliminates the candidate earliest in the order | The worked example and the edge cases `example-1`, `tie-final`, `tie-final-reversed`, `tie-lowest-and-final`, `kinds`, `max-size`, and `words-valid` |
| An overvote passed like an empty position | The worked example, District 4, Table A, 7 edge cases, and every round-by-round comparison with the County's reports, but none of the comparisons by winner |
| An overvote only when two continuing candidates are marked | The same checks |
| The aggregate write-in counted | The worked example, District 4, Table A, 6 edge cases, and every round-by-round comparison with the County's reports, but none of the comparisons by winner |
| In the converter, an overvote written as an empty field | The round trip of every contest |
| In the converter, the candidates' indices reversed | The round trip of every contest |

The batch and tie errors fail no comparison with the County's reports, so only the edge cases detect them.  The expectations stated by hand come from the reference's author, who read the requirements in the same way when writing the reference.  A misreading shared by the reference and those expectations passes both, and the requirements call for a reviewer to check the smallest reports by hand.

## RCTab

RCTab, the ranked-choice tabulator of the Bright Spots Developers under the Mozilla Public License 2.0, counts contests of the corpus as a second tabulator, with configurations that express the charter's rules and the County's practice.  `rctab.sh` pins release v2.1.0 of 2026-07-07 by its Linux x86-64 package `rctab_v2.1.0_Linux_X64.zip`, whose SHA-256 is `46547b3be29d9c4cd807c261b977202af67a36cb7fc9248306bfd3a81ea06102`.  The package bundles a Java 21.0.7 runtime, and `install` unpacks it into `DIR/rcv`.  RCTab's command-line mode starts the JavaFX toolkit, which needs an X display and GTK 3, as RCTab's open issue 789 reports, so on a host without a display `run` runs RCTab under `xvfb-run` from Debian's package `xvfb`.  RCTab exits with status 0 when a tabulation fails, and `run` therefore checks its console output for the pinned version, for SEVERE lines, and for the results directory.  `run` starts RCTab in the directory `OUT`, which then also holds RCTab's execution log.  RCTab's command-line mode tabulates the one configuration that its option `--cli` names ([`Main.java` lines 59 to 86](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Main.java#L59-L86)), so `batch` runs `run` for each line of a list, several at once, under one virtual display.  For the results below, the Python scripts ran on the machine that holds the corpus and RCTab ran on Debian 13 on x86-64, and the files moved between the two by copying.

`rctab.sh selftest` downloads RCTab's test contest `2015_portland_mayor` from the release's source tree, its configuration, cast vote records, and expected reports, each pinned by SHA-256.  It tabulates the contest and compares the detailed CSV and JSON reports with the expected ones line by line, ignoring line terminators and the lines that name the generating version or date, as RCTab's own tests do.  The contest uses the ES&S reader, batch elimination, candidate order for ties, an overvote label, and undeclared write-ins, and both reports equal the expected ones.

`rctab.py prepare` writes each canonical ballot file as a cast vote record report in the JSON form of NIST SP 1500-103, which RCTab's `cdf` provider reads, writes the file's two configurations beside it, and adds their lines to the list that `batch` reads.  Each candidate of the file becomes a candidate selection under its own name, whatever its kind, and the configuration decides whether RCTab counts it.  RCTab holds a name as text, so each byte of a name outside UTF-8 text appears as `\xhh`.  Each mark becomes the selection of its candidate at the position's rank, so a multiple position gives several selections at one rank, and the unnamed overvote `*` gives the selection of a candidate named `overvote`, which the configurations give as the `overvoteLabel`.  RCTab therefore reads the ballots that the reference reads, and the round trips of [Checks](#checks) test the converter against the CVR.

[The configurations](rctab/) are those that `prepare` writes for the corpus's contests without the 2022 suspension: for each contest, one for the charter's count and one for the County's practice, whose rules differ in `batchElimination` and `continueUntilTwoCandidatesRemain` alone.  Each reads the contest's CDF file from the directory that holds the configuration, writes RCTab's results into a directory of its own there, and lists the candidates in the file's tie-break order, with `Write-in` excluded.  The table maps each setting to the provision that it expresses.

| Setting | Value | Provision |
|---|---|---|
| `candidates`, `tiebreakMode` | The file's candidates in its tie-break order, and `useCandidateOrder` | §1105(e), by decision 3.  Of the candidates tied for the fewest votes, RCTab eliminates the one latest in the list, as rule 4 of the requirements' rounds does |
| `excluded` | `true` for the candidates of kinds `aggregate-writein` and `excluded`, and `false` for the others | §15341, through §1103.  RCTab passes over a ranking of an excluded candidate, as rule 4 of the interpretation passes over an uncounted candidate |
| `overvoteRule`, `overvoteLabel` | `exhaustImmediately`, `overvote` | §1105(h) and §15342(d).  A ballot that reaches a ranking with two or more marks, or with the unnamed overvote, is inactive whether or not the marked candidates continue |
| `maxSkippedRanksAllowed` | `unlimited` | §1105(g).  No number of empty rankings makes a ballot inactive |
| `exhaustOnDuplicateCandidate` | `false` | §1105(d)(2).  RCTab passes over a repeated ranking of an eliminated candidate |
| `maxRankingsAllowed` | `max` | §1105(c), with the requirements' reading of §1105(k)(1).  RCTab accepts a ranking at every position, as the module accepts any number of positions |
| `winnerElectionMode`, `numberOfWinners`, `doesFirstRoundDetermineThreshold`, `nonIntegerWinningThreshold`, `hareQuota` | `singleWinnerMajority`, `1`, `false`, `false`, `false` | §1105(a)(3) and (d)(2).  Each round's threshold is ⌊T/2⌋ + 1 for the round's continuing ballots T, which a candidate reaches exactly when it holds more than half of them |
| `batchElimination` | `true` for the charter, `false` for the County | §1105(f).  In a round without a winner, RCTab eliminates together the largest set of two or more lowest candidates whose combined votes are fewer than the votes of every other continuing candidate, which is rule 3 with its strict test |
| `continueUntilTwoCandidatesRemain` | `false` for the charter, `true` for the County | §1105(d)(2) ends the count at a majority, and the County counts until two candidates remain |
| `minimumVoteThreshold`, `cutoffElimination`, `stopTabulationEarlyAfterRound` | `0`, `false`, empty | None.  Each value turns off an elimination or a stop that the charter does not have |
| `decimalPlacesForVoteArithmetic` | `4` | None.  RCTab requires it and uses it only for the fractional transfers of contests with several winners |
| `outputDirectory` | The configuration's file name without `.json` | None.  Tabulations that run at the same time write their results apart |

No setting expresses the provisions and practices of the next table, in which RCTab's count differs from the reference's.  `rctab.py compare` reads the County's categories through the mapping of the first row.  It predicts RCTab's rounds from the reference's count by each named rule that applies and compares every round with the prediction, so that it reports every difference that no rule states.  Each rule restates the behavior of the lines of RCTab's source at the tag v2.1.0 that the last column cites.

| Rule | Provision or practice | RCTab | Source at v2.1.0 |
|---|---|---|---|
| None | The undervote of §1105(h) for a ballot that ranks only uncounted candidates, the reason `uncounted`, which the County's Blanks include | RCTab's undervotes count only the ballots without rankings, and it reports a ballot that ranks only excluded candidates among its exhausted choices.  `compare` therefore compares RCTab's undervotes with the reason `blank` and its exhausted choices with the reasons `exhausted` and `uncounted` together, and the County's Blanks and Exhausted together with RCTab's undervotes and exhausted choices together | [`Tabulator.java` 1118–1127](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1118-L1127) and [1256–1259](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L1256-L1259), [`OutputWriter.java` 1140–1151](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/OutputWriter.java#L1140-L1151) |
| `repeated-round` | The County's elimination in the round in which a candidate first holds a majority while three or more candidates continue | With `continueUntilTwoCandidatesRemain`, RCTab elects the candidate in that round and eliminates no one, and its next round repeats the round's figures, the winner continuing, and eliminates.  RCTab's test contest `continue_tabulation_test` expects the same.  The County's rounds are RCTab's without the electing round | [`Tabulator.java` 212–217](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L212-L217), [241–243](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L241-L243), and [540–544](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L540-L544) |
| `final-tie` | A round with two continuing candidates with equal votes, in which §1105(d)(2) and (e) eliminate the one latest in the order and elect the other in the next round, and for which the county count names no winner | RCTab elects the tied candidate earliest in the list in that round.  Under the charter the winner is the same, and RCTab's count has one round fewer | [`Tabulator.java` 630–663](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L630-L663), [`Tiebreak.java` 123–143](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tiebreak.java#L123-L143) |
| `no-continuing-ballot` | Rule 2 of the requirements' rounds, which ends a count without a continuing ballot with no winner | No candidate reaches the threshold of 1, and no batch qualifies, since the running total 0 is not below a tally of 0.  RCTab therefore eliminates one candidate per round, the tied candidate latest in the list, as the county count does, and elects the last candidate, or the earlier of the last two by `final-tie` | [`Tabulator.java` 476–481](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L476-L481), [589–593](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L589-L593), [699–700](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L699-L700), [802–818](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L802-L818), and [912](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L912), [`Tiebreak.java` 127–131](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tiebreak.java#L127-L131) |
| `no-ballots` | A contest without ballots, which rule 2 ends in round 1 | RCTab refuses the contest with the message "No cast vote records found!" and writes no report | [`TabulatorSession.java` 442–444](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/TabulatorSession.java#L442-L444) |
| `no-counted-candidate` | A contest without a counted candidate, which rule 2 ends in round 1 | RCTab refuses a configuration whose candidates are all excluded, with the message "Contest config must contain at least 1 non-excluded candidate!", and writes no report | [`ContestConfig.java` 693–695](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/ContestConfig.java#L693-L695), [`TabulatorSession.java` 194](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/TabulatorSession.java#L194) |
| `one-counted-candidate` | The county count of a contest with one counted candidate, which names that candidate in round 1 | With `continueUntilTwoCandidatesRemain`, RCTab tabulates no round, since it continues only while more than one candidate remains or the last round eliminated one.  It then stops with a `NullPointerException` where it reads round 1 to write its reports, and it writes none | [`Tabulator.java` 516–521](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L516-L521) and [855](https://github.com/BrightSpots/rcv/blob/v2.1.0/src/main/java/network/brightspots/rcv/Tabulator.java#L855) |
| `missing-ballots` | A CVR that lacks ballots of the County's report | A rule of the comparison with the County's report, from `check.py`: a round passes when each of the County's figures equals or exceeds RCTab's and the excesses sum to the missing ballots | None |
| None | The County's first-round suspension of November 2022 | No setting suspends a ballot, so RCTab is compared only with reports without the suspension | None |

`rctab.py compare` compares RCTab's rounds with the reference's count in the mode that the configuration's rules express, and with the County's report for the County's practice, by the rules of its docstring.  It classifies each comparison as equal, equal under the rules that applied, or different.  Every well-formed file that `edges.py` writes, the edited files that the reader accepts included, and every contest of the corpus without the 2022 suspension ran in both configurations, and no comparison is different.  The table counts the comparisons of the edge cases by the rules that applied.

| Result | Charter configuration | County configuration |
|---|---|---|
| Equal | 196 | 129 |
| Equal under `final-tie` | 60 | 61 |
| Equal under `repeated-round` | 0 | 28 |
| Equal under `no-continuing-ballot` | 2 | 0 |
| Equal under `no-continuing-ballot` and `final-tie` | 1 | 0 |
| Equal under `one-counted-candidate` | 0 | 41 |
| Equal under `no-ballots` | 2 | 2 |
| Equal under `no-counted-candidate` | 22 | 22 |
| Different | 0 | 0 |

`final-tie` applies in both configurations to the same files: the hand-stated contests `example-1`, `tie-final`, `tie-final-reversed`, `tie-lowest-and-final`, `kinds`, `max-size`, and `all-inactive`, every exhaustive contest, `edited-208`, and 29 random contests.  In each, RCTab elects in the tied round the tied candidate earlier in the order.  The county count names no winner there, and the charter's count elects the same candidate one round later, except in `all-inactive`, which rule 2 ends.  `repeated-round` applies to `batch-nested`, `batch-single-count-majority`, `names` and six edited copies of it, and 19 random contests, in each of which a candidate holds a majority while three or more candidates continue.  `no-continuing-ballot` applies to `all-inactive`, whose two listed candidates receive no vote, so that RCTab elects the earlier, and to `one-candidate-blank` and `random-097`, whose one counted candidate RCTab elects without a vote.  A scratch contest of three listed candidates, three inactive ballots, and the order `2 1 3` tests the rule's eliminations: RCTab eliminates C in round 1 and elects B in round 2, as the rule predicts.  `one-counted-candidate` applies to `one-candidate`, `one-candidate-blank`, `identifiers-k1`, and 38 random contests, `no-ballots` to `no-ballots` and `random-140`, and `no-counted-candidate` to `no-counted-candidate`, `edited-230`, and 20 random contests.

In the corpus's table, RCTab's rounds include the round that `repeated-round` names, and the County's report has one round fewer wherever that rule applies.

| Contest | Charter: RCTab's rounds | Charter against the reference | County: RCTab's rounds | County against the reference | County against the County's report |
|---|---|---|---|---|---|
| 2022 School Director, District 4 | 2 | Equal | 2 | Equal | Equal |
| 2024 City Council, At Large | 5 | Equal | 9 | Equal | Equal under `missing-ballots` |
| 2024 City Council, District 1 | 1 | Equal | 3 | Equal under `repeated-round` | Equal under `repeated-round` |
| 2024 City Council, District 3 | 2 | Equal | 6 | Equal under `repeated-round` | Equal under `repeated-round` |
| 2024 City Council, District 5 | 1 | Equal | 3 | Equal under `repeated-round` | Equal under `repeated-round` |
| 2024 City Council, District 7 | 3 | Equal | 3 | Equal | Equal under `missing-ballots` |
| 2024 City Attorney | 1 | Equal | 1 | Equal | Equal under `missing-ballots` |
| 2024 School Director, District 1 | 1 | Equal | 1 | Equal | Equal |
| 2024 School Director, District 3 | 1 | Equal | 1 | Equal | Equal |
| 2024 School Director, District 5 | 1 | Equal | 1 | Equal | Equal |
| 2024 School Director, District 7 | 1 | Equal | 1 | Equal | Equal |
| 2025 Mayor | 1 | Equal | 10 | Equal under `repeated-round` | Equal under `repeated-round` and `missing-ballots` |
| 2025 City Council, District 2 | 2 | Equal | 6 | Equal under `repeated-round` | Equal under `repeated-round` |

In District 4, RCTab gives Hutchinson 8,227, Manigo 8,190, and Resnick 10,015 in round 1, with 4,269 undervotes, 148 overvotes, and 134 exhausted choices, eliminates Manigo, and elects Hutchinson in round 2 with 12,421 against Resnick's 12,165, with 173 overvotes and 1,955 exhausted choices.  The 134 ballots rank only write-ins, and the County's corrected report counts them among its 4,403 Blanks, so its 1,821 Exhausted of round 2 are RCTab's exhausted choices without them.  Both configurations give these rounds, since the charter's count of District 4 has no batch and reaches its majority in the County's last round.  The charter's configuration eliminates Afolabi, Hailey, Hirsch, and Semedar together in round 1 of District 3 of 2024 and elects Fife in round 2 with 11,437 against Logan's 8,069, and it eliminates Lowe, Matoury, Thomas, and Anderson together in round 1 of District 2 of 2025 and elects Wang in round 2 with 7,008 against Murray-Badal's 4,782.  In the at-large contest of 2024, it eliminates Danino, Matoury, Tostado, Pechenuk, and Robinson together in round 3 and elects Brown in round 5 with 72,313 against Armstrong's 54,776.  In the county configuration of the 2025 mayoral contest, RCTab elects Lee in round 1 with 47,170 of 94,292 continuing ballots and eliminates the other candidates one per round from round 2, and the County's nine rounds are RCTab's rounds 2 to 10.

A run of a small edge case took about 1.5 seconds and 0.2 GB, and the at-large contest, the largest of the corpus, took 9 seconds and 1.8 GB at its peak.  Under a quota of 400 percent of a CPU on the four-core host, the edge cases took 452 seconds with four runs at a time, when the load average rose to nearly 9 because each RCTab process starts many threads, and 596 seconds with two runs at a time, when it stayed between 3 and 5.  Both runs wrote the same reports.

The steps below run the edge cases and the 2022 District 4 contest, where `EDGES` and `RUN` are directories, `DIR` is RCTab's installation, and `WORK` a directory for the self-test.  `prepare` writes for District 4 the configurations of [`rctab/`](rctab/), and the commands of the RCTab host run after copying `EDGES`, `RUN`, and `rctab.sh` there.

```
uv run tests/rcv/edges.py tmp/rcv-edges
grep -aL '^error ' tmp/rcv-edges/*.report | sed 's/report$/rcv/' | xargs uv run tests/rcv/rctab.py prepare EDGES
uv run tests/rcv/convert.py tmp/rcv-data/cvr/otis/Oakland_20221108_SchoolBoardD4.csv \
  --report tmp/rcv-data/reports/248/Oakland_007-SchoolDirector_District_4.xml --out RUN/Oakland_20221108_SchoolBoardD4.rcv
uv run tests/rcv/rctab.py prepare RUN RUN/Oakland_20221108_SchoolBoardD4.rcv --date 2022-11-08 \
  --jurisdiction "Oakland, California" --office "School Director, District 4"

# on the RCTab host
tests/rcv/rctab.sh install DIR
tests/rcv/rctab.sh selftest DIR WORK
systemd-run --user --scope -p CPUQuota=400% -p MemoryMax=10G tests/rcv/rctab.sh batch DIR EDGES/runs 2
systemd-run --user --scope -p CPUQuota=400% -p MemoryMax=10G tests/rcv/rctab.sh batch DIR RUN/runs 2

# after copying EDGES and RUN back
while read config results; do
  uv run tests/rcv/rctab.py compare tmp/rcv-edges/${config%-*}.rcv EDGES/$config EDGES/$results
done < EDGES/runs
uv run tests/rcv/rctab.py compare RUN/Oakland_20221108_SchoolBoardD4.rcv RUN/Oakland_20221108_SchoolBoardD4-county.json \
  RUN/results/Oakland_20221108_SchoolBoardD4-county --county tmp/rcv-data/reports/248/Oakland_007-SchoolDirector_District_4.xml
```

## References

- [Alameda County RCV results](https://www.alamedacountyca.gov/rovresults/rcv/)
- [Alameda County Registrar of Voters, Ranked-Choice Voting Tally presentation](https://www.acgov.org/board/bos_calendar/documents/RankedChoiceVotingTallyPresentation.pdf)
- [D. Otis, Single winner ranked choice voting CVRs, Harvard Dataverse, version 25](https://doi.org/10.7910/DVN/AMK8PJ)
- [County of Alameda Elections Commission, agenda of November 21, 2024](https://alamedacountyca.gov/board/com_calendar/documents/FINALNov.21,2024ACECAgenda.pdf)
- [Oakland City Charter, Article XI (third-party copy)](https://gocodebook.com/library/us/ca/oakland/article-xi-elections)
- [Alameda County, Legal / Disclaimers](https://acgov.org/government/legal.htm)
- [RCTab, Bright Spots Developers](https://github.com/BrightSpots/rcv)
- [RCTab release v2.1.0](https://github.com/BrightSpots/rcv/releases/tag/v2.1.0)
- [RCTab configuration documentation, v2.1.0](https://github.com/BrightSpots/rcv/blob/v2.1.0/config_file_documentation.txt)
- [RCTab source, v2.1.0](https://github.com/BrightSpots/rcv/tree/v2.1.0/src/main/java/network/brightspots/rcv)
- [RCTab issue 789, Using CLI mode on a server with no X](https://github.com/BrightSpots/rcv/issues/789)
- [NIST SP 1500-103, Cast Vote Records Common Data Format](https://doi.org/10.6028/NIST.SP.1500-103)
