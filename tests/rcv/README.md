# Oakland RCV corpus

This directory holds the test corpus of the ranked-choice tabulator for Oakland, California, and the scripts that fetch and check it.  The corpus covers every Oakland contest on Alameda County's RCV results site from the general election of November 8, 2022 through the general election of November 3, 2026.  For each contest it lists the County's RCV detailed report and, where one exists, D. Otis's standardized cast vote record (CVR), and it adds the Registrar's presentation on the 2022 District 4 error.  [The manifest](manifest.json) gives each file's URL, size, and SHA-256, and [the notice](NOTICE) records each source's terms of use.  The repository holds none of the files.

## Scripts

The commands run from the repository root through `uv run`, and the scripts use only Python's standard library.  `fetch.py`, `reports.py`, `recount.py`, `district4.py`, and `check.py` read `tests/rcv/manifest.json` and work in the data directory `tmp/rcv-data`, which Git ignores, unless the command names another.  Each script's docstring states its rules and its exit status.

| File | Command | Behavior |
|---|---|---|
| [`fetch.py`](fetch.py) | `uv run tests/rcv/fetch.py [DIR] [--no-cvr]` | Downloads each file of the manifest to its path under `DIR`, one request at a time with a two-second pause, and keeps a present file whose size and SHA-256 match.  A download that does not match stays beside its target as `PATH.mismatch`, the script prints the expected and the received size and digest, and the exit status is 1.  `--no-cvr` skips the CVRs, about 194 MB. |
| [`reports.py`](reports.py) | `uv run tests/rcv/reports.py [DIR]` | Parses each report, checks that its tallies, inactive categories, and transfers agree within and between rounds, writes `DIR/normalized/<election>/<race>.json`, and prints the table of [the corpus](#corpus). |
| [`recount.py`](recount.py) | `uv run tests/rcv/recount.py [KEY ...] [--suspend] [--data DIR]` | Recounts each contest that has a CVR, or the contests named by their manifest keys, and prints each round that differs from the report and a summary line per contest ([Recount](#recount)). |
| [`district4.py`](district4.py) | `uv run tests/rcv/district4.py [--data DIR]` | Checks the 2022 District 4 counts against the County's figures ([District 4](#district-4)) and exits with status 1 on a difference. |
| [`convert.py`](convert.py) | `uv run tests/rcv/convert.py CVR [--report XML] [--contest ID] [--order I ...] [--no-ids] [--out FILE]` | Writes the canonical ballot file of a CVR ([The converter](#the-converter)). |
| [`reference.py`](reference.py) | `uv run tests/rcv/reference.py [--county \| --suspend \| --contest-words \| --result-words] FILE` | Prints the report of a canonical file, or writes the count's word forms ([The reference](#the-reference)). |
| [`edges.py`](edges.py) | `uv run tests/rcv/edges.py [OUT]` | Writes the edge cases with the reference's outputs into `OUT`, `tmp/rcv-edges` by default, and checks the reference against the expectations stated by hand ([Edge cases](#edge-cases)). |
| [`check.py`](check.py) | `uv run tests/rcv/check.py [--data DIR]` | Converts each CVR, checks the converter and the reference against the requirements and the County's reports, writes `DIR/canonical`, and runs the planted errors ([Checks](#checks)). |

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

## The reference

`reference.py` transcribes the reader of the canonical file with its error report, the writer, the interpretation of a ballot, the rounds, the report, and the count's word forms from [the requirements](../../Demos/Rcv/requirements.md) alone, without the Lean specification.  `reference.py FILE` prints the report of the charter's count, or the error report of a malformed file, with exit status 0 in both cases, as the module returns either report.  `--contest-words` writes the contest's words and `--result-words` reads contest words and writes the count's, each as little-endian 64-bit words.

`--county` and `--suspend` give the county count and the faulty setting of the 2022 case study, which the requirements define for comparisons with the County's reports and which no module carries.  Their reports have the report's form with the rule lines `rule alameda-county-count` and `rule alameda-county-count first-round-suspension`, so that neither can be taken for the charter's report.  The faulty setting adds the line `inactive suspended x` after the other inactive lines of each round.

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

## References

- [Alameda County RCV results](https://www.alamedacountyca.gov/rovresults/rcv/)
- [Alameda County Registrar of Voters, Ranked-Choice Voting Tally presentation](https://www.acgov.org/board/bos_calendar/documents/RankedChoiceVotingTallyPresentation.pdf)
- [D. Otis, Single winner ranked choice voting CVRs, Harvard Dataverse, version 25](https://doi.org/10.7910/DVN/AMK8PJ)
- [County of Alameda Elections Commission, agenda of November 21, 2024](https://alamedacountyca.gov/board/com_calendar/documents/FINALNov.21,2024ACECAgenda.pdf)
- [Oakland City Charter, Article XI (third-party copy)](https://gocodebook.com/library/us/ca/oakland/article-xi-elections)
- [Alameda County, Legal / Disclaimers](https://acgov.org/government/legal.htm)
