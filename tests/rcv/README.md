# Oakland RCV corpus

This directory holds the test corpus of the ranked-choice tabulator for Oakland, California, and the scripts that fetch and check it.  The corpus covers every Oakland contest on Alameda County's RCV results site from the general election of November 8, 2022 through the general election of November 3, 2026.  For each contest it lists the County's RCV detailed report and, where one exists, D. Otis's standardized cast vote record (CVR), and it adds the Registrar's presentation on the 2022 District 4 error.  [The manifest](manifest.json) gives each file's URL, size, and SHA-256, and [the notice](NOTICE) records each source's terms of use.  The repository holds none of the files.

## Scripts

The commands run from the repository root through `uv run`, and the scripts use only Python's standard library.  Each script reads `tests/rcv/manifest.json` and works in the data directory `tmp/rcv-data`, which Git ignores, unless the command names another.  Each script's docstring states its rules and its exit status.

| File | Command | Behavior |
|---|---|---|
| [`fetch.py`](fetch.py) | `uv run tests/rcv/fetch.py [DIR] [--no-cvr]` | Downloads each file of the manifest to its path under `DIR`, one request at a time with a two-second pause, and keeps a present file whose size and SHA-256 match.  A download that does not match stays beside its target as `PATH.mismatch`, the script prints the expected and the received size and digest, and the exit status is 1.  `--no-cvr` skips the CVRs, about 194 MB. |
| [`reports.py`](reports.py) | `uv run tests/rcv/reports.py [DIR]` | Parses each report, checks that its tallies, inactive categories, and transfers agree within and between rounds, writes `DIR/normalized/<election>/<race>.json`, and prints the table of [the corpus](#corpus). |
| [`recount.py`](recount.py) | `uv run tests/rcv/recount.py [KEY ...] [--suspend] [--data DIR]` | Recounts each contest that has a CVR, or the contests named by their manifest keys, and prints each round that differs from the report and a summary line per contest ([Recount](#recount)). |
| [`district4.py`](district4.py) | `uv run tests/rcv/district4.py [--data DIR]` | Checks the 2022 District 4 counts against the County's figures ([District 4](#district-4)) and exits with status 1 on a difference. |

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

## References

- [Alameda County RCV results](https://www.alamedacountyca.gov/rovresults/rcv/)
- [Alameda County Registrar of Voters, Ranked-Choice Voting Tally presentation](https://www.acgov.org/board/bos_calendar/documents/RankedChoiceVotingTallyPresentation.pdf)
- [D. Otis, Single winner ranked choice voting CVRs, Harvard Dataverse, version 25](https://doi.org/10.7910/DVN/AMK8PJ)
- [County of Alameda Elections Commission, agenda of November 21, 2024](https://alamedacountyca.gov/board/com_calendar/documents/FINALNov.21,2024ACECAgenda.pdf)
- [Oakland City Charter, Article XI (third-party copy)](https://gocodebook.com/library/us/ca/oakland/article-xi-elections)
- [Alameda County, Legal / Disclaimers](https://acgov.org/government/legal.htm)
