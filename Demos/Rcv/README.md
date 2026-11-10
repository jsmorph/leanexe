# Ranked-choice tabulation

This demo is a tabulator for single-winner ranked-choice contests under Oakland City Charter §1105, the rule that Alameda County misconfigured in the November 2022 count of the Oakland Unified School District 4 board race.  The module fixes the charter's rule at compile time, so no setting can be chosen wrong at run time, and its theorems connect the module's bytes to a Lean transcription of the charter.  [The requirements](requirements.md) state the canonical ballot file, the interpretation of a ballot, the rounds, the report, and the theorems, and [the review](review.md) records each reading of the governing texts and the reviews' findings.

[The test corpus](../../tests/rcv/README.md) fetches Alameda County's official round-by-round reports for Oakland's ranked-choice contests from 2022 to 2026 and the cast vote records published for them, and recounts the records under the county's settings.

## Specification

The specification states the requirements' count over lists, natural numbers, and 64-bit position words, with no reference to a program, and every definition computes, so native Lean runs it on canonical files.  Two fresh agents reviewed it against the requirements, each with a model of its own, and [the review](review.md#review-of-the-specification) records their findings and the responses.  The count reads the kinds, the tie-break order, and the position words, while the names enter only the file and the report, and the ballots' identifiers only the file.

| File | Contents |
|---|---|
| [`Contest.lean`](Contest.lean) | The contest structure: the contest identifier and the candidates' names as bytes, the kinds, the tie-break order, and each ballot's optional identifier and position words.  `Contest.WellFormed` states the constraints of a structure |
| [`Spec.lean`](Spec.lean) | The interpretation, the rounds, the canonical file, the report, and the word forms |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the worked example, byte for byte, and of the requirements' edge cases |
| [`Native.lean`](Native.lean) | The executable `rcv-spec`, which runs the specification on canonical files and word arrays |

`interpret` examines a ballot's positions from the first against the continuing set.  `examine` applies the four rules of the interpretation and returns no outcome when it passes the last position, and `passedReason` then gives `blank`, `exhausted`, or `uncounted` from the ballot and the kinds alone.  `tally` interprets every ballot against the continuing set and counts the votes of each continuing candidate and the inactive ballots by reason.  `rule` applies the four rules of a round in order: the majority test `2 vᵣ(i) > Tᵣ`, the end with no winner when `Tᵣ = 0`, the batch of `batch`, which is the largest qualifying `L(X)` of two or more candidates under the strict test, and the elimination of the single candidate with the fewest votes or of the tied candidate latest in the order, which `latest` finds.  `count` runs rounds from the counted set until a rule ends the count, allowing one more round than there are counted candidates, while T3(d) of the requirements bounds the rounds by the larger of 1 and the number of counted candidates.

`write` prints a contest structure as its canonical file, and `report` gives the report's bytes, whose header lines are lines 2 to `6 + n` of the file.  `countWords` reads a word array, returns `[0]` unless `Words.Valid` holds, and otherwise returns the result words of the count, and `contestWords` gives the contest words of a structure.  The specification holds no reader of canonical files and no error report of malformed files, which the requirements' plan places in the second increment.

`Cases.lean` checks that `write` prints the worked example's structure as the requirements' ballot file and that `report` gives the requirements' report of it byte for byte, with the example's contest and result words.  Its other checks cover the edge cases that the requirements list under "Tests", apart from the malformed files: overvotes at each position, every pattern of empty positions up to four positions, duplicate and uncounted rankings, ties at the lowest place and in the final round, batches at both sides of the strict test and with tied members, nested qualifying sets, a batch inside which the single count ends, contests with no continuing ballot, no ballots, one candidate, or no counted candidate, 63 candidates and 63 positions, identifiers of 1 and 64 bytes, the contests of T15, the constraints of the structure, and invalid word arrays.  Each expected value comes from the rules by hand.

`rcv-spec` accepts a canonical file only when its own parser's result prints, through `write`, as the file's exact bytes and meets `Contest.WellFormed`.  Its modes are `report FILE`, which writes the report, `words FILE`, which writes the result words of the file's contest words, `array FILE`, which reads a word array and writes the result words, and `district4 FILE`, which compares the report's round lines with the District 4 report of the requirements.  `tests/rcv/check.py` writes the canonical file of the 2022 District 4 contest, with the candidates in the county's order, the aggregate write-in as candidate 4, the order `1 2 3 4`, and each ballot's `ballotID` as its identifier, and the specification's report of it holds every round line of the requirements' report.

```sh
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Cases rcv-spec
tools/leanrun --timeout 10m .lake/build/bin/rcv-spec district4 \
  tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv
```

```
30983 ballots, 19 round lines, 0 differ from the requirements
```

The Python reference of `tests/rcv/` and the specification agree byte for byte on every file that `tests/rcv/edges.py` and `tests/rcv/check.py` write.  On the 283 edge-case files that the reference reads and the 19 contests of the corpus, `rcv-spec report` gives the reference's report, and on their contest words and the 17 arrays of the word forms alone, written as decimal lines from the reference's little-endian files, `rcv-spec array` gives the reference's result words.  `rcv-spec` rejects each of the 349 files for which the reference gives an error report.

## Theorems of the rounds

[`Rounds.lean`](Rounds.lean) proves T4, T5, T6, T7, and T9 of the requirements over `countContest`, `reportLines`, and `report`, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  T4 assumes `Contest.WellFormed`, whose tie-break order is a permutation of the candidates, and T9 assumes that the new order is such a permutation.  T5, T6, and T7 hold for every contest structure.  T7 states the requirement over contest structures, and the requirement over files follows from it with T2, since the reader returns the structure whose writing is each well-formed file.

| Theorem | Lean name | Statement |
|---|---|---|
| T4 Elimination | `elimination` | Every round that eliminates meets `Eliminates`: `Tᵣ > 0`, no candidate holds a majority, and the elimination is a batch of two or more candidates that equals a qualifying `L(X)` and contains every qualifying `L(Y)`, or, when no qualifying set has two or more candidates, the candidate that alone has the fewest votes, or the two or more candidates with the fewest votes, marked as tied, and their member latest in the order.  The last round eliminates no one and ends by rule 1, with the candidate that holds a majority as the winner, or by rule 2, with `Tᵣ = 0` and no winner |
| T5 Conservation | `conservation` | In every round the votes and the four inactive counts sum to the number of ballots, and `continuing` is the sum of the votes |
| T6 Locality | `locality` | Round 1's continuing set is `K`.  Each round's votes and inactive counts are the numbers of ballots whose interpretation against that round's continuing set counts for each candidate or has each reason, every round but the last eliminates, and the next round's continuing set is the current one minus the eliminated candidates |
| T7 Invariance | `invariance` | Ballots whose position words are a permutation of the contest's give the same count and the same report, which covers a permutation of the ballots and any change of their identifiers |
| T9 Order | `order_choice` | If an order `π′` places the eliminated candidate of each marked tie after the rest of its tied set, the count under `π′` equals the count under the contest's order, and the report's lines differ only in the order line |

`run` takes the decision of a round as an argument, and `count` passes `rule`.  `Trace` describes the rounds of a count under any interpretation and any decision: a round in which the decision gives a winner is the last, and a round that eliminates is followed by the trace from its continuing set minus the eliminated candidates.  `Ends` states the properties of a decision that bound the rounds: every elimination names at least one candidate and only candidates of the continuing set, and a continuing set of at most one candidate ends the count.  `rule_ends` proves them for `rule`.  For such a decision, `run_trace` gives a trace whenever the fuel is at least the larger of 1 and the size of the continuing set, and `Trace.run_eq` and `run_fuel` show that every such fuel gives the same count.  `count_trace` applies these lemmas to `count`, whose fuel `K.length + 1` therefore suffices, and `Trace.length_le` bounds the rounds by the larger of 1 and the size of `K`.  `Trace.mem`, `Trace.head`, `Trace.next`, and `Trace.last_round` give each round's counts, continuing set, and decision, `run_perm` shows that the order of the ballots leaves the count unchanged, and `run_congr` equates the counts under two decisions that agree on every round of one of them.  For `rule`, `batch_some` and `batch_none` describe the fold of rule 3, `ruleTied_eq_fewest` equates the tied set of rule 4 with the candidates that have the fewest votes, and `latest_spec` shows that `latest` returns the member of the tied set latest in an order that holds each candidate once.

[`RoundStatements.lean`](RoundStatements.lean) decided each statement natively through the specification before its proof.  It reads the files that `tests/rcv/edges.py` writes, so no library imports it.  The conclusions of T4, T5, T6, and T7 held on the 283 edge-case files that `rcv-spec` loads and on 10,000 seeded random contests of up to eight candidates of every kind, five positions, and 60 ballots, which have 19,186 rounds, among them 919 batches, 3,829 lowest eliminations, and 4,155 eliminations by order.  Of 41,674 random orders tried for T9, 34,293 met its hypothesis, 4,175 of them in counts with a marked tie and with an order other than the contest's, and each of the 34,293 gave the same count and the stated report lines, while 7,381 of the orders that failed the hypothesis changed the count.  The run rejected false variants of the statements: T4 with the earliest instead of the latest tied member on 3,016 contests, T4 with the smallest qualifying set of two or more instead of the largest on 91, T5 with the continuing ballots counted twice on 9,124, and T6 with an unchanged continuing set on 4,084.

```sh
tools/leanrun --timeout 20m lake build Demos.Rcv.Rounds
uv run tests/rcv/edges.py
tools/leanrun --timeout 20m lake build rcv-spec
tools/leanrun --timeout 50m lake env lean Demos/Rcv/RoundStatements.lean
```

## Properties of instant runoff

[`Properties.lean`](Properties.lean) proves T12, T13, T14, and T15 of the requirements over `countContest`, `singleCount`, and `countyCount`, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  T12, T13, and T14 hold for every contest structure, so for every structure that meets `Contest.WellFormed`, and T15 proves that its two contests meet it.  `Beats` states the requirements' term "beats": more ballots count for one candidate than for the other against the continuing set of the two.  `Raises` states "raising": a position that marks only the candidate moves to an earlier position, and the other positions keep their order.  T14 lets the new ballot hold any number of positions after `p`, and its premise that the count names `w` makes `w` a counted candidate.

| Theorem | Lean name | Statement |
|---|---|---|
| T12 Majority criterion | `majority_criterion` | If more than half of the continuing ballots against `K` count for `w`, the count has one round and names `w`, and the single count and the county count name `w` |
| T13 Condorcet loser | `condorcet_loser` | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, the count does not name `ℓ` |
| T14 Later-no-harm | `later_no_harm` | If position `p` of a ballot marks only `w` and the count names `w`, a ballot whose positions 1 to `p` are the same in its place gives a count with the same rounds that names `w` |
| T15 Monotonicity fails | `monotonicity_fails` | The two contests of the requirements meet the constraints and differ only in two ballots, on which the second raises `A` from the second position to the first.  The count names `A` for the first and `B` for the second, and round 1 of each eliminates one candidate with the fewest votes alone |

T12 evaluates round 1 of the count and of the single count with `rule_holder` and `find_holder`, and it takes the county count's winner from `county_holder`, the form of T11(b) over traces.  `trace_not_loser` proves T13 over traces of the count for every interpretation that satisfies `Closed` and `Stable`.  When two or more candidates continue in the last round, the winner's majority persists by T11(a), `majority_subset`, against the pair of itself and any other candidate, which beats it there.  When the winner continues alone, the round before eliminated one candidate, since a batch leaves two or more (`BatchAt.rest_two_le`), and that candidate had the fewest votes against a set with the members of the pair of it and the winner, against which it beats the winner.  `interp_congr` gives the same interpretation against two sets with the same members.  For T14, `interpret_prefix` shows that a ballot whose position marks only a continuing candidate has an interpretation that its positions up to that one determine, `trace_winner_all` shows that the count's winner continues in every round, and `trace_ballots` shows, for every interpretation and decision, that ballots giving every round of a trace the same counts give the same trace.  T15 evaluates the counts and the constraints of its two contests in the kernel with `decide +kernel`.

[`PropertiesNative.lean`](PropertiesNative.lean), the executable `rcv-properties`, decided each statement natively through the specification before its proof.  It reads the contest words of the edge cases, 284 contests, and it generates 34,000 seeded random contests of every kind of candidate, in which half of the ballots rank distinct candidates and one candidate takes the first position of up to 60 percent of the ballots, and the 106,260 contests of every multiset of up to five ballots of a 20-ballot alphabet under two orders.  On these inputs T12 held for 88,790 candidates with a majority in round 1, 70,876 of them among three or more counted candidates, T13 for 89,043 counted candidates whom every other beats, 24,087 of them in counts of two or more rounds, and T14 for 3,766,242 replacements of a ballot, 1,163,880 of them in counts of two or more rounds, and `rcv-properties t15` reproduced the two counts of T15.  The run rejected false variants of the statements.  T12 with half of the continuing ballots in place of more than half failed for 42,332 candidates, and T12 with the county count ending after round 1 failed for 70,876.  T13 without its premise that `K` has two or more candidates failed for 9,925 candidates, T13 with ties allowed in the premise failed for 8,558, and the Condorcet winner criterion, which instant runoff does not meet, failed for 827.  For T14, a change of a position before `p` changed the count in 509,518 of 907,761 replacements, a change of position `p` in 4,082,497 of 4,354,272, and a change of the positions after `p` when the count does not name `w` in 551,353 of 3,785,079.  Moving the winner's single position to the front of a ballot changed the winner in 28 of 190,820 cases, the failure of monotonicity that T15 states.  The checks of T14 and of monotonicity take at most 48 positions of each contest, spread evenly over its ballots.

```sh
tools/leanrun --timeout 20m lake build Demos.Rcv.Properties rcv-properties
uv run tests/rcv/edges.py
tools/leanrun --timeout 5m .lake/build/bin/rcv-properties t15
tools/leanrun --timeout 20m sh -c '.lake/build/bin/rcv-properties edges tmp/rcv-edges/*.words'
tools/leanrun --timeout 20m .lake/build/bin/rcv-properties random 1 10000 5 4 30
tools/leanrun --timeout 20m .lake/build/bin/rcv-properties random 2 4000 8 5 60
tools/leanrun --timeout 20m .lake/build/bin/rcv-properties random 3 20000 3 3 12
tools/leanrun --timeout 20m .lake/build/bin/rcv-properties exhaustive 5
```
