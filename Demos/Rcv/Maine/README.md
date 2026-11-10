# Maine ranked-choice tabulation

[The requirements](requirements.md) state the tabulator's Maine module, the count of 21-A M.R.S. §723-A with the rules of 29-250 C.M.R. ch. 535, and [the review](review.md) records each reading of the governing texts.  This directory holds increment M1 of the requirements' plan: the specification, its tests against the Python reference, the edge cases, and the Secretary of State's records, and the theorems T4 to T9, with Oakland's T10 applied to the module's interpretation.  The module shares with [the Oakland module](../README.md) the contest structure, the reader, the tally of a round, `run`, the lines of the report, the word forms of a round, and the lemmas about `run`.

## Specification

The specification states the requirements' count over lists, natural numbers, and the 64-bit position words, and every definition computes, so native Lean runs it on canonical files.  Two fresh agents reviewed it against the requirements, each with a model of its own, and [the review](review.md#review-of-the-specification) records their findings and the responses.

| File | Contents |
|---|---|
| [`Spec.lean`](Spec.lean) | The interpretation, the initial test, the decision of a round, the count, the report, the report of a file, and the word forms |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the requirements' 17-ballot example and its report, byte for byte, of the five-ballot example of the initial test with its words, and of small cases of the rules |
| [`Native.lean`](Native.lean) | The executable `rcv-maine`, which runs the specification on canonical files and word arrays and tests the theorems' statements |

`examine` adds rule 1 of the interpretation to the Oakland module's examination: at an empty position, `skipped` ends the examination with `exhausted` when the next position is also empty and some later position is marked.  `interpret` gives the reason of a ballot whose examination passes its last position by the shared `passedReason`.  `firstCounts` gives `f(i)` for each candidate of `K`, the number of ballots whose first position is single and marks it, and `initialWinner` the candidate with `2 f(i) > N`, if any.  `decision` applies the two rules of a round to its counts: two candidates with equal votes form a tied set whose member later in the order is eliminated, at most two candidates otherwise end the count, and `lastPlace` eliminates the candidate with the fewest votes, or the tied candidate latest in the order.  `count` ends with the initial test's winner and no rounds, or runs the shared `run` with `interpret` and `decision` from `K`, allowing one more round than `K` has candidates.  `reportLines` adds the `first` lines to the shared report's lines under the module's rule identifier, `reportFile` gives the report or the error report of a file through the shared reader, and `countWords` inserts `f(1)` to `f(n)` after the number of rounds.

## Theorems

[`Stability.lean`](Stability.lean) and [`Rounds.lean`](Rounds.lean) prove T4 to T9 of the requirements for the count, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, some on the first and the third only.  T4 assumes `Contest.WellFormed`, whose order is a permutation of the candidates, and T9 assumes that the new order is such a permutation.  The other theorems hold for every contest structure.

| Theorem | Lean name | Statement |
|---|---|---|
| T4 Elimination | `elimination` | Every round that eliminates meets `Eliminates`: three or more candidates and a lowest elimination of the candidate that alone has the fewest votes or an elimination by order of the member of the tied set latest in the order, or two candidates with equal votes, which form the tied set, and the elimination by order of the one later in the order.  The last round eliminates no one and meets `Concludes`: at most two candidates, and the winner is the one of more votes, the one alone, or none when no candidate continues |
| T5 Conservation | `conservation` | In every round the votes and the four inactive counts sum to the number of ballots, and `continuing` is the sum of the votes |
| T6 Locality | `locality` | When the count has rounds, round 1's continuing set is `K`.  Each round's counts are the numbers of ballots whose interpretation against its continuing set counts for each candidate or has each reason, the next round's continuing set is the current one minus the eliminated candidate, and each `f(i)` is the number of ballots whose first position is single and marks `i` |
| T7 Invariance | `invariance` | Ballots whose position words are a permutation of the contest's give the same count, the same first counts, and the same report |
| T8 Stability | `stability_counts`, `stability_inactive`, `interpret_closed`, `interpret_stable`, `stability_rounds` | For continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for `w` against `S'` when `w ∈ S'`, and a ballot inactive against `S` is inactive against `S'` with the same reason.  The interpretation counts a ballot only for a member of the continuing set.  From each round of the count to the next, no inactive count decreases, the votes of a candidate that continues do not decrease, and `continuing` does not increase |
| T9 Order | `order_choice` | If an order `π′` places the eliminated candidate of each marked tie after the rest of its tied set, the count under `π′` equals the count under the contest's order, and the report's lines differ only in the order line |
| T10 Batch | `batch_winner`, `batch_rounds`, `batch_members` | The Oakland theorem for every interpretation with `Closed` and `Stable`, applied to this interpretation.  The Maine count has no batch, and no comparison rests on T10 |

The proofs reuse the shared lemmas about `run` through `Demos.Rcv.Rounds.Ends`, which `decision_ends` proves for `decision`: every elimination names one candidate of the round, and a round of at most one candidate ends the count.  `Demos.Rcv.Rounds.run_trace` then gives a trace of the count's rounds whenever the initial test elects no one (`count_trace`), and `count_initial` gives the count of no rounds otherwise.  `decision_three` equates rule 2 with the Oakland module's rule 4, `Demos.Rcv.Rounds.lowestDecision` of `Demos.Rcv.Rounds.ruleTied`, so that its lemmas apply, and `decision_eq_eliminate`, `decision_eq_winner`, `decision_tied`, and `decision_order` describe the decision's eliminations, its ends, its tied sets, and its use of the order.  Rule 1 of the interpretation ends the examination at a position whatever the continuing set, so the proofs of T8 follow the Oakland module's with one more case.

## Tests

[`Native.lean`](Native.lean) decided each theorem's statement natively before its proof, deciding the theorems' own propositions `Eliminates` and `Concludes`.  `rcv-maine random` drew 78,000 seeded random contests of up to 12 candidates of every kind, 8 positions, and 200 ballots, a third of them with one candidate ranked first on about 60 percent of the ballots, of which the initial test decided 22,909.  The other contests had 99,220 rounds, 16,555 lowest eliminations, and 27,574 eliminations by order, 12,336 of them tied final pairs.  T4 to T9 held on every contest, and of 312,000 random orders tried for T9, 264,780 met its hypothesis, 17,753 of them with a marked tie and an order other than the contest's, while 47,220 orders that failed it changed the count.  `rcv-maine pairs` decided both statements of T8 and `Closed` for 4,680 ballots of up to four positions against every pair `S' ⊆ S` of subsets of five candidates of every kind, 1,137,240 pairs.  The runs rejected false statements: T4 with the earliest tied member on 19,329 contests, T4 with a majority for the winner in the last round on 15,776, T6 with `f(i)` counting first positions that mark `i` among others on 10,749, and T8 for the reading of the overvote that passes a multiple position without a continuing candidate on 53,019 pairs.

The specification and the reference's Maine mode, which an agent wrote from the requirements without the Lean specification, agree byte for byte on every file of the edge cases and of the corpus.  `rcv-maine compare` gives the reference's report for the 668 canonical files of `tests/rcv/maine/edges.py`, 319 of them well formed and the rest malformed, and for the six contests of [the corpus](../../../tests/rcv/maine/README.md), and `rcv-maine compare-words` gives the reference's result words for their 342 word arrays.  `rcv-maine check` decided the conclusions of T4 to T9 on the 319 contests of the edge cases, with 882 rounds and 349 eliminations by order.

```sh
uv run tests/rcv/maine/edges.py
uv run python -I tests/rcv/maine/check.py
tools/leanrun --timeout 40m lake build Demos.Rcv.Maine.Rounds Demos.Rcv.Maine.Cases rcv-maine
.lake/build/bin/rcv-maine compare tmp/rcv-maine-edges/*.rcv tmp/rcv-maine-data/canonical/*.rcv
.lake/build/bin/rcv-maine compare-words tmp/rcv-maine-edges/*.words tmp/rcv-maine-data/canonical/*.words
.lake/build/bin/rcv-maine check tmp/rcv-maine-edges/*.rcv
.lake/build/bin/rcv-maine pairs
.lake/build/bin/rcv-maine random 1 3000 5 4 12
.lake/build/bin/rcv-maine random 2 20000 6 5 30
.lake/build/bin/rcv-maine random 3 4000 8 6 60
.lake/build/bin/rcv-maine random 4 50000 3 3 8
.lake/build/bin/rcv-maine random 5 1000 12 8 200
```

```
674 files, 325 well formed, 0 differ
342 word arrays, 0 differ
```
