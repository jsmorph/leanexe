# Maine ranked-choice tabulation

[The requirements](requirements.md) state the tabulator's Maine module, the count of 21-A M.R.S. §723-A with the rules of 29-250 C.M.R. ch. 535, and [the review](review.md) records each reading of the governing texts.  This directory holds increments M1 and M2 of the requirements' plan.  M1 is the specification, its tests against the Python reference, the edge cases, and the Secretary of State's records, and the theorems T4 to T9, with Oakland's T10 applied to the module's interpretation.  M2 is the program over word arrays and its refinement, the module that the verified compiler compiles with its call theorems over words and over bytes, and the theorems T1, T3, and T11.  The module shares with [the Oakland module](../README.md) the contest structure, the reader and its program, the tally of a round, `run`, the lines of the report, the word forms of a round, the lemmas about `run`, and the functions of the Oakland programs that the two counts share.

## Specification

The specification states the requirements' count over lists, natural numbers, and the 64-bit position words, and every definition computes, so native Lean runs it on canonical files.  Two fresh agents reviewed it against the requirements, each with a model of its own, and [the review](review.md#review-of-the-specification) records their findings and the responses.

| File | Contents |
|---|---|
| [`Spec.lean`](Spec.lean) | The interpretation, the initial test, the decision of a round, the count, the report, the report of a file, and the word forms |
| [`Variants.lean`](Variants.lean) | The count without the initial test and the single count, with which T11 and T12 compare the count |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the requirements' 17-ballot example and its report, byte for byte, of the five-ballot example of the initial test with its words, and of small cases of the rules |
| [`Native.lean`](Native.lean) | The executable `rcv-maine`, which runs the specification on canonical files and word arrays and tests the theorems' statements |

`examine` adds rule 1 of the interpretation to the Oakland module's examination: at an empty position, `skipped` ends the examination with `exhausted` when the next position is also empty and some later position is marked.  `interpret` gives the reason of a ballot whose examination passes its last position by the shared `passedReason`.  `firstCounts` gives `f(i)` for each candidate of `K`, the number of ballots whose first position is single and marks it, and `initialWinner` the candidate with `2 f(i) > N`, if any.  `decision` applies the two rules of a round to its counts: two candidates with equal votes form a tied set whose member later in the order is eliminated, at most two candidates otherwise end the count, and `lastPlace` eliminates the candidate with the fewest votes, or the tied candidate latest in the order.  `count` ends with the initial test's winner and no rounds, or runs the shared `run` with `interpret` and `decision` from `K`, allowing one more round than `K` has candidates.  `reportLines` adds the `first` lines to the shared report's lines under the module's rule identifier, `reportFile` gives the report or the error report of a file through the shared reader, and `countWords` inserts `f(1)` to `f(n)` after the number of rounds.

[`Variants.lean`](Variants.lean) defines the two counts with which T11 and T12 compare the count.  `countWithoutTest`, the count without the initial test, runs the rounds of the count from `C₁ = K` whatever the first rankings, and `singleCount`, the single count, runs the Oakland rules 1, 2, and 4 of `Demos.Rcv.Variants.ruleSingle` with this module's interpretation.  Two fresh agents reviewed both definitions against the requirements, each with a model of its own, and [the review](review.md#review-of-the-counts-of-t11-and-t12) records their findings.

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

The plan lists T8 and T10 for this interpretation under increment M2, and the theorems of this table, proved in M1, state them.  [`Winner.lean`](Winner.lean) proves T3 and [`Holder.lean`](Holder.lean) T11, and each of their theorems depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, as `#print axioms` at the end of each file reports.  None assumes `Contest.WellFormed`.

| Theorem | Lean name | Statement |
|---|---|---|
| T3(a) Winner | `winner_iff` | The count names a winner exactly when `countedSet kinds`, which is `K`, is not empty |
| T3(b) | `winner_majority` | A winner `w` of the initial test has `N < 2 f(w)`, with `f(w)` the `firstCount` of the ballots, and when the last round has a continuing ballot, the count names a candidate `w` with `(w, v)` among the votes of the last round and `Tᵣ < 2 v` |
| T3(c) | `tied_final` | When the rounds end with `prev` and `last`, `last` has one continuing candidate exactly when the votes of `prev` are `[(a, v), (b, v)]`, and then the elimination of `prev` is `.order [a, b] i` for some `i`, which the report prints as a `tie` line |
| T3(d) | `rounds_le` | The count has no rounds exactly when `initialWinner` names a candidate, and at most the larger of 1 and the size of `K` rounds |
| T11(a) Majority holder | `holder_subset` | If `w` holds more than half of the continuing ballots against a set `S` without duplicates, it holds more than half against every such `S'` with `w ∈ S' ⊆ S` |
| T11(b) | `count_majority` | A candidate `w` with `(w, v)` among the votes of a round of the count and `Tᵣ < 2 v` continues in every later round, and the count names `w` |
| T11(c) | `initial_holder` | If the initial test elects `w`, then `w` holds more than half of `T₁` in round 1 of `countWithoutTest`, and `countWithoutTest` names `w` |
| T11(d) | `single_winner` | If `singleCount` names `w`, the count names `w` |

`decision_single` shows that every elimination of `decision` names one candidate, so a count that eliminates from two or more candidates keeps one, which gives T3(a).  `holder_trace` shows that a candidate that holds a majority against the continuing set of a round is never eliminated and is named: no last place holds a majority, and two candidates of which one holds a majority do not tie, while T8 keeps the majority from round to round through `Demos.Rcv.Stability.majority_subset`.  Every ballot that ranks a candidate of `K` first alone counts for it in round 1 (`firstCount_le_votes`), so the initial test's winner holds a majority there.  A round of the single count that eliminates has no majority and a continuing ballot, so it has two tied candidates or three or more, and `decision` eliminates the same candidate (`decision_of_single`).  The two counts therefore have the same rounds until the single count names a majority holder, whom the count names as well (`single_names`).

## Program

[`Program.lean`](Program.lean) states the Maine count over words in the verified compiler's dialect: `count` takes a contest array in the word form of the requirements and returns the result words of `Demos.Rcv.Maine.countArray`, or `[0]` for an array that is not a valid contest.  It calls the functions of [the Oakland program](../Program.lean) that the two counts share: `classify` of a position word, the loops over the candidates of a mask `continuingOf`, `majorityOf`, `fewestOf`, `tiedOf`, and `latestOf`, `pushRound` of a round's words, `countedOf` and `countedSize` of the counted set, and `validArray`, the test of a valid array.  `examineAt` adds rule 1 of the interpretation in one pass over a ballot: it keeps the number of empty positions just passed, up to 2, and a marked position after two of them ends the examination with `exhausted`, where the specification looks ahead from the first of them.  `tallyRound` examines the first `m` words of each ballot, so the round of the first positions against `K`, with `m = 1`, holds the first counts `f(i)` at the votes' counters, and `majorityOf` of those counters against `N` gives the initial test's winner.  `decideRound` counts the continuing candidates with `memberCount` and computes rule 2 with `lastPlaceOf`.  Of two candidates it names the one outside the mask of rule 2's lowest elimination, the bit that the exclusive or of the two masks leaves, and when they tie it keeps rule 2's elimination by order.  `countValid` appends the first counts to the result words, ends with the test's winner, and otherwise runs the rounds in a `repeatWhile` as the Oakland program does.

The refinement proves that the program computes the specification, through the Oakland refinement's lemmas on words, masks, loops over the candidates, `pushRound`, and `validArray`.  [`RefineTally.lean`](RefineTally.lean) states the program's examination after `g` empty positions as the specification's examination of `g` zero words followed by the remaining words (`examineAt_eq`): two zero words before a marked one end it with `exhausted`, and a third changes nothing.  A ballot that the Maine examination passes to its end passes the Oakland examination as well, so the Oakland refinement gives its reason.  [`RefineRule.lean`](RefineRule.lean) equates `lastPlaceOf` with the Oakland module's rule 4 and proves `decideRound_eq`, and [`Refinement.lean`](Refinement.lean) follows the rounds against `Demos.Rcv.Spec.run` with `decision` in `go_eq`, reads the first counts from the counters of the round of first positions (`first_count`), and concludes `count_eq`.

The report's printer of [`PrintProgram.lean`](PrintProgram.lean) is the Oakland printer with this module's rule line and the `first` lines: `pushFirst` prints the line of each counted candidate from the mask of `K` and the first counts of the result words, and the rounds' words start after the first counts.  It takes the mask of `K` as an argument, since a first count of 0 does not tell a counted candidate from an uncounted one, and `tabulate` of [`TabulateProgram.lean`](TabulateProgram.lean) passes `countedOf` of the reader's words.  [`PrintProof.lean`](PrintProof.lean) proves `printReport_eq` as the Oakland printer's proof does, with the facts about the rounds and the winner of [`Winner.lean`](Winner.lean), and [`TabulateProof.lean`](TabulateProof.lean) proves `printError_eq` and `tabulate_eq`.

| File | Contents |
|---|---|
| [`Program.lean`](Program.lean) | The count over words in the dialect |
| [`RefineTally.lean`](RefineTally.lean) | The examination with rule 1 and the counters of a round |
| [`RefineRule.lean`](RefineRule.lean) | Rule 2, the two candidates of rule 1, and the words of the decision |
| [`Refinement.lean`](Refinement.lean) | The rounds, the first counts, and `count_eq` |
| [`PrintProgram.lean`](PrintProgram.lean) | The Maine report's printer and error printer in the dialect |
| [`PrintProof.lean`](PrintProof.lean) | The `first` lines, the result words, and `printReport_eq` |
| [`TabulateProgram.lean`](TabulateProgram.lean) | `tabulate`: the reader program, the count, and the printers |
| [`TabulateProof.lean`](TabulateProof.lean) | The error report, the words of a structure, the report's length, and `tabulate_eq` |
| [`Tabulate.lean`](Tabulate.lean) | `verified_compile` of the module |
| [`TabulateCall.lean`](TabulateCall.lean) | The exports and the call theorems |
| [`TabulateBound.lean`](TabulateBound.lean) | The closed forms of the bounds of `count` and `tabulate` |
| [`TabulateFile.lean`](TabulateFile.lean) | The file theorems of `build/verified/rcvMaine.wasm` |

## The module's exports return the count over words and the report of a file

[`Tabulate.lean`](Tabulate.lean) compiles the Maine count, the shared reader, and the Maine printers into one module, and [`TabulateCall.lean`](TabulateCall.lean) states the call theorems of its exports.  The compilation imports the programs alone, so a change of a proof does not compile the module again.  Each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, as `#print axioms` at the end of `TabulateCall.lean` and `TabulateBound.lean` reports.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.Maine.Refine.count_eq` | [`Refinement.lean`](Refinement.lean) | `Demos.Rcv.Maine.Program.count ws = Demos.Rcv.Maine.countArray ws` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Maine.TabulateProgram.tabulate_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `bytesOf (tabulate b) = Demos.Rcv.Maine.reportFile (bytesOf b)` for every buffer of fewer than `2^32` bytes |
| `count_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | `Verified.CallSpec compiled.module compiled.tables 22 Demos.Rcv.Maine.countArray compiled.count.bound`: function 22, called with a borrowed word array from a ready store in which `top` can rise by the generated bound, returns without a trap an owned array that holds `countArray` of the input, leaves a ready store, and raises `top` by at most the bound |
| T1 `tabulate_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | `Verified.CallSpec compiled.module compiled.tables 64 tabulateSpec compiled.tabulate.bound`, where `tabulateSpec b` is the buffer of `Demos.Rcv.Maine.reportFile (bytesOf b)`: function 64, called with a borrowed buffer from a ready store in which `top` can rise by the generated bound, returns without a trap an owned buffer of the report, leaves a ready store, and raises `top` by at most the bound |
| `readContest_callSpec`, `printReport_callSpec`, `printError_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | Functions 47, 61, and 63 compute the shared reader's `readResult` of the buffer's bytes, the Maine `printReport`, and the Maine `printError` |
| `exports` | [`TabulateCall.lean`](TabulateCall.lean) | The exports `count`, `readContest`, `printReport`, `printError`, and `tabulate` are functions 22, 47, 61, 63, and 64 |
| `count_bound` | [`TabulateBound.lean`](TabulateBound.lean) | `compiled.count.bound ws ≤ 486624` for every array of fewer than `2^64` words |
| `tabulate_bound` | [`TabulateBound.lean`](TabulateBound.lean) | `compiled.tabulate.bound b ≤ 80 L + 33958029` for a file of `L < 2^32` bytes |

The bounds in the call theorems are the generated ones, so the theorems hold for arrays and files of every size, and [`TabulateBound.lean`](TabulateBound.lean) closes them.  The count's bound is 152 bytes for an invalid array, and for a valid one 600 bytes for the counters of the first positions, 232 bytes for the literal `#[1, 0]`, 80 bytes for each of the at most 63 first counts, and either 80 bytes for the push of the test's winner or the rounds: at most 64 rounds of 600 bytes of counters and `80 (n + 9)` bytes of words, and the move of the at most 4,601 result words before the winner's to a block with room for it, at most 486,624 bytes in all.  The bound of `tabulate` adds the reader's `80 L + 10,704` bytes and the printer's, which pushes the first two lines, at most 20,777 bytes of header lines, at most 63 `first` lines, and at most 64 rounds, and copies the report, at most 1,304,174 bytes, into the buffer that it returns.  The reader and the Oakland printer's functions have the generated costs of the Oakland tabulator's compilation, which the lemmas before `readContest_bound_eq` show by rewriting both compilations' equations, so the Oakland tabulator's bounds of the reader and the round lines apply.  A proof of those equations by `rfl` unfolds the compiled programs and exceeds the heartbeat limit.

`tabulate_eq` follows the two results of the shared reader, as the Oakland tabulator's does.  For a malformed file the Oakland proof's `read_error_lt` bounds the line number below `2 ^ 64`, and `printError_eq` gives the Maine error report.  For a well-formed file, T2(b) gives the structure `c` whose writing is the file, `readWords_contestWords` reads the parts of its words, `countWords_contestWords` equates the Maine count over the words with the result words of `countContest c` and `firstContest c`, `countedOf_contest` gives the mask of `K`, and `printReport_eq` prints `report c`, whose length `report_length_lt` bounds below `2 ^ 64`.

## Tests

[`Native.lean`](Native.lean) decided the statements of T4 to T9 natively before their proofs, deciding the theorems' own propositions `Eliminates` and `Concludes`.  `rcv-maine random` drew 78,000 seeded random contests of up to 12 candidates of every kind, 8 positions, and 200 ballots, a third of them with one candidate ranked first on about 60 percent of the ballots, of which the initial test decided 22,909.  The other contests had 99,220 rounds, 16,555 lowest eliminations, and 27,574 eliminations by order, 12,336 of them tied final pairs.  T4 to T9 held on every contest, and of 312,000 random orders tried for T9, 264,780 met its hypothesis, 17,753 of them with a marked tie and an order other than the contest's, while 47,220 orders that failed it changed the count.  `rcv-maine pairs` decided both statements of T8 and `Closed` for 4,680 ballots of up to four positions against every pair `S' ⊆ S` of subsets of five candidates of every kind, 1,137,240 pairs.  The runs rejected false statements: T4 with the earliest tied member on 19,329 contests, T4 with a majority for the winner in the last round on 15,776, T6 with `f(i)` counting first positions that mark `i` among others on 10,749, and T8 for the reading of the overvote that passes a multiple position without a continuing candidate on 53,019 pairs.

The same runs decide the statements of T3 and T11 with `okT3`, `okT11a`, `okT11b`, `okT11c`, and `okT11d`, and T3 and T11 held on every contest.  T11(a) held on 730,280 pairs `S' ⊆ S` of subsets of `K` against which a candidate holds a majority, on the contests whose `K` has at most six candidates, T11(b) on 47,349 rounds' holders of a majority, T11(c) on the 22,909 contests that the initial test decides, and T11(d) on the 62,224 contests whose single count names a winner.  The runs rejected T11(b) for a holder of exactly half of a positive `Tᵣ` on 6,615 contests, and T11(d) in the other direction, that the single count names the count's winner, on 10,416, each a contest without a continuing ballot in round 1.  T11's statements ran before their proofs.  T3's ran after its proof, and the requirements' review had tested T3 on two models of the requirements before.

The specification and the reference's Maine mode, which an agent wrote from the requirements without the Lean specification, agree byte for byte on every file of the edge cases and of the corpus.  `rcv-maine compare` gives the reference's report for the 668 canonical files of `tests/rcv/maine/edges.py`, 319 of them well formed and the rest malformed, and for the six contests of [the corpus](../../../tests/rcv/maine/README.md), and `rcv-maine compare-words` gives the reference's result words for their 342 word arrays.  `rcv-maine check` decided the conclusions of T3 to T9 and T11 on the 319 contests of the edge cases, with 882 rounds and 349 eliminations by order, among them T11(a) on 4,949 pairs, T11(b) on 347 holders of a majority, T11(c) on the 27 contests that the initial test decides, and T11(d) on 285 single counts that name a winner.

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

[`tests/rcv/maine/tabulate.py`](../../../tests/rcv/maine/tabulate.py) compares the module, native Lean, and the reference.  For each canonical file it requires the module's export `tabulate` in the Wasmtime host, `rcv-maine report`, the specification, `rcv-maine program-report`, the program run natively, and the report that `edges.py` or `check.py` wrote to equal the reference's Maine report byte for byte, and for each word array it requires the export `count`, `rcv-maine array`, `rcv-maine program-array`, and the stored result words to equal the reference's.  On the 668 edge files, the six contests of the corpus, and the four files that the review of `Variants.lean` added, all agree, and so do the 342 word arrays.  The verified compiler compiles `Tabulate.lean` in a build of 950 s with a peak of 3.5 GB under `tools/leanrun --cpus 6 --threads 6 --memory-high 20G` on edgexpert-18ff, and the module has 33,578 bytes.

```sh
tools/leanrun --timeout 60m lake build Demos.Rcv.Maine.TabulateBound rcv-maine
mkdir -p build/verified
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Maine.Tabulate Demos.Rcv.Maine.TabulateProgram.compiled.module build/verified/rcvMaine.wasm
uv run tests/rcv/maine/edges.py
uv run python -I tests/rcv/maine/check.py
uv run tests/rcv/maine/tabulate.py tmp/rcv-maine-edges tmp/rcv-maine-data/canonical
```

```
tmp/rcv-maine-edges: 668 files, 319 well-formed, 349 malformed, 336 word arrays
tmp/rcv-maine-data/canonical: 6 files, 6 well-formed, 0 malformed, 6 word arrays
0 files or arrays with a disagreement
```

In the verified compiler's tests the module is `rcvMaine`: [the module registry](../../../tests/verified/modules.txt) lists its compilation, and [the case generator](../../../tests/TestSupport/Rcv/MaineCases.lean) gives its cases, which the executable `verified-cases-rcv-maine` prints alone and `verified-cases` prints with those of every other module.  `tests/verified/run.sh --cases rcvMaine` writes `build/verified/rcvMaine.wasm`, validates it with `wasm-tools`, and compares 143 cases between the Wasmtime host and `Demos.Rcv.Maine.countArray` and `Demos.Rcv.Maine.reportFile` in native Lean.  The cases hold the contest words and the canonical files of the contests, the other arrays, and the random contests of the Oakland module's cases, the requirements' two Maine examples, the 17-ballot example cut after each of its lines, and the Oakland example's edits that each break one line.  [`TabulateFile.lean`](TabulateFile.lean) states that the written file holds `encode compiled.module` and decodes to `compiled.module`, and each of its two theorems depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  `tests/native/verified.sh --module rcvMaine` translates the module's 65 functions to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same 143 cases.

```sh
tests/verified/run.sh --cases rcvMaine
tools/leanrun --timeout 10m lake env lean Demos/Rcv/Maine/TabulateFile.lean
tests/native/verified.sh --module rcvMaine
```

```
verified: passed 143 failed 0
'Demos.Rcv.Maine.TabulateFile.rcvMaine_file' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demos.Rcv.Maine.TabulateFile.rcvMaine_file_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
rcvMaine: 65 of 65 functions, 65 of 65 exports
rcvMaine: the clightgen program matches the translation
native verified: passed 143 failed 0
```
