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
| [`Native.lean`](Native.lean) | The executable `rcv-spec`, which runs the specification and the program on canonical files and word arrays |

`interpret` examines a ballot's positions from the first against the continuing set.  `examine` applies the four rules of the interpretation and returns no outcome when it passes the last position, and `passedReason` then gives `blank`, `exhausted`, or `uncounted` from the ballot and the kinds alone.  `tally` interprets every ballot against the continuing set and counts the votes of each continuing candidate and the inactive ballots by reason.  `rule` applies the four rules of a round in order: the majority test `2 vᵣ(i) > Tᵣ`, the end with no winner when `Tᵣ = 0`, the batch of `batch`, which is the largest qualifying `L(X)` of two or more candidates under the strict test, and the elimination of the single candidate with the fewest votes or of the tied candidate latest in the order, which `latest` finds.  `count` runs rounds from the counted set until a rule ends the count, allowing one more round than there are counted candidates, while T3(d) of the requirements bounds the rounds by the larger of 1 and the number of counted candidates.

`write` prints a contest structure as its canonical file, and `report` gives the report's bytes, whose header lines are lines 2 to `6 + n` of the file.  `countWords` reads a word array, returns `[0]` unless `Words.Valid` holds, and otherwise returns the result words of the count, and `contestWords` gives the contest words of a structure.  The specification holds no reader of canonical files and no error report of malformed files, which the requirements' plan places in the second increment.

`Cases.lean` checks that `write` prints the worked example's structure as the requirements' ballot file and that `report` gives the requirements' report of it byte for byte, with the example's contest and result words.  Its other checks cover the edge cases that the requirements list under "Tests", apart from the malformed files: overvotes at each position, every pattern of empty positions up to four positions, duplicate and uncounted rankings, ties at the lowest place and in the final round, batches at both sides of the strict test and with tied members, nested qualifying sets, a batch inside which the single count ends, contests with no continuing ballot, no ballots, one candidate, or no counted candidate, 63 candidates and 63 positions, identifiers of 1 and 64 bytes, the contests of T15, the constraints of the structure, and invalid word arrays.  Each expected value comes from the rules by hand.

`rcv-spec` accepts a canonical file only when its own parser's result prints, through `write`, as the file's exact bytes and meets `Contest.WellFormed`.  It reads and writes word arrays as the reference does, packed as little-endian 64-bit words.  Its modes are `report FILE`, which writes the report, `contest-words FILE`, which writes the file's contest words, `words FILE`, which writes the result words of the file's contest words, `array FILE`, which reads a word array and writes the result words of `countArray`, `program FILE`, which writes those of the program `Demos.Rcv.Program.count` run natively, and `district4 FILE`, which compares the report's round lines with the District 4 report of the requirements.  `tests/rcv/check.py` writes the canonical file of the 2022 District 4 contest, with the candidates in the county's order, the aggregate write-in as candidate 4, the order `1 2 3 4`, and each ballot's `ballotID` as its identifier, and the specification's report of it holds every round line of the requirements' report.

```sh
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Cases rcv-spec
tools/leanrun --timeout 10m .lake/build/bin/rcv-spec district4 \
  tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv
```

```
30983 ballots, 19 round lines, 0 differ from the requirements
```

The Python reference of `tests/rcv/` and the specification agree byte for byte on every file that `tests/rcv/edges.py` and `tests/rcv/check.py` write.  On the 283 edge-case files that the reference reads and the 19 contests of the corpus, `rcv-spec report` gives the reference's report, and on their contest words and the 17 arrays of the word forms alone, `rcv-spec array` gives the reference's result words.  `rcv-spec` rejects each of the 349 files for which the reference gives an error report.

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

## Stability, batches, and the county count

[`Variants.lean`](Variants.lean) defines the single count and the county count of the requirements' theorems as `run` from `K`, with the count's interpretation and fuel and a decision of their own.  `ruleSingle` applies rules 1, 2, and 4, and `ruleCounty` applies rule 4 while three or more candidates continue and otherwise ends the count, where `countyWinner` names the candidate with more votes, the candidate alone, or none.  Both take rule 4 from `lowestDecision` and `ruleTied`, as `rule` does, and `ruleSingle_ends` and `ruleCounty_ends` prove `Ends` for them, so the lemmas about `Trace` apply to the three counts.  [`Stability.lean`](Stability.lean), [`Batch.lean`](Batch.lean), [`Holder.lean`](Holder.lean), and [`Winner.lean`](Winner.lean) prove T8, T10, T11, and T3, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.

| Theorem | Lean name | Statement |
|---|---|---|
| T8 Stability | `stability_counts`, `stability_inactive`, `stability_rounds` | For continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for `w` against `S'` when `w ∈ S'`, and a ballot inactive against `S` is inactive against `S'` with the same reason.  From each round of the count to the next, no inactive count decreases, the votes of a candidate that continues do not decrease, and `continuing` does not increase |
| T10 Batch | `batch_winner`, `batch_rounds`, `batch_members` | (a) The single count names the count's winner, or both name none.  (b) The counts of the count's rounds form a sublist of the single count's, or all but the last do, the single count names the count's winner, and its last continuing set strictly contains the count's.  (c) From a round of the single count with the continuing set of a round of the count that eliminates the batch `B`, each of the next `B.length` rounds ends the single count or eliminates exactly one member of `B` that continues in it |
| T11 Majority holder | `holder_subset`, `county_majority`, `county_winner`, `county_tied`, `county_rounds_sublist` | (a) A candidate with a majority against a continuing set has one against every smaller continuing set that holds it.  (b) A candidate with a majority in a round of the county count continues in every later round, and the county count names it.  (c) If the count names `w` and its last round is round 1 or has two or more continuing candidates, the county count names `w`.  If the count's last round has one candidate and is not round 1, the county count's last round has the counts of the count's round before it.  (d) The counts of the count's rounds with two or more continuing candidates form a sublist of the county count's |
| T3 Winner | `winner_iff`, `winner_majority`, `tied_final`, `rounds_le` | (a) The count names a winner exactly when round 1 has a continuing ballot.  (b) The winner holds more than half of the last round's continuing ballots.  (c) A last round after round 1 has one continuing candidate exactly when the round before it had two with equal votes, and that round then eliminates by order with the two as the tied set.  (d) The count has at most the larger of 1 and the size of `K` rounds |

`Closed` states that an interpretation counts a ballot only for a member of the continuing set, and `Stable` states both statements of T8.  T10 holds for every interpretation with both properties, as `run_batch_winner`, `run_batch_rounds`, and `run_batch_members` state for the counts from any continuing set without repeated candidates, and `interpret_closed` and `interpret_stable` give them for `interpret`.  `countP_transfer` compares the counts of a set and of a superset: a ballot that counts for a member of `L'` against `S' ⊆ S` counts against `S` for a member of `L'` or of `S` outside `S'`, and `tally_follows` and `majority_subset` derive T8's consequence and T11(a) from it.  `BatchAt` collects the facts of a round that eliminates the batch `B = L(X)`, and `walk` follows the single count or the county count from such a round.  Against every set between the count's next continuing set and the batch round's, the members of `B` that continue have fewer votes than every other continuing candidate (`batch_lt`), so rule 4 eliminates one of them per round, and a candidate with a majority lies outside `B` and keeps it against the count's next continuing set (`batch_holder_rest`).  `county_holder` and `county_rounds` state T11(b) and T11(d) over traces, `trace_tied` and `trace_tie` the two directions of T3(c), and `trace_unique`, `trace_cons`, and `trace_suffix` are lemmas about `Trace` for every decision.

[`StabilityNative.lean`](StabilityNative.lean) is the executable `rcv-stability`, which decided each conclusion natively before its proof.  Its `rounds` mode printed the round lines of the single count and the county count equal to those of `tests/rcv/reference.py`, whose `--county` mode gives the county count and whose charter count without rule 3 gives the single count, on the 283 edge-case files that the reference reads and the 19 contests of the corpus.  The conclusions held on the 303 valid contests of the edge cases' and the corpus's word files, which add the valid array of the word forms to those 302, on 300,000 seeded random contests of up to seven candidates of every kind, four positions, and 40 ballots, on 200,000 random interpretations with `Closed` and `Stable`, and on the 460,460 contests of every multiset of up to six ballots from 20 ballots over three listed candidates and a write-in, under two orders.  The random contests had 563,444 rounds, 74,565 batches, 3,568 single counts that end inside a batch, and 27,803 tied final rounds, the random interpretations 66,556 batches and 1,930 single counts that end inside one, and the exhaustive contests 95,750 tied final rounds.  The run rejected false statements: T10(a) under an interpretation that counts a ballot for a candidate outside the set, as finding 1 of [the review](review.md) describes, on 1,216 cases, T10(c) without the end of the single count on 1,182 batches, T11(c) without its premise on 9,182 contests, and T8 for an overvote of continuing marks alone on 2,229,689 pairs of a ballot and two sets.

Each ballot of the random interpretations carries an order of preference over some candidates and a reason: against a set, it counts for the first candidate of the order in the set, and otherwise it is inactive with the reason.  Every interpretation with `Closed` and `Stable` treats each ballot in this way.  The sets against which a ballot is inactive are closed under subsets, so they share the reason of the empty set, and the others are the sets that meet the candidates whose singletons the ballot counts for.  T8's first statement makes the choices on pairs of those candidates a linear order, whose first member in a set is the choice on the set.

```sh
uv run tests/rcv/edges.py
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Winner rcv-stability
.lake/build/bin/rcv-stability check tmp/rcv-edges/*.words tmp/rcv-data/canonical/*.words
.lake/build/bin/rcv-stability random 1 100000
.lake/build/bin/rcv-stability random 4 100000
.lake/build/bin/rcv-stability random 6 100000
.lake/build/bin/rcv-stability general 2 100000
.lake/build/bin/rcv-stability general 5 100000
.lake/build/bin/rcv-stability exhaustive
.lake/build/bin/rcv-stability planted 3 100000
```

## Program

[`Program.lean`](Program.lean) states the count over words in the verified compiler's dialect: `count` takes a contest array in the word form of the requirements and returns the result words of `Demos.Rcv.Spec.countArray`.  A set of candidates is a word with bit `i - 1` for candidate `i`, the form of the result words' masks, so the continuing set of a round is one word and a test of membership is a shift and a mask.  `validArray` checks the header, the length `3 + 2n + Nk`, the kinds, the order, and every position word in one pass over the array.  `countValid` runs the rounds in a `LeanExe.repeatWhile` whose fuel is one more than the number of counted candidates, the fuel of `Demos.Rcv.Spec.count`, and whose state holds the continuing set, whether the count has ended, the winner, the number of rounds, and the result words.

Each round reads the ballots from the input array.  `examineAt`, a tail recursion that the compiler turns into a loop, examines a ballot's positions from the first and stops at the position that decides the interpretation, and `classify` reads one position word: it passes 0, gives an overvote for a word with bit 63 or with two or more bits, and for a word with one bit, whose position `bitIndex` finds in six tests, gives a vote when the continuing set holds the candidate and passes otherwise.  The union of the words passed gives the reason of a ballot that passes its last position: `blank` when the union is 0, `exhausted` when it holds a counted candidate, and `uncounted` otherwise.  `tallyRound` adds each ballot's slot to an array of 68 counters, slot `i - 1` for a vote for candidate `i` and slots 64 to 67 for the four reasons, and the loop updates the array in place.  A round thus reads each ballot word at most once, and `decideRound` applies the four rules to the counters: `majorityOf`, `continuingOf`, `fewestOf`, `tiedOf`, and `latestOf` take `n` steps each, and `batchOf` computes `L(X)` with `lowerOf` for each continuing `X` in `n²` steps.  The cost of a round is therefore linear in the ballot words plus a term in `n²`.

`compiled.count.bound ws`, the generated bound on the bytes by which a call raises the allocator's `top`, is 152 bytes for an invalid array, the block of the result `[0]`.  For a valid array it is the smaller of two accountings of the growing result words plus the final push, and `count_bound` takes the accounting that charges each push 80 bytes: 232 bytes for the literal `#[1, 0]`; in each of at most `c + 1` rounds, with `c` the number of counted candidates, 600 bytes for the block of 68 counters and `80 (n + 9)` bytes for the round's words; and `16 (s + 1) + 80` bytes for the move of the `s` result words to a block with room for the winner's word.  With `n` and `c` at most 63 and `s` at most 4,610, `count_bound` closes the bound at 481,128 bytes for every array.

The refinement proves that the program computes the specification.  [`RefineBits.lean`](RefineBits.lean) relates `classify` to `Demos.Rcv.Spec.position`, relates the masks of increasing candidate lists to their bits through Mathlib's `Nat.bitIndices`, and turns each loop over the candidates into a fold over `members`, the candidates of a mask.  [`RefineTally.lean`](RefineTally.lean) shows that `examineAt` gives the slot of `Demos.Rcv.Spec.interpret` and that each counter of `tallyRound` counts the ballots of its slot.  [`RefineRule.lean`](RefineRule.lean) proves each loop of `decideRound` against the specification's `find?`, `batch`, `min?`, filters, and `latest`, and `decideRound_eq` states that `decideRound` gives the words of the decision of `Demos.Rcv.Spec.rule`.  [`Refinement.lean`](Refinement.lean) shows that `validArray` decides `Words.Valid`, follows the rounds against `Demos.Rcv.Spec.run` one round at a time in `go_eq`, and concludes `count_eq`.

| File | Contents |
|---|---|
| [`Program.lean`](Program.lean) | The count over words in the dialect |
| [`RefineBits.lean`](RefineBits.lean) | Positions, masks, and loops as folds |
| [`RefineTally.lean`](RefineTally.lean) | The interpretation of a ballot and the counters of a round |
| [`RefineRule.lean`](RefineRule.lean) | The four rules of a round and the words of its decision |
| [`Refinement.lean`](Refinement.lean) | The test of a valid array, the rounds, and `count_eq` |
| [`Compiled.lean`](Compiled.lean) | `verified_compile` of the program |
| [`VerifiedCall.lean`](VerifiedCall.lean) | The call theorem of the export `count` and the closed form of its bound |

## The module's export returns the count over words

`count_callSpec` composes the generated `compiled.count.trapFree` with `count_eq`, as the verified-request skill composes its call theorems.  The bound in its statement is the generated one, so the theorem holds for arrays of every length, and `count_bound` gives its closed form.  Each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, as `#print axioms` at the end of `VerifiedCall.lean` reports.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.Refine.count_eq` | [`Refinement.lean`](Refinement.lean) | `Demos.Rcv.Program.count ws = Demos.Rcv.Spec.countArray ws` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Program.count_callSpec` | [`VerifiedCall.lean`](VerifiedCall.lean) | `Verified.CallSpec compiled.module compiled.tables 22 Demos.Rcv.Spec.countArray compiled.count.bound`: function 22, called with a borrowed word array from a ready store in which `top` can rise by the generated bound, returns without a trap an owned array that holds `countArray` of the input, leaves a ready store, and raises `top` by at most the bound |
| `Demos.Rcv.Program.count_bound` | [`VerifiedCall.lean`](VerifiedCall.lean) | `compiled.count.bound ws ≤ 481128` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Program.count_export` | [`VerifiedCall.lean`](VerifiedCall.lean) | The export `count` is function 22 |

## Testing the count over words

[`tests/rcv/compare.py`](../../tests/rcv/compare.py) compares the module, native Lean, and the reference on word arrays.  For each array it computes the reference's result words and requires the module's export `count` in the Wasmtime host, `rcv-spec array`, `rcv-spec program`, and the result file that `edges.py` or `check.py` wrote to give the same bytes.  The commands below build the call theorem and `rcv-spec`, emit the module, write the edge cases and the corpus's canonical files, and compare them.

```sh
tools/leanrun --timeout 60m lake build Demos.Rcv.VerifiedCall rcv-spec
mkdir -p build/verified
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Compiled Demos.Rcv.Program.compiled.module build/verified/rcvCount.wasm
uv run tests/rcv/edges.py
uv run tests/rcv/check.py
uv run tests/rcv/compare.py tmp/rcv-edges tmp/rcv-data/canonical
```

```
tmp/rcv-edges: 300 arrays, 284 valid contests with 657 rounds
tmp/rcv-data/canonical: 19 arrays, 19 valid contests with 33 rounds
0 arrays with a disagreement
```

The edge cases cover every case of the requirements' list, 220 random contests of up to 12 candidates and 2,000 ballots, and the invalid arrays of the word forms.  The corpus holds the 19 contests whose cast vote records it pins, among them the 2022 District 4 contest, whose result words hold the two rounds of the requirements' report.  `rcv-spec program` runs the program natively, so a disagreement between it and the module points to the compilation, and one between it and `rcv-spec array` to the program.
