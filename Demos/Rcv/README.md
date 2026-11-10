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
