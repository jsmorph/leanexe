# Ranked-choice tabulation

This demo is a tabulator for single-winner ranked-choice contests under Oakland City Charter §1105, the rule that Alameda County misconfigured in the November 2022 count of the Oakland Unified School District 4 board race.  The module fixes the charter's rule at compile time, so no setting can be chosen wrong at run time, and its theorems connect the module's bytes to a Lean transcription of the charter.  [The requirements](requirements.md) state the canonical ballot file, the interpretation of a ballot, the rounds, the report, and the theorems, and [the review](review.md) records each reading of the governing texts and the reviews' findings.

[The test corpus](../../tests/rcv/README.md) fetches Alameda County's official round-by-round reports for Oakland's ranked-choice contests from 2022 to 2026 and the cast vote records published for them, and recounts the records under the county's settings.

## Specification

The specification states the requirements' count over lists and natural numbers, with no reference to a program, and every definition computes, so native Lean runs it on canonical files.  A fresh agent reviewed it against the requirements with a model of its own, and [the review](review.md#review-of-the-specification) records the findings and the responses.  The count reads the kinds, the tie-break order, and the position words, while the names enter only the file and the report, and the ballots' identifiers only the file.

| File | Contents |
|---|---|
| [`Contest.lean`](Contest.lean) | The contest structure: the contest identifier and the candidates' names as bytes, the kinds, the tie-break order, and each ballot's optional identifier and position words.  `Contest.WellFormed` states the constraints of a structure |
| [`Spec.lean`](Spec.lean) | The interpretation, the rounds, the canonical file, the report, and the word forms |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the worked example, byte for byte, and of the requirements' edge cases |
| [`Native.lean`](Native.lean) | The executable `rcv-spec`, which runs the specification on canonical files and word arrays |

`interpret` examines a ballot's positions from the first against the continuing set.  `examine` applies the four rules of the interpretation and returns no outcome when it passes the last position, and `passedReason` then gives `blank`, `exhausted`, or `uncounted` from the ballot and the kinds alone.  `tally` interprets every ballot against the continuing set and counts the votes of each continuing candidate and the inactive ballots by reason.  `rule` applies the four rules of a round in order: the majority test `2 vᵣ(i) > Tᵣ`, the end with no winner when `Tᵣ = 0`, the batch of `batch`, which is the largest qualifying `L(X)` of two or more candidates under the strict test, and the elimination of the single candidate with the fewest votes or of the tied candidate latest in the order, which `latest` finds.  `count` runs rounds from the counted set until a rule ends the count, allowing one more round than there are counted candidates, which every count needs at most.

`write` prints a contest structure as its canonical file, and `report` gives the report's bytes, whose header lines are lines 2 to `6 + n` of the file.  `countWords` reads a word array, returns `[0]` unless `Words.Valid` holds, and otherwise returns the result words of the count, and `contestWords` gives the contest words of a structure.  The reader of canonical files, the error report of malformed files, and the decimal printer over words belong to the second increment.

`Cases.lean` checks that `write` prints the worked example's structure as the requirements' ballot file and that `report` gives the requirements' report of it byte for byte, with the example's contest and result words.  Its other checks cover the edge cases that the requirements list under "Tests", apart from the malformed files: overvotes at each position, every pattern of empty positions up to four positions, duplicate and uncounted rankings, ties at the lowest place and in the final round, batches at both sides of the strict test and with tied members, nested qualifying sets, a batch inside which the single count ends, contests with no continuing ballot, no ballots, one candidate, or no counted candidate, 63 candidates and 63 positions, identifiers of 1 and 64 bytes, the contests of T15, the constraints of the structure, and invalid word arrays.  Each expected value comes from the rules by hand.

`rcv-spec` accepts a canonical file only when its own parser's result prints, through `write`, as the file's exact bytes and meets `Contest.WellFormed`.  Its modes are `report FILE`, which writes the report, `words FILE`, which writes the result words of the file's contest words, `array FILE`, which reads a word array and writes the result words, and `district4 FILE`, which compares the report's round lines with the District 4 report of the requirements.  A canonical file of the 2022 District 4 contest, with the candidates in the county's order, the aggregate write-in as candidate 4, the order `1 2 3 4`, and each ballot's `ballotID` as its identifier, gives every round line of the requirements' report.

```sh
tools/leanrun --timeout 20m lake build Demos.Rcv.Cases rcv-spec
tools/leanrun --timeout 10m .lake/build/bin/rcv-spec district4 FILE
```

```
30983 ballots, 19 round lines, 0 differ from the requirements
```
