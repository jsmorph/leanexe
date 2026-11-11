# Maine ranked-choice tabulation

This module counts single-winner ranked-choice contests under 21-A M.R.S. §723-A, as PL 2025 c. 363 amended it, with the rules of 29-250 C.M.R. ch. 535 where the statute leaves the count to them.  It reads the canonical ballot file of [the Oakland module](../README.md), counts the contest under Maine's rules, and writes a report of every round, and its theorems state that the module returns, for every file, the report that a Lean specification of [the requirements](requirements.md) gives.  [The review](review.md) records each reading of the governing texts, each difference between the statute and the rules with the text that governs it, and the departures of official practice, and [the Maine corpus](../../../tests/rcv/maine/README.md) pins the Secretary of State's reports and cast vote records.

In the Maine count, a ballot's examination ends with the reason `exhausted` at two consecutive empty positions followed by a marked one, an initial test elects a candidate ranked first alone on more than half of all ballots, and the rounds eliminate one candidate at a time until two remain, with no majority stop and no batch.  When two candidates with equal votes remain, the count eliminates the one later in the tie-break order, and of two with unequal votes it names the one with more.  The module shares with the Oakland module the contest structure, the reader and its program, the tally of a round, `run`, the lines of the report, to which the Maine report adds the lines `first i f(i)` of the initial test, the word forms of a round, the lemmas about `run`, and the functions of the Oakland programs that the two counts share.

The module runs as an export in a WebAssembly host and on [the recount page](../README.md#the-browser-page), a WASI process compiled from the same functions reads a file on standard input and writes its report on standard output, the module's translation to C compiles with CompCert, and native Lean runs the specification.  The module's reports of the corpus's six contests equal the reference's, and they name the winner and the eliminations of each of the Secretary of State's summary reports.  Three of them agree with the summary reports in every figure, the 2024 contest when the converter's option `--practice` writes its declared write-in as the Secretary of State counted it, which [the review's departures](review.md#departures-of-official-practice) record, and in the other three each figure lies within 21 votes of the report's, by differences consistent with the rows of one manual-entry spreadsheet, as [the corpus's checks](../../../tests/rcv/maine/README.md#checks) state.  RCTab's rounds under configurations of the Maine count agree with the module's on its edge cases and corpus, apart from the behaviors of RCTab that [the Maine corpus's RCTab section](../../../tests/rcv/maine/README.md#rctab) states.

## Guarantees

`tabulate_callSpec` states the requirements' T1 for the module's export, and the theorems of the WASI process and of the C translation state it for those forms.  The bound in the call theorem is the one that the verified compiler generates, which `tabulate_bound` closes in the size of the file.  A name without a namespace is in `Demos.Rcv.Maine.TabulateProgram`, and `Demos.Rcv.Maine.reportFile b` is the specification's Maine report of the bytes `b`: the shared error report of the first faulty line of a malformed file, and the Maine report of the count of a well-formed one.

| Form | Theorem | Conclusion | Premises |
|---|---|---|---|
| The module's export `tabulate` | `tabulate_callSpec`, [`TabulateCall.lean`](TabulateCall.lean) | Function 64 returns without a trap an owned buffer that holds `Demos.Rcv.Maine.reportFile` of its argument's bytes, leaves a ready store, and raises the allocator's `top` by at most `compiled.tabulate.bound b` | A ready store, a borrowed buffer `b`, and room in the memory cap for `top` to rise by `compiled.tabulate.bound b` |
| The bound | `tabulate_bound`, [`TabulateBound.lean`](TabulateBound.lean) | `compiled.tabulate.bound b ≤ 80 L + 33,958,029` for a file of `L` bytes | `L < 2^32`, which every buffer in a store meets |
| The export `count` | `count_callSpec`, [`TabulateCall.lean`](TabulateCall.lean) | Function 22 returns without a trap an owned array that holds `Demos.Rcv.Maine.countArray` of its argument, the count's result words, and raises `top` by at most `compiled.count.bound ws`, which `count_bound` closes at 486,624 bytes | A ready store, a borrowed word array `ws`, and room for the bound |
| The emitted file | `Demos.Rcv.Maine.TabulateFile.rcvMaine_file` and `rcvMaine_file_decode`, [`TabulateFile.lean`](TabulateFile.lean) | `build/verified/rcvMaine.wasm` holds `encode compiled.module` and decodes to `compiled.module` | The file as it was when `tests/verified/run.sh` checked the theorem |
| The WASI process | `Demos.Rcv.Maine.Process.initial_terminates`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | `_start`, from the module's initial store, exits with status 0 after writing exactly the bytes of the Maine `reportFile` of the input | An input of at most 50,000,000 bytes, StreamFold's host assumptions, a Talos host that satisfies `hostSpec`, and a host that accepts the exit status 0 |
| | `Demos.Rcv.Maine.Process.initial_exits_long`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | `_start` exits with status 22 after writing nothing | An input of more than 50,000,000 bytes, the same host assumptions, and a host that accepts the exit status 22 |
| | `Demos.Rcv.Maine.Process.terminates_bytes`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | One byte sequence encodes the process's module, decodes to it, and is a valid binary, and the module satisfies both theorems above | None |
| The C translation | `tabulate_native`, [`TabulateCall.lean`](TabulateCall.lean) | The C function of function 64 returns without a trap the buffer of the Maine `reportFile` of its argument's bytes, as `tabulate_trapFree` states for the module | Every `Archi` and every semantics of external functions, and a C memory `lx_mem`, of the size that [the C translation](#the-c-translation) gives, that corresponds to a store with room for `compiled.tabulate.bound b` |
| | `tabulate_native_size`, [`TabulateBound.lean`](TabulateBound.lean) | The same | A file of at most `L` bytes and a heap whose `top` and `80 L + 33,958,029` bytes fit in `lx_mem`, which [the C translation](#the-c-translation) states for a fixed size of file |
| The browser page | `tabulate_callSpec` and `tabulate_bound` | The call that the page makes returns the Maine `reportFile` of the file | The page's code establishes the premises of `tabulate_callSpec`, as [the browser page](#the-browser-page) describes, and lies outside the theorems |

The theorems about the specification's count are in the namespace `Demos.Rcv.Maine`, and T2, the theorems of the shared reader, are the Oakland module's.  The count without the initial test runs the rounds of the count from `K` whatever the first rankings, and the single count runs the Oakland rules 1, 2, and 4 with this module's interpretation, eliminating the candidate with the fewest votes until one holds a majority or no ballot continues.  Two fresh agents reviewed both counts against the requirements, as [the review](review.md#review-of-the-counts-of-t11-and-t12) records.

| Requirement | Lean names | Statement |
|---|---|---|
| T3 Winner | `winner_iff`, `winner_majority`, `tied_final`, `rounds_le`, [`Winner.lean`](Winner.lean) | (a) The count names a winner exactly when `K` is not empty.  (b) A winner `w` of the initial test has `N < 2 f(w)`, and when the last round has a continuing ballot, the count names a candidate with more than half of that round's continuing ballots.  (c) When the rounds end with `prev` and `last`, `last` has one continuing candidate exactly when the votes of `prev` are `[(a, v), (b, v)]`, and then `prev` eliminates by order with `[a, b]` as the tied set, which the report prints as a `tie` line.  (d) The count has no rounds exactly when `initialWinner` names a candidate, and at most the larger of 1 and the size of `K` rounds |
| T4 Elimination | `elimination`, [`Rounds.lean`](Rounds.lean) | For a structure that meets `Contest.WellFormed`, every round that eliminates meets `Eliminates`: three or more candidates and the elimination of the candidate that alone has the fewest votes, or of the member latest in the order of the tied set of those with the fewest votes, or two candidates with equal votes, which form the tied set, and the elimination of the one later in the order.  The last round eliminates no one and meets `Concludes`: at most two candidates, and the winner is the one with more votes, the one alone, or none when no candidate continues |
| T5 Conservation | `conservation` | In every round the votes and the four inactive counts sum to the number of ballots, and `continuing` is the sum of the votes |
| T6 Locality | `locality` | When the count has rounds, round 1's continuing set is `K`.  Each round's counts are the numbers of ballots whose interpretation against its continuing set counts for each candidate or has each reason, the next round's continuing set is the current one minus the eliminated candidate, and each `f(i)` is the number of ballots whose first position is single and marks `i` |
| T7 Invariance | `invariance` | Ballots whose position words are a permutation of the contest's give the same count, the same first counts, and the same report |
| T8 Stability | `stability_counts`, `stability_inactive`, `interpret_closed`, `interpret_stable`, [`Stability.lean`](Stability.lean), `stability_rounds`, [`Rounds.lean`](Rounds.lean) | For continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for `w` against `S'` when `w ∈ S'`, and a ballot inactive against `S` is inactive against `S'` with the same reason.  The interpretation counts a ballot only for a member of the continuing set.  From each round of the count to the next, no inactive count decreases, the votes of a candidate that continues do not decrease, and `continuing` does not increase |
| T9 Order | `order_choice` | If an order `π′`, a permutation of the candidates, places the eliminated candidate of each marked tie after the rest of its tied set, the count under `π′` equals the count under the contest's order, and the report's lines differ only in the order line |
| T10 Batch | `batch_winner`, `batch_rounds`, `batch_members`, [`Stability.lean`](Stability.lean) | The Oakland theorem, which holds for every interpretation with `Closed` and `Stable`, applied to this interpretation.  The Maine count has no batch, and no comparison depends on T10 |
| T11 Majority holder | `holder_subset`, `count_majority`, `initial_holder`, `single_winner`, [`Holder.lean`](Holder.lean) | (a) If `w` holds more than half of the continuing ballots against a set `S` without duplicates, it holds more than half against every such `S'` with `w ∈ S' ⊆ S`.  (b) A candidate with more than half of `Tᵣ` in a round of the count continues in every later round, and the count names it.  (c) If the initial test elects `w`, then `w` holds more than half of `T₁` in round 1 of the count without the initial test, which names `w`.  (d) If the single count names `w`, the count names `w` |
| T12 Majority criterion | `majority_criterion`, [`Properties.lean`](Properties.lean) | If more than half of the ballots rank a candidate `w` of `K` first alone, the count has no rounds and names `w`.  If more than half of the continuing ballots against `K` in round 1 of the count without the initial test count for `w`, the count names `w` |
| T13 Condorcet loser | `condorcet_loser` | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, the count does not name `ℓ` |
| T14 Later-no-harm | `later_no_harm` | If position `p` of a ballot marks only `w` and the count names `w`, a ballot whose positions 1 to `p` are the same, with any number of positions after `p`, gives in its place a count with the same rounds that names `w` |
| T15 Monotonicity fails | `monotonicity_fails` | The two contests of the Oakland requirements' T15 meet the constraints and differ only in two ballots, on which the second raises `A` from the second position to the first.  The count of each equals the Oakland count, naming `A` for the first and `B` for the second, and its first counts are 6, 5, and 6, and 8, 5, and 4, of 17 ballots |

Every theorem of both tables depends on no axiom other than `propext`, `Classical.choice`, and `Quot.sound`.  The `#print axioms` commands at the ends of the theorem files and [`ProcessAxioms.lean`](ProcessAxioms.lean) report these axioms, and the last covers every theorem of the namespace `Demos.Rcv.Maine.Process`, those that `verified_compile_wasi` generates among them, while the Oakland module's audit covers the generic theorems of the process.  `Beats` of `Properties.lean` states the requirements' term "beats" with this module's interpretation, and T15 uses the Oakland module's `Raises` and `monotonicityContest`.

## Trusted base

The theorems depend on the items of [the trusted base](../../../docs/trusted-base.md) that the Oakland module's theorems depend on, for WebAssembly modules, WASI Preview 1 processes, and C files, with the Oakland module's [`tabulate.c`](../tabulate.c) as the C executable's calling code.  No theorem checks that the specification states the requirements, and two fresh agents reviewed it against them, as [the review](review.md#review-of-the-specification) records.  [The requirements' list](requirements.md#what-lies-outside-the-theorems) gives what lies outside the theorems: the converter, the kinds of the candidates, the origin of the tie-break order, the agreement of the spreadsheets with the paper ballots, the page's code, the reference, and the scripts.

## Running the module

The commands below build the module, the WASI process, the C executable, and native Lean's executables `rcv-maine` and `rcv-maine-process` from the repository root, with the tools that [the Oakland module's commands](../README.md#running-the-tabulator) need.  The compilations of `Tabulate.lean` and `ProcessWasi.lean` reach 5.7 and 8.8 GiB of resident memory, above `tools/leanrun`'s default limit, so the build command raises the limit, and [the build costs](#running-times-and-build-costs) give their times.  `Tabulate.lean` imports the programs alone, so a change of a proof does not compile the module again.

```sh
tools/leanrun --timeout 90m --memory-high 12G lake build Demos.Rcv.Maine.ProcessAxioms rcv-maine rcv-maine-process
mkdir -p build/verified build/rcv/maine
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Maine.Tabulate Demos.Rcv.Maine.TabulateProgram.compiled.module build/verified/rcvMaine.wasm
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Maine.ProcessModule Demos.Rcv.Maine.Process.module build/rcv/maine/process.wasm
wasm-tools validate build/rcv/maine/process.wasm
tests/rcv/native.sh maine
```

`uv run python -I tests/rcv/maine/fetch.py` verifies the Secretary of State's files in `tmp/rcv-maine-data` and downloads those that are missing, and since www.maine.gov answers the script with HTTP 403, a person saves a missing file from a browser at its manifest path.  `uv run python -I tests/rcv/maine/check.py` then writes the canonical files of the corpus under `tmp/rcv-maine-data/canonical`, as [the Maine corpus](../../../tests/rcv/maine/README.md) describes.  The converter writes the canonical file `FILE` of one contest, and each other form of the table reads `FILE` and writes its report.

| Form | Command | Output |
|---|---|---|
| Converter | `uv run python -I tests/rcv/maine/convert.py KEY --out FILE` | The canonical file of a contest of the corpus's manifest |
| WASI process | `build/tools/leanexe-wasmtime-host run build/rcv/maine/process.wasm < FILE` | The report on standard output |
| Module's export | `build/tools/leanexe-wasmtime-host call build/verified/rcvMaine.wasm tabulate bytes bytes-file:FILE` | The report's bytes in hexadecimal |
| C | `build/rcv/maine/native/rcv-maine-c FILE` | The report on standard output |
| Browser page | `uv run tests/web/serve.py`, then http://127.0.0.1:8000/rcv/ with the Maine module chosen | The report as text, with a link that saves its bytes |
| Native Lean | `.lake/build/bin/rcv-maine report FILE` | The specification's report on standard output |
| Native Lean process | `.lake/build/bin/rcv-maine-process < FILE` | The report on standard output |
| Reference | `uv run tests/rcv/reference.py --maine FILE` | The reference's Maine report |

## Design

| File | Contents |
|---|---|
| [`Spec.lean`](Spec.lean) | The interpretation, the initial test, the decision of a round, the count, the report, the report of a file, and the word forms |
| [`Variants.lean`](Variants.lean) | The count without the initial test and the single count, with which T11 and T12 compare the count |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the requirements' 17-ballot example and its report, byte for byte, of the five-ballot example of the initial test with its words, and of small cases of the rules |
| [`Rounds.lean`](Rounds.lean), [`Stability.lean`](Stability.lean), [`Winner.lean`](Winner.lean), [`Holder.lean`](Holder.lean), [`Properties.lean`](Properties.lean) | T4 to T7, T9, and `stability_rounds`; the other statements of T8, and T10; T3; T11; and T12 to T15 |
| [`Program.lean`](Program.lean) | The count over words in the verified compiler's dialect |
| [`RefineTally.lean`](RefineTally.lean), [`RefineRule.lean`](RefineRule.lean), [`Refinement.lean`](Refinement.lean) | The refinement of the count over words: the examination and the counters of a round, the decision of a round, the first counts, and `count_eq` |
| [`PrintProgram.lean`](PrintProgram.lean), [`PrintProof.lean`](PrintProof.lean) | The Maine report's printer and error printer, and `printReport_eq` |
| [`TabulateProgram.lean`](TabulateProgram.lean), [`TabulateProof.lean`](TabulateProof.lean) | `tabulate`, which composes the shared reader program, the count, and the printers, and `tabulate_eq` |
| [`Tabulate.lean`](Tabulate.lean), [`TabulateCall.lean`](TabulateCall.lean), [`TabulateBound.lean`](TabulateBound.lean), [`TabulateFile.lean`](TabulateFile.lean) | The module `rcvMaine`, its exports and call theorems with the C theorem, the closed forms of the bounds, and the theorems of its emitted file |
| [`Process.lean`](Process.lean), [`ProcessWasi.lean`](ProcessWasi.lean), [`ProcessModule.lean`](ProcessModule.lean), [`ProcessFuture.lean`](ProcessFuture.lean), [`ProcessCharges.lean`](ProcessCharges.lean), [`ProcessProof.lean`](ProcessProof.lean), [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean), [`ProcessAxioms.lean`](ProcessAxioms.lean) | The WASI process, its compilation and command module, its invariant and output, the allocation charges, the refinement, the theorems of the module, and the axiom audit |
| [`Native.lean`](Native.lean), [`PropertiesNative.lean`](PropertiesNative.lean), [`ProcessNative.lean`](ProcessNative.lean) | The executables `rcv-maine`, `rcv-maine-properties`, and `rcv-maine-process` |

### The specification

The specification states the requirements' count over lists, natural numbers, and the 64-bit position words, and every definition computes, so native Lean runs it on canonical files.  `examine` adds rule 1 of the interpretation to the Oakland module's examination: at an empty position, `skipped` ends the examination with `exhausted` when the next position is also empty and some later position is marked.  `interpret` gives the reason of a ballot whose examination passes its last position by the shared `passedReason`.  `firstCounts` gives `f(i)` for each candidate of `K`, the number of ballots whose first position is single and marks it, and `initialWinner` gives the candidate with `2 f(i) > N`, if any.

`decision` applies the two rules of a round to its counts: of two candidates with equal votes it eliminates the one later in the order as a tied set, at most two candidates otherwise end the count, and `lastPlace` eliminates the candidate with the fewest votes, or the tied candidate latest in the order.  `count` ends with the initial test's winner and no rounds, or runs the shared `run` with `interpret` and `decision` from `K`, allowing one more round than `K` has candidates.  `reportLines` adds the `first` lines to the shared report's lines under the module's rule identifier, `reportFile` gives the report or the error report of a file through the shared reader, and `countWords` inserts `f(1)` to `f(n)` after the number of rounds.  [`Variants.lean`](Variants.lean) defines `countWithoutTest`, which runs the rounds of the count from `C₁ = K` whatever the first rankings, and `singleCount`, which runs `Demos.Rcv.Variants.ruleSingle` with this module's interpretation.

### The proofs

The proofs use the shared lemmas about `run` through `Demos.Rcv.Rounds.Ends`, which `decision_ends` proves for `decision`: every elimination names one candidate of the round, and a round of at most one candidate ends the count.  `Demos.Rcv.Rounds.run_trace` then gives a trace of the count's rounds whenever the initial test elects no one (`count_trace`), and `count_initial` gives the count of no rounds otherwise.  `decision_three` equates rule 2 with the Oakland module's rule 4, `Demos.Rcv.Rounds.lowestDecision` of `Demos.Rcv.Rounds.ruleTied`, so that its lemmas apply, and `decision_eq_eliminate`, `decision_eq_winner`, `decision_tied`, and `decision_order` describe the decision's eliminations, its ends, its tied sets, and its use of the order.  Rule 1 of the interpretation ends the examination at a position whatever the continuing set, so the proofs of T8 follow the Oakland module's with one more case.

`decision_single` shows that every elimination of `decision` names one candidate, so a count that eliminates from two or more candidates keeps one, which gives T3(a).  `holder_trace` shows that a candidate that holds a majority against the continuing set of a round is never eliminated and is named: no last place holds a majority, and two candidates of which one holds a majority do not tie, while T8 keeps the majority from round to round through `Demos.Rcv.Stability.majority_subset`.  Every ballot that ranks a candidate of `K` first alone counts for it in round 1 (`firstCount_le_votes`), so the initial test's winner holds a majority there.  A round of the single count that eliminates has no majority and a continuing ballot, so it has two tied candidates or three or more, and `decision` eliminates the same candidate (`decision_of_single`), so the two counts have the same rounds until the single count names a majority holder, whom the count names as well (`single_names`).

The proof of T12 shows that a candidate of `K` ranked first alone on more than half of the ballots holds a majority of round 1 of the count without the initial test, by `firstCount_le_votes`, as every winner of the test does, so that `majority_unique` makes the two the same candidate (`initialWinner_of_first`), and it takes the count's winner from `holder_trace` and from T11(c).  `trace_not_loser` proves T13 over traces of `decision`: when the last round has two candidates, the winner has more votes against their pair, which the other candidate beats, and when the winner continues alone, the round before eliminated one candidate with the fewest votes (`decision_fewest`) against a set that holds both, against which it beats the winner.  The initial test cannot elect `ℓ`, since the ballots that rank `ℓ` first alone count for `ℓ` against every pair that holds it.  For T14, `interpret_prefix` shows that a ballot whose position marks only a continuing candidate has an interpretation that its positions up to that one determine, since rule 1 at an earlier empty position reads the later positions only for a mark, and the Oakland module's `trace_ballots` and `tally_replace` give the second count the trace of the first.  T15 evaluates the two Maine counts and their first counts in the kernel with `decide +kernel` and takes the rest of its statement from the Oakland module's T15.

### The program and the printer

[`Program.lean`](Program.lean) states the Maine count over words in the verified compiler's dialect: `count` takes a contest array in the word form of the requirements and returns the result words of `Demos.Rcv.Maine.countArray`, or `[0]` for an array that is not a valid contest.  It calls the functions of [the Oakland program](../Program.lean) that the two counts share: `classify` of a position word, the loops over the candidates of a mask `continuingOf`, `majorityOf`, `fewestOf`, `tiedOf`, and `latestOf`, `pushRound` of a round's words, `countedOf` and `countedSize` of the counted set, and `validArray`.  `examineAt` adds rule 1 of the interpretation in one pass over a ballot: it keeps the number of empty positions just passed, up to 2, and a marked position after two of them ends the examination with `exhausted`, where the specification looks ahead from the first of them.  `tallyRound` examines the first `m` words of each ballot, so the round of the first positions against `K`, with `m = 1`, holds the first counts `f(i)` at the votes' counters, and `majorityOf` of those counters against `N` gives the initial test's winner.

`decideRound` counts the continuing candidates with `memberCount` and computes rule 2 with `lastPlaceOf`.  Of two candidates it names the one outside the mask of rule 2's lowest elimination, the bit that the exclusive or of the two masks leaves, and when they tie it keeps rule 2's elimination by order.  `countValid` appends the first counts to the result words, ends with the test's winner, and otherwise runs the rounds in a `repeatWhile` as the Oakland program does.  The refinement uses the Oakland refinement's lemmas on words, masks, loops over the candidates, `pushRound`, and `validArray`.  [`RefineTally.lean`](RefineTally.lean) states the program's examination after `g` empty positions as the specification's examination of `g` zero words followed by the remaining words (`examineAt_eq`), [`RefineRule.lean`](RefineRule.lean) equates `lastPlaceOf` with the Oakland module's rule 4 and proves `decideRound_eq`, and [`Refinement.lean`](Refinement.lean) follows the rounds against `Demos.Rcv.Spec.run` with `decision` in `go_eq`, reads the first counts from the counters of the round of first positions (`first_count`), and concludes `count_eq`.

The report's printer of [`PrintProgram.lean`](PrintProgram.lean) is the Oakland printer with this module's rule line and the `first` lines: `pushFirst` prints the line of each counted candidate from the mask of `K` and the first counts of the result words, and the rounds' words start after the first counts.  It takes the mask of `K` as an argument, since a first count of 0 does not tell a counted candidate from an uncounted one, and `tabulate` of [`TabulateProgram.lean`](TabulateProgram.lean) passes `countedOf` of the reader's words.  [`PrintProof.lean`](PrintProof.lean) proves `printReport_eq` as the Oakland printer's proof does, with the facts about the rounds and the winner of `Winner.lean`, and [`TabulateProof.lean`](TabulateProof.lean) proves `printError_eq` and `tabulate_eq`, which follows the two results of the shared reader as the Oakland module's does.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.Maine.Refine.count_eq` | [`Refinement.lean`](Refinement.lean) | `Demos.Rcv.Maine.Program.count ws = Demos.Rcv.Maine.countArray ws` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Maine.TabulateProgram.tabulate_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `bytesOf (tabulate b) = Demos.Rcv.Maine.reportFile (bytesOf b)` for every buffer of fewer than `2^32` bytes |
| `readContest_callSpec`, `printReport_callSpec`, `printError_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | Functions 47, 61, and 63 compute the shared reader's `readResult` of the buffer's bytes, the Maine `printReport`, and the Maine `printError` |
| `exports` | [`TabulateCall.lean`](TabulateCall.lean) | The exports `count`, `readContest`, `printReport`, `printError`, and `tabulate` are functions 22, 47, 61, 63, and 64 |
| `reportFile_length_le` | [`TabulateBound.lean`](TabulateBound.lean) | Every Maine report holds at most 1,304,174 bytes |

### The bounds

[`Tabulate.lean`](Tabulate.lean) compiles the Maine count, the shared reader, and the Maine printers into one module.  The bounds in the call theorems are the generated ones, so the theorems hold for arrays and files of every size, and [`TabulateBound.lean`](TabulateBound.lean) closes them.  The count's bound is 152 bytes for an invalid array, and for a valid one 600 bytes for the counters of the first positions, 232 bytes for the literal `#[1, 0]`, 80 bytes for each of the at most 63 first counts, and either 80 bytes for the push of the test's winner or the rounds: at most 64 rounds of 600 bytes of counters and `80 (n + 9)` bytes of words, and the move of the at most 4,601 result words before the winner's to a block with room for it, at most 486,624 bytes in all.

The bound of `tabulate` adds the reader's `80 L + 10,704` bytes and the printer's, which pushes the first two lines, at most 20,777 bytes of header lines, at most 63 `first` lines, and at most 64 rounds, and copies the report, whose length `reportFile_length_le` bounds, into the buffer that it returns.  The reader and the Oakland printer's functions have the generated costs of the Oakland tabulator's compilation, which the lemmas before `readContest_bound_eq` show by rewriting both compilations' equations, so the Oakland tabulator's bounds of the reader and the round lines apply.  A proof of those equations by `rfl` unfolds the compiled programs and exceeds the heartbeat limit.

### The WASI process

[`Process.lean`](Process.lean) runs the module over stdin and stdout as [the Oakland process](../README.md#the-wasi-process) runs the Oakland module, and shares that process's state, steps, limit, and status `tooLong`.  Its `begin` reads the whole standard input with `readAll 50000000` into one buffer and returns a state that holds the Maine report of the input, which `Demos.Rcv.Maine.TabulateProgram.tabulate` computes.  Each step writes the rest of the report, continuing after short writes, and the process stops with status 0 when the report is written, with an errno when a read or a write returns one, and with status 22, WASI's `fbig`, before `tabulate` and with nothing written, for an input of more than 50,000,000 bytes.  [`ProcessWasi.lean`](ProcessWasi.lean) compiles the functions of `Tabulate.lean` and the process's with `verified_compile_wasi`, [`ProcessModule.lean`](ProcessModule.lean) composes the command module, and [`ProcessNative.lean`](ProcessNative.lean) is the executable `rcv-maine-process`, which runs the process on the operating system's stdin and stdout.

Both processes use the Oakland process's proofs.  The Oakland process's invariant `Demos.Rcv.Process.Writes` takes the bytes of the whole output and a bound on a state's output, `Demos.Rcv.Process.beginWith` is `begin` for a report function, of which this `begin` is an instance by definition, and [the runs of a compiled tabulator's process](../ProcessRun.lean) state the refinement and the runs from a store with room for every compiled program with the facts of `Demos.Rcv.Process.Compiled`.  The files of this directory state the Maine report's invariant `Future`, the relations of the compiled `begin` and `step` to the native ones, which `compiledProcess` bundles with the compiled program, the charges of the compiled functions, and the theorems below as instances.

| Theorem | File | Statement |
|---|---|---|
| `process_output` | [`ProcessFuture.lean`](ProcessFuture.lean) | From an empty output history, for an input of at most 50,000,000 bytes, every run of the native `begin` returns a running state with status 0, from which some execution of the native process writes exactly `expectedOutput` of the input, the bytes of `Demos.Rcv.Maine.reportFile` of the input, and returns status 0 |
| `implements`, `run_initial` | [`ProcessProof.lean`](ProcessProof.lean) | Every modeled run of the module's `_start` that completes without exhausting Talos fuel matches a run of the native process, including runs that stop at an I/O error, a host trap, or a rejected exit |
| `bytes` | [`ProcessProof.lean`](ProcessProof.lean) | One byte sequence encodes the module, decodes to it, is a valid binary, and has `implements` |

`begin_report` and `begin_long` of [`ProcessFuture.lean`](ProcessFuture.lean) state what `begin` returns: the running state of the Maine report with nothing written, or the stopped state with status 22.  [`ProcessCharges.lean`](ProcessCharges.lean) bounds the allocation of `begin` by 4,083,962,173 bytes (`beginCharge_eq`): the allocation of `readAll`'s buffer, 50,004,144 bytes, and the bound of `tabulate` on 50,000,000 bytes, `80 · 50,000,000 + 33,958,029`, which `tabulate_bound` gives since the WASI compilation's bound of `tabulate` is `compiled.tabulate.bound` by definition (`tabulate_bound_eq`).  A copy of a state costs at most 1,304,229 bytes (`copyLimit`) and a write step at most two copies (`stepCharge`), so the memory of a run, `processMemory`, is `beginCharge` and one copy, 4,085,266,402 bytes, and `processMemory_le` states that it fits above the literal pool, which ends at 4,096 bytes, in the 65,535 pages of the module's memory, so neither process theorem has a memory premise.

### The C translation

`tests/rcv/native.sh maine` builds `build/rcv/maine/native/rcv-maine-c` as `tests/rcv/native.sh` builds the Oakland module's `rcv-tabulate-c`, which [the Oakland module's C section](../README.md#the-c-translation) describes: `native-verified build` writes the C text of the translation of `compiled.module` that `compiled.translation_eq` states, has `clightgen` read it back, compares that Clight with the translation, and compiles the text with `ccomp` only when they match.  `ccomp` links the object with the export tables, the Oakland module's [`tabulate.c`](../tabulate.c), compiled with `PROGRAM` defined as `"rcv-maine-c"`, and `tools/native-host.c`.  The option `(cap := 16384)` of `Tabulate.lean`, chosen from the closed bound as the Oakland module's is, gives the translation 16,384 pages of `lx_mem`, 1,073,741,824 bytes, and leaves the module's bytes as they are.  `tabulate_native_size` of [`TabulateBound.lean`](TabulateBound.lean) states that the C function returns the Maine report of a file of at most `L` bytes when `top + 80 L + 33,958,029` is at most the size of `lx_mem`, and `tabulate_native_12000000` states it for every file of at most 12,000,000 bytes from a heap whose `top` is at most 16,777,216 bytes, which covers the corpus's largest file, of 8,262,002 bytes.

### The browser page

[The recount page](../../../tests/web/rcv/index.html), which `uv run tests/web/serve.py` serves at http://127.0.0.1:8000/rcv/, lets the reader choose the Oakland module or this one, `build/verified/rcvMaine.wasm`, and states each module's SHA-256, export, call theorem, file theorem, and bound.  For the Maine module, [`tabulate.js`](../../../tests/web/rcv/tabulate.js) calls the export `tabulate`, function 64, as `tabulate_callSpec` requires, in the way that [the Oakland module's page description](../README.md#the-browser-page) states: a fresh instance for each file, a check that the memory's size, 48 bytes, the file's block, and the bound fit within 65,535 pages, a growth of the memory by that room before `alloc`, and a copy of the returned report.  The page's bound for a file of `L` bytes is `80 L + 33,958,029`, which `tabulate_bound` proves at least `compiled.tabulate.bound b` for every file `b` of fewer than `2^32` bytes.  From the fresh instance's 16 pages, the cap admits files of up to 52,591,297 bytes, and the largest file of the corpus, the 2024 contest of 8,262,002 bytes, needs 703,180,245 bytes of room.

## Tests

### The statements decided natively

[`Native.lean`](Native.lean), the executable `rcv-maine`, decides the conclusions of T3 to T9 and T11 natively through the specification, with the theorems' own propositions `Eliminates` and `Concludes`, and it rejects false variants of the statements, which shows that each test can fail.  `rcv-maine random` draws 78,000 seeded random contests of up to 12 candidates of every kind, 8 positions, and 200 ballots, about a third of them with one candidate ranked first on about 60 percent of the ballots, and the initial test decides 22,909 of them.  The other contests have 99,220 rounds, 16,555 lowest eliminations, and 27,574 eliminations by order, 12,336 of them tied final pairs.  Of 312,000 orders tried for T9, 264,780 meet its hypothesis, 17,753 of them with a marked tie and an order other than the contest's, and the other 47,220 change the count.  T11(a) holds on 730,280 pairs `S' ⊆ S` of subsets of `K` against which a candidate holds a majority, in the contests whose `K` has at most six candidates, T11(b) on 47,349 holders of a majority, T11(c) on the 22,909 contests that the initial test decides, and T11(d) on the 62,224 contests whose single count names a winner.

`rcv-maine pairs` decides both statements of T8 and `Closed` for 4,680 ballots of up to four positions against every pair `S' ⊆ S` of subsets of five candidates of every kind, 1,137,240 pairs of a ballot and two sets, and `rcv-maine check` decides the conclusions of T3 to T9 and T11 on the 320 contests of the edge cases, which have 886 rounds and 352 eliminations by order.  The runs reject T4 with the earliest tied member on 19,329 random contests, T4 with a majority for the winner in the last round on 15,776, T6 with `f(i)` counting first positions that mark `i` among others on 10,749, and T8 for the reading of the overvote that passes a multiple position without a continuing candidate on 53,019 pairs.  They reject T11(b) for a holder of exactly half of a positive `Tᵣ` on 6,615 contests, and T11(d) in the other direction, that the single count names the count's winner, on 10,416, each a contest without a continuing ballot in round 1.

```sh
uv run tests/rcv/maine/edges.py
tools/leanrun --timeout 40m lake build rcv-maine
.lake/build/bin/rcv-maine check tmp/rcv-maine-edges/*.rcv
.lake/build/bin/rcv-maine pairs
.lake/build/bin/rcv-maine random 1 3000 5 4 12
.lake/build/bin/rcv-maine random 2 20000 6 5 30
.lake/build/bin/rcv-maine random 3 4000 8 6 60
.lake/build/bin/rcv-maine random 4 50000 3 3 8
.lake/build/bin/rcv-maine random 5 1000 12 8 200
```

[`PropertiesNative.lean`](PropertiesNative.lean), the executable `rcv-maine-properties`, decides the statements of T12 to T15 natively through the specification.  It reads the contest words of the 321 valid arrays of the edge cases, generates 34,000 seeded random contests of every kind of candidate, in which half of the ballots rank distinct candidates with occasional runs of one or two empty positions and a favorite of any kind takes the first position of up to 60 percent of the ballots, and counts the 106,260 contests of every multiset of up to five ballots of a 20-ballot alphabet of four positions under two orders.  The alphabet holds runs of two empty positions before a ranking at the start and after one, a single empty position between rankings and after a write-in, and overvotes.  Of the 140,581 contests, the initial test decides 50,438.  T12 holds for the 50,438 winners of the test and for 90,039 holders of a majority of round 1 against `K`, 39,601 of them in counts with rounds, T13 for 87,599 counted candidates whom every other beats, 45,995 of them in counts of two or more rounds and 36,899 in counts that the test decides, and T14 for 3,877,218 replacements of a ballot, 1,951,608 of them in counts of two or more rounds and 1,744,194 in counts that the test decides.  `rcv-maine-properties t15` reproduces the two counts of T15, their equality with the Oakland counts, and their first counts.

The runs reject false variants of the statements.  The initial test's part of T12 fails with half of the ballots in place of more than half for 14,086 candidates, and for a candidate outside `K`, which the review's finding 1 excluded, for 4,802.  Its second part fails with the Oakland conclusion that the count ends after round 1 for 80,946 holders and with half of the continuing ballots for 19,047.  T13 fails without its premise that `K` has two or more candidates for 11,242 candidates and with ties allowed in the premise for 10,738, and the Condorcet winner criterion fails for 760.  For T14, a change of a position before `p` changes the count in 559,920 of 1,083,280 replacements, a change of position `p` in 3,127,428 of 4,162,248, and a change of the positions after `p` when the count does not name `w` in 554,304 of 4,517,105, and moving the winner's single position to the front of a ballot changes the winner in 39 of 218,965 cases, the failure of monotonicity that T15 states.

```sh
uv run tests/rcv/maine/edges.py
tools/leanrun --timeout 60m lake build rcv-maine-properties
.lake/build/bin/rcv-maine-properties t15
.lake/build/bin/rcv-maine-properties edges tmp/rcv-maine-edges/*.words
.lake/build/bin/rcv-maine-properties random 1 10000 5 5 30
.lake/build/bin/rcv-maine-properties random 2 4000 8 6 60
.lake/build/bin/rcv-maine-properties random 3 20000 3 4 12
.lake/build/bin/rcv-maine-properties exhaustive 5
```

### The forms compared with the reference

The reference's Maine mode, which an agent wrote from the requirements without the Lean specification, and the specification agree byte for byte on every file of the edge cases and of the corpus.  `rcv-maine compare` gives the reference's report for the 669 canonical files that `tests/rcv/maine/edges.py` writes, 320 of them well formed and the rest malformed, and for the six contests of the corpus, and `rcv-maine compare-words` gives the reference's result words for their 343 word arrays.  The Maine mode uses the Oakland reference's reader, writer, tally, and printer, so the comparison tests the Maine interpretation, the initial test, the rounds, and the `first` lines.

```sh
uv run tests/rcv/maine/edges.py
uv run python -I tests/rcv/maine/check.py
tools/leanrun --timeout 40m lake build rcv-maine
.lake/build/bin/rcv-maine compare tmp/rcv-maine-edges/*.rcv tmp/rcv-maine-data/canonical/*.rcv
.lake/build/bin/rcv-maine compare-words tmp/rcv-maine-edges/*.words tmp/rcv-maine-data/canonical/*.words
```

```
675 files, 326 well formed, 0 differ
343 word arrays, 0 differ
```

[`tests/rcv/maine/tabulate.py`](../../../tests/rcv/maine/tabulate.py) compares the module, its process, C, native Lean, and the reference.  For each canonical file it requires the module's export `tabulate` in the Wasmtime host, `rcv-maine report`, the specification, `rcv-maine program-report`, the program run natively, and the report that `edges.py` or `check.py` wrote to equal the reference's Maine report byte for byte, and for each word array it requires the export `count`, `rcv-maine array`, `rcv-maine program-array`, and the stored result words to equal the reference's.  Its options add to the outputs of a file the standard output of the WASI process in the Wasmtime host, whose control record must be `wasi-exit 0`, that of the native process `rcv-maine-process`, and that of the C executable `rcv-maine-c`.  The run with the Oakland process's module in place of this one's reports all 669 edge files as disagreements, and so does the run with `/bin/cat` in place of the C executable, so the comparison detects a process or an executable that prints something else.

```sh
uv run tests/rcv/maine/tabulate.py --process build/rcv/maine/process.wasm \
  --lean-process .lake/build/bin/rcv-maine-process --native build/rcv/maine/native/rcv-maine-c \
  tmp/rcv-maine-edges tmp/rcv-maine-data/canonical
```

```
tmp/rcv-maine-edges: 669 files, 320 well-formed, 349 malformed, 337 word arrays
tmp/rcv-maine-data/canonical: 6 files, 6 well-formed, 0 malformed, 6 word arrays
0 files or arrays with a disagreement
```

[`tests/rcv/page.mjs`](../../../tests/rcv/page.mjs) with `--count maine` runs the page's calling code under Node on canonical files, with the page's bound, and requires each report to equal the reference's Maine report.  The executable `rcv-maine-bound` of [`MaineBoundMain.lean`](../../../tests/TestSupport/Rcv/MaineBoundMain.lean) prints each file's `compiled.tabulate.bound` in native Lean, and with `--bounds` the script requires the page's bound to be at least that value.  On the 669 edge files and the six contests of the corpus, the reports equal the reference's.  The page's bound is at least the generated bound on all 669 edge files, and the largest generated bound is 3,550,360 bytes, for the file `max-size` of 2,496 bytes, whose bound on the page is 34,157,709 bytes.  For the corpus, `tabulate_bound` proves the page's bound at least the generated bound, and native Lean's evaluation of the generated bound had not finished the corpus's two largest files, of 5,604,408 and 8,262,002 bytes, after 44 minutes.  The script prints the module's SHA-256 and then the lines below.

```sh
tools/leanrun --timeout 60m lake build rcv-maine-bound
tools/leanrun --timeout 60m sh -c \
  '.lake/build/bin/rcv-maine-bound tmp/rcv-maine-edges/*.rcv > tmp/rcv-maine-bounds.txt'
node tests/rcv/page.mjs --count maine --bounds tmp/rcv-maine-bounds.txt tmp/rcv-maine-edges \
  tmp/rcv-maine-data/canonical
```

```
tmp/rcv-maine-edges: 669 files, 320 well-formed, 349 malformed, largest bound 38873949 bytes
tmp/rcv-maine-data/canonical: 6 files, 6 well-formed, 0 malformed, largest bound 694918189 bytes
0 files refused or with a disagreement
```

### The verified compiler's tests

In the verified compiler's tests the module is `rcvMaine`: [the module registry](../../../tests/verified/modules.txt) lists its compilation, and [the case generator](../../../tests/TestSupport/Rcv/MaineCases.lean) gives its cases, which the executable `verified-cases-rcv-maine` prints alone and `verified-cases` prints with those of every other module.  `tests/verified/run.sh --cases rcvMaine` writes `build/verified/rcvMaine.wasm`, validates it with `wasm-tools`, and compares 143 cases between the Wasmtime host and `Demos.Rcv.Maine.countArray` and `Demos.Rcv.Maine.reportFile` in native Lean.  The cases hold the contest words and the canonical files of the contests, the other arrays, and the random contests of the Oakland module's cases, the requirements' two Maine examples, the 17-ballot example cut after each of its lines, and the Oakland example's edits that each break one line.  `lake env lean` on [`TabulateFile.lean`](TabulateFile.lean) checks the file theorems against the file that `run.sh` wrote, and `tests/native/verified.sh --module rcvMaine` translates the module to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same cases.

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

### Running times and build costs

On the corpus's largest file, the 2024 contest of 8,262,002 bytes, the process's module in the Wasmtime 44 host takes 0.09 s with the input from a file (`--stdin-file`) and 0.17 s from a pipe, with a peak resident memory of 50 MiB.  The native process `rcv-maine-process` takes 0.32 s from a file and 0.30 s from a pipe, with a peak of 115 MiB, and the C executable `rcv-maine-c` takes 0.11 s, with a peak of 36 MiB.  An input of 50,000,000 zero bytes gives the error report of 285 bytes with status 0, in 0.09 s from a file and 0.70 s from a pipe, and one more byte gives status 22 with nothing written, from a file, from a pipe, and in the native process.  Each time is the median of three runs on edgexpert-18ff, an AArch64 host, under a CPU quota of two processors while other jobs ran there.

The table gives the time and the peak resident memory of `lake env lean` on the module's three largest compilations, with their imports built, under `tools/leanrun --cpus 2 --threads 2 --memory-high 12G` on the same host.  `Tabulate.lean` runs `verified_compile` on the module, `ProcessWasi.lean` runs `verified_compile_wasi` on the module's functions and the process's, and `ProcessModule.lean` composes the command module and checks its validity and encoding.  `lake build` compiles independent files at the same time, so the build command of [Running the module](#running-the-module) gives the runner a limit of 12 GiB, above the largest peak.

| File | Time (s) | Peak memory (GiB) |
|---|---|---|
| [`Tabulate.lean`](Tabulate.lean) | 1,095 | 5.7 |
| [`ProcessWasi.lean`](ProcessWasi.lean) | 674 | 8.8 |
| [`ProcessModule.lean`](ProcessModule.lean) | 331 | 5.6 |
