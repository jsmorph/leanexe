# Ranked-choice tabulation

This demo is a tabulator for single-winner ranked-choice contests under Section 1105 of the Oakland City Charter.  Its module reads a canonical ballot file, counts the contest in rounds under the charter's rules, and writes a report of every round, and its theorems connect the module's bytes to a Lean specification of [the requirements](requirements.md).  The module fixes the charter's rule at compile time, so no one can choose a wrong setting at run time, and the second line of every report names the governing texts and the date on which they were read.  The module runs as an export in a WebAssembly host and on a browser page, a WASI process compiled from its functions runs the tabulator over standard input and output, the module's translation to C compiles with CompCert, and native Lean runs the specification.

The requirements state the canonical ballot file, the interpretation of a ballot, the rounds, the report, and the theorems, and [the review](review.md) records each reading of the governing texts, the departures of Alameda County's practice from them, and the reviews' findings.  [The test corpus](../../tests/rcv/README.md) gives the URL, size, and SHA-256 of each of the County's round-by-round reports of Oakland's ranked-choice contests from 2022 to 2026 and of the cast vote records published for them, and its scripts fetch the files, convert the records to canonical files, and compare the counts with the County's reports.  [The case study](#case-study-school-director-district-4-2022) recounts the 2022 contest for School Director, District 4, which the County first certified under a faulty setting for a candidate whom the charter's count does not elect.

## Guarantees

T1 is the module's guarantee: the export `tabulate` returns the specification's report of every byte string, the WASI process gives the same report for every input of up to 50,000,000 bytes, and the C translation gives it within its memory bound.  The other theorems state properties of the specification's reader and count, and of the program's decimal reader, for every input, so the properties of the count hold of every report that the module returns.  Every theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, and the sections below give each statement in full.

| Requirement | Lean names | Guarantee | Section |
|---|---|---|---|
| T1 Bytes | `tabulate_callSpec`, `initial_terminates`, `initial_exits_long`, `tabulate_native`, `tabulate_native_12000000` | From a ready store with room for the generated bound, the export returns without a trap `reportFile` of the file's bytes: the error report of a malformed file and the report of the count otherwise.  Under StreamFold's host assumptions and a host that accepts the exit status, the WASI process writes exactly that report and exits with status 0, for every input of up to 50,000,000 bytes, and writes nothing and exits with status 22 for a longer input, and the C function returns it without a trap, for every file of up to 12,000,000 bytes from a heap whose `top` is at most 16,777,216 bytes | [The module's export returns the report of a file](#the-modules-export-returns-the-report-of-a-file), [the WASI process](#the-wasi-process), [the C translation](#the-c-translation) |
| T2 Reader | `read_write`, `write_of_read`, `read_error_first`, `readNumber_whole` | The reader inverts the writer, each contest has exactly one canonical file, the error report names the first faulty line and its role, and the decimal reader inverts the printer | [Theorems of the reader](#theorems-of-the-reader) |
| T3 Winner | `winner_iff`, `winner_majority`, `tied_final`, `rounds_le` | The count names a winner exactly when round 1 has a continuing ballot, the winner holds more than half of the last round's continuing ballots, a last round of one candidate after round 1 follows a round of two tied candidates, and the number of rounds is at most the larger of 1 and the number of counted candidates | [Stability, batches, and the county count](#stability-batches-and-the-county-count) |
| T4 to T7, T9 | `elimination`, `conservation`, `locality`, `invariance`, `order_choice` | Each round eliminates by the charter's rules, the votes and the inactive counts sum to the ballots, each count depends on the round's continuing set alone, the order of the ballots and their identifiers change nothing, and two tie-break orders that make the same choice at each tie that the report marks give the same rounds | [Theorems of the rounds](#theorems-of-the-rounds) |
| T8 Stability | `stability_counts`, `stability_inactive`, `stability_rounds` | A ballot keeps its candidate while the candidate continues, an inactive ballot stays inactive with its reason, and no inactive count decreases from round to round | [Stability, batches, and the county count](#stability-batches-and-the-county-count) |
| T10 Batch | `batch_winner`, `batch_rounds`, `batch_members` | The single count, the count without rule 3, names the same winner, and where the count eliminates a batch, the single count eliminates its members one per round until the batch is gone or the single count ends | [Stability, batches, and the county count](#stability-batches-and-the-county-count) |
| T11 Majority holder | `holder_subset`, `county_majority`, `county_winner`, `county_tied`, `county_rounds_sublist` | Each round of the count with two or more continuing candidates is a round of the county count, which states Alameda County's practice, and when the count's last round is round 1 or holds two or more candidates, the county count names the count's winner | [Stability, batches, and the county count](#stability-batches-and-the-county-count) |
| T12 to T15 | `majority_criterion`, `condorcet_loser`, `later_no_harm`, `monotonicity_fails` | The count meets the majority criterion, never elects a Condorcet loser, and meets later-no-harm, and two contests show that it is not monotonic | [Properties of instant runoff](#properties-of-instant-runoff) |

## Trusted base

The theorems about the module rest on the items that [the trusted base](../../docs/trusted-base.md) lists for WebAssembly modules, among them Lean's kernel, Talos's execution semantics and store definitions, the binary decoder, the agreement of Wasmtime or the browser's engine with Talos, and the host's placement of the argument bytes.  The WASI process adds the items for WASI Preview 1 modules, among them the host specification, Wasmtime's Preview 1, and StreamFold's host assumptions.  The C executable rests instead on the items for C files, among them Talos's store and memory definitions, the Lean copy of Clight, CompCert's proofs and its unverified parts, and the calling code of `tabulate.c` and `tools/native-host.c`.  No theorem checks that the specification states the requirements, and two fresh agents reviewed it against them, as [the review](review.md#review-of-the-specification) records.

The theorems concern the count of a canonical file, and [the requirements' list](requirements.md#what-lies-outside-the-theorems) gives what lies outside them.  The converters write canonical files from vendor exports without proof, the kinds of the candidates rest on filings outside the records, and the origin of the tie-break order is a fact outside the file.  Whether the records agree with the paper ballots is the question of a risk-limiting audit.  The page's JavaScript, the Python reference, and the scripts that compare counts with the County's reports are code without proof, which the tests exercise.

## Running the tabulator

The converters of the table write a canonical ballot file `FILE` from a vendor's records, and each other form reads `FILE` and writes its report.  [Testing the tabulator](#testing-the-tabulator) gives the commands that build the module, the WASI process, the C executable, and native Lean's executables, and `uv run tests/rcv/check.py` writes the canonical files of the corpus under `tmp/rcv-data/canonical`.  [The corpus's scripts](../../tests/rcv/README.md#scripts) fetch the records, convert them, and compare the counts with the County's reports.  `tests/rcv/tabulate.py` requires the module, the WASI process, the C executable, and native Lean to give the reference's report of each file, and `tests/rcv/page.mjs` requires the same of the page's code.

| Form | Command | Output |
|---|---|---|
| Converter of D. Otis's records | `uv run tests/rcv/convert.py CVR --report XML --out FILE` | The canonical file, with the candidates of the County's report |
| Converter of a Dominion export | `uv run tests/rcv/dominion.py EXPORT CONTEST --out FILE` | The canonical file of one contest |
| WASI process | `build/tools/leanexe-wasmtime-host run build/rcv/process.wasm < FILE` | The report on standard output |
| Module's export | `build/tools/leanexe-wasmtime-host call build/verified/rcvTabulate.wasm tabulate bytes bytes-file:FILE` | The report's bytes in hexadecimal |
| C | `build/rcv/native/rcv-tabulate-c FILE` | The report on standard output |
| Browser page | `uv run tests/web/serve.py`, then http://127.0.0.1:8000/rcv/ | The report as text, with a link that saves its bytes |
| Native Lean | `.lake/build/bin/rcv-tabulate report FILE` | The specification's `reportFile` on standard output |
| Native Lean process | `.lake/build/bin/rcv-process < FILE` | The report on standard output |
| Reference | `uv run tests/rcv/reference.py FILE`, or with `--single`, `--county`, or `--suspend` | The report of the charter's count, or of the single count, the county count, or the faulty setting |

## Case study: School Director, District 4, 2022

The 2022 contest for School Director, District 4, of the Oakland Unified School District had three candidates, Mike Hutchinson, Pecolia Manigo, and Nick Resnick, and a write-in line.  Alameda County first certified a count that eliminated Hutchinson in round 1 and gave Resnick the most votes in round 2, and its corrected report, time-stamped 2023-03-10, eliminates Manigo and elects Hutchinson.  The case study recounts D. Otis's records of the contest with the module under the charter and with the reference under the County's faulty setting, and it compares the first count with the corrected report and the second with the first certified figures.

### The charter's count

`tests/rcv/check.py` converts D. Otis's records, 30,983 ballots of five rankings each, to a canonical file.  The candidates are those of the County's report in its order, with the write-ins as candidate 4 of kind `aggregate-writein`, the tie-break order is `1 2 3 4`, and each ballot carries its record's `ballotID` as its identifier.  The module's export `tabulate`, run in the Wasmtime host on that file, returns a report of 766 bytes, and the WASI process, the C executable, and the reference write the same bytes.  The table gives the report's figures beside those of the County's corrected report, whose settings have `useFirstRoundSuspension="False"`, and beside the two counts of [the faulty setting](#the-faulty-setting).  An empty cell is a figure that its source does not give: the reports of the module and the reference list only continuing candidates, and Table A gives only the candidates' votes, the suspended ballots, and the action of each round.

| Figure | Module, under the charter | County's corrected report | Reference, faulty setting | Table A, first certified count |
|---|---|---|---|---|
| Round 1, Hutchinson | 8,227 | 8,227 | 8,112 | 8,112 |
| Round 1, Manigo | 8,190 | 8,190 | 8,153 | 8,153 |
| Round 1, Resnick | 10,015 | 10,015 | 9,954 | 9,954 |
| Round 1, continuing ballots | 26,432 | 26,432 | 26,219 | |
| Round 1, suspended | | | 235 | 235 |
| Round 1, `blank` and `uncounted`, or Blanks | 4,269 and 134 | 4,403 | 4,269 and 134 | |
| Round 1, `overvote`, or Overvotes | 148 | 148 | 126 | |
| Round 1, `exhausted`, or Exhausted | 0 | 0 | 0 | |
| Round 1, eliminated | Manigo | Manigo | Hutchinson | Hutchinson |
| Round 2, Hutchinson | 12,421 | 12,421 | | 0 |
| Round 2, Manigo | | 0 | 11,753 | 11,753 |
| Round 2, Resnick | 12,165 | 12,165 | 12,352 | 12,352 |
| Round 2, continuing ballots | 24,586 | 24,586 | 24,105 | |
| Round 2, `blank` and `uncounted`, or Blanks | 4,269 and 134 | 4,403 | 4,269 and 134 | |
| Round 2, `overvote`, or Overvotes | 173 | 173 | 173 | |
| Round 2, `exhausted`, or Exhausted | 1,821 | 1,821 | 2,302 | |
| Winner | Hutchinson | Hutchinson | Resnick | Resnick |

Round 1 of the charter's count has no majority, since Resnick's 10,015 votes are fewer than half of the 26,432 continuing ballots.  No qualifying set of rule 3 holds two or more candidates: Resnick's votes fall short of the 16,417 of Hutchinson and Manigo together, and the set below Hutchinson holds Manigo alone.  Rule 4 therefore eliminates Manigo, who has 37 fewer votes than Hutchinson.  In round 2 Manigo's 8,190 ballots count 4,194 for Hutchinson and 2,150 for Resnick, 1,821 are exhausted, and 25 are overvotes, so Hutchinson, 1,788 votes behind Resnick in round 1, finishes 256 votes ahead.  His 12,421 votes are more than half of the 24,586 continuing ballots, and rule 1 ends the count with Hutchinson as the winner.  The report marks no tie, so by T9 every tie-break order gives the same rounds.

### The theorems behind the comparison

Apart from the 2022 suspension, the County's practice departs from the charter in two ways that change the rounds of a report: it eliminates one candidate per round where §1105(f) eliminates a batch, and it counts past a majority until two candidates remain.  T10 (`batch_winner`, `batch_rounds`, `batch_members`) covers the first departure: the single count, which applies the charter's rules without the batch of rule 3, names the charter's winner, and where the charter's count eliminates a batch, the single count eliminates its members one per round.  [The comparison rule](requirements.md#comparison-with-alameda-countys-reports) offsets the County's round numbers by `m` − 1 after a batch of `m`, since the County, like the single count, eliminates the batch's members one per round.  District 4's count has no batch, so the offset is zero, and the module's round `r` is the County's round `r`.

T11 compares the charter's count with the county count, the requirements' statement of the County's practice, which eliminates one candidate per round while three or more continue and ends at the first round with two or fewer.  By T11(d) (`county_rounds_sublist`), each round of the charter's count with two or more continuing candidates is a round of the county count with the same continuing set, votes, and inactive counts.  Both rounds of District 4 hold two or more candidates, and the county count, by its definition, has two rounds for three counted candidates, so its rounds are the module's, and T11(c) (`county_winner`) gives Hutchinson as its winner.  The charter's majority stop and the County's stop at two candidates fall in the same round, so the corrected report has no round beyond the charter's count.

The theorems relate the module's count to the county count, a Lean definition, and they say nothing about the County's report.  `check.py` compares the report's figures with the reference's counts, and `district4.py` with its own recount of D. Otis's records, both through the requirements' mapping of the categories: Blanks is `blank` plus `uncounted`, Overvotes is `overvote`, and Exhausted is `exhausted`.  Every figure of both rounds agrees, and the 4,403 Blanks include the 134 ballots that rank only write-ins, which the count passes over under Cal. Elec. Code §15341.

### The faulty setting

Each 2022 Oakland report of the corpus other than District 4's sets `useFirstRoundSuspension="True"`, which suspended ballots in round 1.  The requirements state its rule as the faulty setting: the county count, except that round 1 counts as suspended each ballot whose first position is empty or holds one uncounted candidate and whose interpretation in round 1 counts for a candidate or is `overvote`.  From round 2 on, every ballot counts as the requirements state.  `reference.py --suspend` applies the rule to the canonical file, and `district4.py` and `recount.py --suspend` apply it again to D. Otis's records.  The rule reproduces every round, Suspended rows included, of the six other 2022 reports with that setting whose contests have cast vote records in the corpus.

In District 4 the rule suspends 235 ballots, 100 whose first ranking is empty and 135 that rank a write-in first.  Under the charter, 115 of them count for Hutchinson in round 1, 37 for Manigo, and 61 for Resnick, and 22 are overvotes, as slide 5 of the Registrar's presentation shows.  The suspension takes 78 more votes from Hutchinson than from Manigo, so Hutchinson's lead of 37 votes becomes a deficit of 41, and round 1 eliminates him.  In round 2 his 8,112 ballots count 3,492 for Manigo and 2,327 for Resnick, and the suspended ballots return, 108 of them for Manigo and 71 for Resnick.  Resnick finishes with 12,352 votes against Manigo's 11,753, and the faulty setting names him.  Table A on slide 6, under the caption "Table A shows the certified results using the incorrect RCV configuration", gives the same votes in both rounds and the same 235 suspended ballots.

No module implements the faulty setting, since it departs from §1105(d)(1), which counts every ballot in round 1 for its first choice, and from §1105(g), which advances a ballot past a ranking with no candidate "in the first or any round".  A module counts under the governing texts that its rule identifier names.  The reference's report under the faulty setting carries the rule line `rule alameda-county-count first-round-suspension`, so that no one can take it for the charter's report.

### What is proved and what is tested

The theorems cover the charter's count from the bytes of the canonical file to the bytes of the report.  T1 (`tabulate_callSpec`) states that the module's export returns the specification's report of every file, so the module's report of District 4's file is the specification's report of it, and `initial_terminates` and `tabulate_native` carry the statement to the WASI process and the C function.  T9, T10, and T11 are theorems about the specification's count of every contest, this one included, and the theorems rest on [the trusted base](#trusted-base).

Python scripts without proof produce or check everything else.  The converter writes the canonical file from D. Otis's records, and `check.py` tests it by reading the identifiers and rankings back from the file.  `reference.py --suspend`, `recount.py --suspend`, and `district4.py` compute the faulty setting, and `district4.py` compares its figures with those of slides 5 and 6, which it holds as constants because the slides are images.  The scripts test D. Otis's records against the County's counts alone, and whether the records agree with the paper ballots lies outside the theorems and the scripts.

### Reproducing the case study

The commands below assume the Wasmtime host and `build/rcv/process.wasm`, which [Testing the tabulator](#testing-the-tabulator) builds.  They fetch the corpus, write the canonical files, run the WASI process on District 4 and print the SHA-256 of its report, print the reference's report under the faulty setting, and recount D. Otis's records with `district4.py`, which compares its counts with the corrected report and with slides 5 and 6.  The module `build/verified/rcvTabulate.wasm` has the SHA-256 `769a3ba4114421d701f57d3fa31ffe9d8661d7fcf6c159e0fb206063e7c90dbc`, the canonical file has 803,011 bytes and the SHA-256 `0a1019fb5a51dcf497c686765a98002a6e0791720a57665ea8a2cd7c0df2a817`, and its report has 766 bytes and the SHA-256 `86efd87691d0e6dd8732e4778f6e53556e7fedfb7c59f59e942ac865076dc465`.  `district4.py` prints the output below and exits with status 0, and its line on the write-in gives round 1 with the aggregate write-in counted as a fourth candidate, figures that match neither of the County's counts.

```sh
uv run tests/rcv/fetch.py
uv run tests/rcv/check.py
build/tools/leanexe-wasmtime-host run build/rcv/process.wasm \
  < tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv | sha256sum
uv run tests/rcv/reference.py --suspend tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv
uv run tests/rcv/district4.py
```

```
248/Oakland/007-SchoolDirector_District_4: 30,983 ballots in the CVR, report timestamp 2023-03-10T10:00:31.077, useFirstRoundSuspension False
corrected round 1: Hutchinson 8,227, Manigo 8,190, Resnick 10,015; blanks 4,403, overvotes 148: agrees
corrected round 2: Hutchinson 12,421, Resnick 12,165; blanks 4,403, overvotes 173, exhausted 1,821: agrees
suspension round 1: Hutchinson 8,112, Manigo 8,153, Resnick 9,954; blanks 4,403, overvotes 126, suspended 235: agrees
suspension round 2: Manigo 11,753, Resnick 12,352; blanks 4,403, overvotes 173, exhausted 2,302: agrees
suspended ballots under the correct configuration: MIKE HUTCHINSON 115, PECOLIA MANIGO 37, NICK RESNICK 61, overvotes 22: agrees
write-in as a candidate, round 1: MIKE HUTCHINSON 8,147, PECOLIA MANIGO 8,176, NICK RESNICK 9,977, Write-in 269
District 4 checks pass
```

## The count

### Specification

The specification states the requirements' count over lists, natural numbers, and 64-bit position words, with no reference to a program, and every definition computes, so native Lean runs it on canonical files.  Two fresh agents reviewed it against the requirements, each with a model of its own, and [the review](review.md#review-of-the-specification) records their findings and the responses.  The count reads the kinds, the tie-break order, and the position words, while the names enter only the file and the report, and the ballots' identifiers only the file.

| File | Contents |
|---|---|
| [`Contest.lean`](Contest.lean) | The contest structure: the contest identifier and the candidates' names as bytes, the kinds, the tie-break order, and each ballot's optional identifier and position words.  `Contest.WellFormed` states the constraints of a structure |
| [`Spec.lean`](Spec.lean) | The interpretation, the rounds, the canonical file, the report, and the word forms |
| [`Read.lean`](Read.lean) | The reader of the canonical file, the error rule by line number, and the report of a file |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the worked example, byte for byte, and of the requirements' edge cases |
| [`Native.lean`](Native.lean) | The executable `rcv-spec`, which runs the specification and the program on canonical files and word arrays |

`interpret` examines a ballot's positions from the first against the continuing set.  `examine` applies the four rules of the interpretation and returns no outcome when it passes the last position, and `passedReason` then gives `blank`, `exhausted`, or `uncounted` from the ballot and the kinds alone.  `tally` interprets every ballot against the continuing set and counts the votes of each continuing candidate and the inactive ballots by reason.  `rule` applies the four rules of a round in order: the majority test `2 vᵣ(i) > Tᵣ`, the end with no winner when `Tᵣ = 0`, the batch of `batch`, which is the largest qualifying `L(X)` of two or more candidates under the strict test, and the elimination of the single candidate with the fewest votes or of the tied candidate latest in the order, which `latest` finds.  `count` runs rounds from the counted set until a rule ends the count, allowing one more round than there are counted candidates, while T3(d) of the requirements bounds the rounds by the larger of 1 and the number of counted candidates.

`write` prints a contest structure as its canonical file, and `report` gives the report's bytes, whose header lines are lines 2 to `6 + n` of the file.  `countWords` reads a word array, returns `[0]` unless `Words.Valid` holds, and otherwise returns the result words of the count, and `contestWords` gives the contest words of a structure.  `Read.lean` states the reader of canonical files and the error report of malformed files, which [the reader](#the-reader) describes.

`Cases.lean` checks that `write` prints the worked example's structure as the requirements' ballot file and that `report` gives the requirements' report of it byte for byte, with the example's contest and result words.  Its other checks cover the edge cases that the requirements list under "Tests", apart from the malformed files: overvotes at each position, every pattern of empty positions up to four positions, duplicate and uncounted rankings, ties at the lowest place and in the final round, batches at both sides of the strict test and with tied members, nested qualifying sets, a batch inside which the single count ends, contests with no continuing ballot, no ballots, one candidate, or no counted candidate, 63 candidates and 63 positions, identifiers of 1 and 64 bytes, the contests of T15, the constraints of the structure, and invalid word arrays.  Each expected value comes from the rules by hand.

`rcv-spec` accepts a canonical file only when its own parser's result prints, through `write`, as the file's exact bytes and meets `Contest.WellFormed`.  It reads and writes word arrays as the reference does, packed as little-endian 64-bit words.  Its modes are `report FILE`, which writes the report, `contest-words FILE`, which writes the file's contest words, `words FILE`, which writes the result words of the file's contest words, `array FILE`, which reads a word array and writes the result words of `countArray`, `program FILE`, which writes those of the program `Demos.Rcv.Program.count` run natively, and `district4 FILE`, which compares the report's round lines with the District 4 report of the requirements.  `tests/rcv/check.py` writes the canonical file of the 2022 District 4 contest, with the candidates in the County's order, the aggregate write-in as candidate 4, the order `1 2 3 4`, and each ballot's `ballotID` as its identifier, and the specification's report of it holds every round line of the requirements' report.

```sh
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Cases rcv-spec
tools/leanrun --timeout 10m .lake/build/bin/rcv-spec district4 \
  tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv
```

```
30983 ballots, 19 round lines, 0 differ from the requirements
```

The Python reference of `tests/rcv/` and the specification agree byte for byte on every file that `tests/rcv/edges.py` and `tests/rcv/check.py` write.  On the 284 edge-case files that the reference reads and the 19 contests of the corpus, `rcv-spec report` gives the reference's report, and on their contest words and the 17 arrays of the word forms alone, `rcv-spec array` gives the reference's result words.  `rcv-spec` rejects each of the 349 files for which the reference gives an error report.

### Theorems of the rounds

[`Rounds.lean`](Rounds.lean) proves T4, T5, T6, T7, and T9 of the requirements over `countContest`, `reportLines`, and `report`, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  T4 assumes `Contest.WellFormed`, whose tie-break order is a permutation of the candidates, and T9 assumes that the new order is such a permutation.  T5, T6, and T7 hold for every contest structure.  T7 states the requirement over contest structures, and the requirement over files follows from it with T2, since the reader returns the structure whose writing is each well-formed file.

| Theorem | Lean name | Statement |
|---|---|---|
| T4 Elimination | `elimination` | Every round that eliminates meets `Eliminates`: `Tᵣ > 0`, no candidate holds a majority, and the elimination is a batch of two or more candidates that equals a qualifying `L(X)` and contains every qualifying `L(Y)`, or, when no qualifying set has two or more candidates, the candidate that alone has the fewest votes, or the two or more candidates with the fewest votes, marked as tied, and their member latest in the order.  The last round eliminates no one and ends by rule 1, with the candidate that holds a majority as the winner, or by rule 2, with `Tᵣ = 0` and no winner |
| T5 Conservation | `conservation` | In every round the votes and the four inactive counts sum to the number of ballots, and `continuing` is the sum of the votes |
| T6 Locality | `locality` | Round 1's continuing set is `K`.  Each round's votes and inactive counts are the numbers of ballots whose interpretation against that round's continuing set counts for each candidate or has each reason, every round but the last eliminates, and the next round's continuing set is the current one minus the eliminated candidates |
| T7 Invariance | `invariance` | Ballots whose position words are a permutation of the contest's give the same count and the same report, which covers a permutation of the ballots and any change of their identifiers |
| T9 Order | `order_choice` | If an order `π′` places the eliminated candidate of each marked tie after the rest of its tied set, the count under `π′` equals the count under the contest's order, and the report's lines differ only in the order line |

`run` takes the decision of a round as an argument, and `count` passes `rule`.  `Trace` describes the rounds of a count under any interpretation and any decision: a round in which the decision gives a winner is the last, and a round that eliminates is followed by the trace from its continuing set minus the eliminated candidates.  `Ends` states the properties of a decision that bound the rounds: every elimination names at least one candidate and only candidates of the continuing set, and a continuing set of at most one candidate ends the count.  `rule_ends` proves them for `rule`.  For such a decision, `run_trace` gives a trace whenever the fuel is at least the larger of 1 and the size of the continuing set, and `Trace.run_eq` and `run_fuel` show that every such fuel gives the same count.  `count_trace` applies these lemmas to `count`, whose fuel `K.length + 1` therefore suffices, and `Trace.length_le` bounds the rounds by the larger of 1 and the size of `K`.  `Trace.mem`, `Trace.head`, `Trace.next`, and `Trace.last_round` give each round's counts, continuing set, and decision, `run_perm` shows that the order of the ballots leaves the count unchanged, and `run_congr` equates the counts under two decisions that agree on every round of one of them.  For `rule`, `batch_some` and `batch_none` describe the fold of rule 3, `ruleTied_eq_fewest` equates the tied set of rule 4 with the candidates that have the fewest votes, and `latest_spec` shows that `latest` returns the member of the tied set latest in an order that holds each candidate once.

[`RoundsNative.lean`](RoundsNative.lean) is the executable `rcv-rounds`, which decided each statement natively through the specification before its proof.  Its `edges` mode reads contest-word files and gives each valid array the contest identifier `case`, the names `C1` to `Cn`, and no ballot identifiers, and its `random` mode draws seeded random contests whose ballots carry an identifier with probability one in three.  The conclusions of T4, T5, T6, and T7 held on the 285 valid contests of the edge cases' word files and on 10,000 seeded random contests of up to eight candidates of every kind, five positions, and 60 ballots, which together have 19,189 rounds, among them 919 batches, 3,829 lowest eliminations, and 4,156 eliminations by order.  Of 41,686 random orders tried for T9, 34,292 met its hypothesis, 4,168 of them in counts with a marked tie and with an order other than the contest's, and each of the 34,292 gave the same count and the stated report lines, while 7,394 of the orders that failed the hypothesis changed the count.  The runs rejected false variants of the statements: T4 with the earliest instead of the latest tied member on 3,017 contests, T4 with the smallest qualifying set of two or more instead of the largest on 91, T5 with the continuing ballots counted twice on 9,125, and T6 with an unchanged continuing set on 4,085.  Each mode prints these counts and exits with status 1 when a statement fails.

```sh
uv run tests/rcv/edges.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Rounds rcv-rounds
tools/leanrun --timeout 20m .lake/build/bin/rcv-rounds edges tmp/rcv-edges/*.words
tools/leanrun --timeout 20m .lake/build/bin/rcv-rounds random 1 4000 5 4 12
tools/leanrun --timeout 20m .lake/build/bin/rcv-rounds random 2 4000 6 4 30
tools/leanrun --timeout 20m .lake/build/bin/rcv-rounds random 3 2000 8 5 60
```

### Stability, batches, and the county count

[`Variants.lean`](Variants.lean) defines the single count and the county count of the requirements' theorems as `run` from `K`, with the count's interpretation and fuel and a decision of their own.  `ruleSingle` applies rules 1, 2, and 4, and `ruleCounty` applies rule 4 while three or more candidates continue and otherwise ends the count, where `countyWinner` names the candidate with more votes, the candidate alone, or none.  Both take rule 4 from `lowestDecision` and `ruleTied`, as `rule` does, and `ruleSingle_ends` and `ruleCounty_ends` prove `Ends` for them, so the lemmas about `Trace` apply to the three counts.  [`Stability.lean`](Stability.lean), [`Batch.lean`](Batch.lean), [`Holder.lean`](Holder.lean), and [`Winner.lean`](Winner.lean) prove T8, T10, T11, and T3, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.

| Theorem | Lean name | Statement |
|---|---|---|
| T8 Stability | `stability_counts`, `stability_inactive`, `stability_rounds` | For continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for `w` against `S'` when `w ∈ S'`, and a ballot inactive against `S` is inactive against `S'` with the same reason.  From each round of the count to the next, no inactive count decreases, the votes of a candidate that continues do not decrease, and `continuing` does not increase |
| T10 Batch | `batch_winner`, `batch_rounds`, `batch_members` | (a) The single count names the count's winner, or both name none.  (b) The counts of the count's rounds form a sublist of the single count's, or all but the last do, the single count names the count's winner, and its last continuing set strictly contains the count's.  (c) From a round of the single count with the continuing set of a round of the count that eliminates the batch `B`, each of the next `B.length` rounds ends the single count or eliminates exactly one member of `B` that continues in it |
| T11 Majority holder | `holder_subset`, `county_majority`, `county_winner`, `county_tied`, `county_rounds_sublist` | (a) A candidate with a majority against a continuing set has one against every smaller continuing set that holds it.  (b) A candidate with a majority in a round of the county count continues in every later round, and the county count names it.  (c) If the count names `w` and its last round is round 1 or has two or more continuing candidates, the county count names `w`.  If the count's last round has one candidate and is not round 1, the county count's last round has the counts of the count's round before it.  (d) The counts of the count's rounds with two or more continuing candidates form a sublist of the county count's |
| T3 Winner | `winner_iff`, `winner_majority`, `tied_final`, `rounds_le` | (a) The count names a winner exactly when round 1 has a continuing ballot.  (b) The winner holds more than half of the last round's continuing ballots.  (c) A last round after round 1 has one continuing candidate exactly when the round before it had two with equal votes, and that round then eliminates by order with the two as the tied set.  (d) The count has at most the larger of 1 and the size of `K` rounds |

`Closed` states that an interpretation counts a ballot only for a member of the continuing set, and `Stable` states both statements of T8.  T10 holds for every interpretation with both properties, as `run_batch_winner`, `run_batch_rounds`, and `run_batch_members` state for the counts from any continuing set without repeated candidates, and `interpret_closed` and `interpret_stable` give them for `interpret`.  `countP_transfer` compares the counts of a set and of a superset: a ballot that counts for a member of `L'` against `S' ⊆ S` counts against `S` for a member of `L'` or of `S` outside `S'`, and `tally_follows` and `majority_subset` derive T8's consequence and T11(a) from it.  `BatchAt` collects the facts of a round that eliminates the batch `B = L(X)`, and `walk` follows the single count or the county count from such a round.  Against every set between the count's next continuing set and the batch round's, the members of `B` that continue have fewer votes than every other continuing candidate (`batch_lt`), so rule 4 eliminates one of them per round, and a candidate with a majority lies outside `B` and keeps it against the count's next continuing set (`batch_holder_rest`).  `county_holder` and `county_rounds` state T11(b) and T11(d) over traces, `trace_tied` and `trace_tie` the two directions of T3(c), and `trace_unique`, `trace_cons`, and `trace_suffix` are lemmas about `Trace` for every decision.

[`StabilityNative.lean`](StabilityNative.lean) is the executable `rcv-stability`, which decided each conclusion natively before its proof.  Its `rounds` mode writes the round lines and the winner line of the count, the single count, or the county count of each contest-word file, and [`tests/rcv/variants.py`](../../tests/rcv/variants.py) requires them to equal those of `tests/rcv/reference.py` in its default, `--single`, and `--county` modes, whose single count is the charter's count without rule 3.  They agree on the 285 valid contests of the edge cases' word files, whose three counts have 658, 758, and 749 rounds, and on the 19 contests of the corpus, with 33, 46, and 60 rounds.  A copy of the reference whose single count keeps rule 3 fails 36 of the comparisons.  The conclusions held on the 304 valid contests of the edge cases' and the corpus's word files, which add the valid array of the word forms to those 303, on 300,000 seeded random contests of up to seven candidates of every kind, four positions, and 40 ballots, on 200,000 random interpretations with `Closed` and `Stable`, and on the 460,460 contests of every multiset of up to six ballots from 20 ballots over three listed candidates and a write-in, under two orders.  The random contests had 563,444 rounds, 74,565 batches, 3,568 single counts that end inside a batch, and 27,803 tied final rounds, the random interpretations 66,556 batches and 1,930 single counts that end inside one, and the exhaustive contests 95,750 tied final rounds.  The run rejected false statements: T10(a) under an interpretation that counts a ballot for a candidate outside the set, as finding 1 of [the review](review.md) describes, on 1,216 cases, T10(c) without the end of the single count on 1,182 batches, T11(c) without its premise on 9,182 contests, and T8 for an overvote of continuing marks alone on 2,229,689 pairs of a ballot and two sets.

Each ballot of the random interpretations carries an order of preference over some candidates and a reason: against a set, it counts for the first candidate of the order in the set, and otherwise it is inactive with the reason.  Every interpretation with `Closed` and `Stable` treats each ballot in this way.  The sets against which a ballot is inactive are closed under subsets, so they share the reason of the empty set, and the others are the sets that meet the candidates whose singletons the ballot counts for.  T8's first statement makes the choices on pairs of those candidates a linear order, whose first member in a set is the choice on the set.

```sh
uv run tests/rcv/edges.py
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build Demos.Rcv.Winner rcv-stability
uv run tests/rcv/variants.py tmp/rcv-edges tmp/rcv-data/canonical
.lake/build/bin/rcv-stability check tmp/rcv-edges/*.words tmp/rcv-data/canonical/*.words
.lake/build/bin/rcv-stability random 1 100000
.lake/build/bin/rcv-stability random 4 100000
.lake/build/bin/rcv-stability random 6 100000
.lake/build/bin/rcv-stability general 2 100000
.lake/build/bin/rcv-stability general 5 100000
.lake/build/bin/rcv-stability exhaustive
.lake/build/bin/rcv-stability planted 3 100000
```

### Properties of instant runoff

[`Properties.lean`](Properties.lean) proves T12, T13, T14, and T15 of the requirements over `countContest`, `singleCount`, and `countyCount`, and each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  T12, T13, and T14 hold for every contest structure, so for every structure that meets `Contest.WellFormed`, and T15 proves that its two contests meet it.  `Beats` states the requirements' term "beats": more ballots count for one candidate than for the other against the continuing set of the two.  `Raises` states "raising": a position that marks only the candidate moves to an earlier position, and the other positions keep their order.  T14 lets the new ballot hold any number of positions after `p`, and its premise that the count names `w` makes `w` a counted candidate.

| Theorem | Lean name | Statement |
|---|---|---|
| T12 Majority criterion | `majority_criterion` | If more than half of the continuing ballots against `K` count for `w`, the count has one round and names `w`, and the single count and the county count name `w` |
| T13 Condorcet loser | `condorcet_loser` | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, the count does not name `ℓ` |
| T14 Later-no-harm | `later_no_harm` | If position `p` of a ballot marks only `w` and the count names `w`, a ballot whose positions 1 to `p` are the same in its place gives a count with the same rounds that names `w` |
| T15 Monotonicity fails | `monotonicity_fails` | The two contests of the requirements meet the constraints and differ only in two ballots, on which the second raises `A` from the second position to the first.  The count names `A` for the first and `B` for the second, and round 1 of each eliminates one candidate with the fewest votes alone |

T12 evaluates round 1 of the count and of the single count with `rule_holder` and `find_holder`, and it takes the county count's winner from `county_holder`, the form of T11(b) over traces.  `trace_not_loser` proves T13 over traces of the count for every interpretation that satisfies `Closed` and `Stable`.  When two or more candidates continue in the last round, the winner's majority persists by T11(a), `majority_subset`, against the pair of itself and any other candidate, which beats it there.  When the winner continues alone, the round before eliminated one candidate, since a batch leaves two or more (`BatchAt.rest_two_le`), and that candidate had the fewest votes against a set with the members of the pair of it and the winner, against which it beats the winner.  `interp_congr` gives the same interpretation against two sets with the same members.  For T14, `interpret_prefix` shows that a ballot whose position marks only a continuing candidate has an interpretation that its positions up to that one determine, `trace_winner_all` shows that the count's winner continues in every round, and `trace_ballots` shows, for every interpretation and decision, that ballots giving every round of a trace the same counts give the same trace.  T15 evaluates the counts and the constraints of its two contests in the kernel with `decide +kernel`.

[`PropertiesNative.lean`](PropertiesNative.lean), the executable `rcv-properties`, decided each statement natively through the specification before its proof.  It reads the contest words of the edge cases, 285 contests, and it generates 34,000 seeded random contests of every kind of candidate, in which half of the ballots rank distinct candidates and one candidate takes the first position of up to 60 percent of the ballots, and the 106,260 contests of every multiset of up to five ballots of a 20-ballot alphabet under two orders.  On these inputs T12 held for 88,790 candidates with a majority in round 1, 70,876 of them among three or more counted candidates, T13 for 89,043 counted candidates whom every other beats, 24,087 of them in counts of two or more rounds, and T14 for 3,766,242 replacements of a ballot, 1,163,880 of them in counts of two or more rounds, and `rcv-properties t15` reproduced the two counts of T15.  The run rejected false variants of the statements.  T12 with half of the continuing ballots in place of more than half failed for 42,332 candidates, and T12 with the county count ending after round 1 failed for 70,876.  T13 without its premise that `K` has two or more candidates failed for 9,925 candidates, T13 with ties allowed in the premise failed for 8,558, and the Condorcet winner criterion, which instant runoff does not meet, failed for 827.  For T14, a change of a position before `p` changed the count in 509,465 of 907,670 replacements, a change of position `p` in 4,082,451 of 4,354,218, and a change of the positions after `p` when the count does not name `w` in 551,391 of 3,785,073.  Moving the winner's single position to the front of a ballot changed the winner in 28 of 190,820 cases, the failure of monotonicity that T15 states.  The checks of T14 and of monotonicity take at most 48 positions of each contest, spread evenly over its ballots.

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

## The count over words

### Program

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
| [`File.lean`](File.lean) | The file theorems of `build/verified/rcvCount.wasm` |

### The module's export returns the count over words

`count_callSpec` composes the generated `compiled.count.trapFree` with `count_eq`, as the verified-request skill composes its call theorems.  The bound in its statement is the generated one, so the theorem holds for arrays of every length, and `count_bound` gives its closed form.  Each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, as `#print axioms` at the end of `VerifiedCall.lean` reports.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.Refine.count_eq` | [`Refinement.lean`](Refinement.lean) | `Demos.Rcv.Program.count ws = Demos.Rcv.Spec.countArray ws` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Program.count_callSpec` | [`VerifiedCall.lean`](VerifiedCall.lean) | `Verified.CallSpec compiled.module compiled.tables 22 Demos.Rcv.Spec.countArray compiled.count.bound`: function 22, called with a borrowed word array from a ready store in which `top` can rise by the generated bound, returns without a trap an owned array that holds `countArray` of the input, leaves a ready store, and raises `top` by at most the bound |
| `Demos.Rcv.Program.count_bound` | [`VerifiedCall.lean`](VerifiedCall.lean) | `compiled.count.bound ws ≤ 481128` for every array `ws` of fewer than `2^64` words |
| `Demos.Rcv.Program.count_export` | [`VerifiedCall.lean`](VerifiedCall.lean) | The export `count` is function 22 |

### Testing the count over words

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
tmp/rcv-edges: 301 arrays, 285 valid contests with 658 rounds
tmp/rcv-data/canonical: 19 arrays, 19 valid contests with 33 rounds
0 arrays with a disagreement
```

The edge cases cover every case of the requirements' list, 220 random contests of up to 12 candidates and 2,000 ballots, and the invalid arrays of the word forms.  The corpus holds the 19 contests whose cast vote records it pins, among them the 2022 District 4 contest, whose result words hold the two rounds of the requirements' report.  `rcv-spec program` runs the program natively, so a disagreement between it and the module points to the compilation, and one between it and `rcv-spec array` to the program.

In the verified compiler's tests the module is `rcvCount`: [the module registry](../../tests/verified/modules.txt) lists its compilation, and [the case generator](../../tests/TestSupport/Rcv/Cases.lean) gives its cases, which the executable `verified-cases-rcv` prints alone and `verified-cases` prints with those of every other module.  `tests/verified/run.sh --cases rcvCount` writes `build/verified/rcvCount.wasm`, validates it with `wasm-tools`, which it looks for on the search path, and compares 54 cases between the Wasmtime host and `Demos.Rcv.Spec.countArray` in native Lean.  The cases hold the contest words of the 18 contests of `Cases.lean`, its 18 other arrays, 16 of them invalid, and 18 random contests that SplitMix64 draws from fixed seeds, with up to 63 candidates, 63 positions, and 20,000 ballots.  In 8 of the random contests three candidates share most of the votes and the others form a tail that qualifies for a batch.  The 38 valid contests have 138 rounds, among them 14 batches, 48 lowest eliminations, and 38 eliminations by order, and 4 of the counts end without a winner.  Each case writes its array to a file under `build/verified/rcvCount/` and requires two retained blocks, the host's array and the result.  [`File.lean`](File.lean) states that the written file holds `encode compiled.module` and decodes to `compiled.module`, and each of its two theorems depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  `tests/verified/run.sh` without `--cases` checks it with the other file modules of [its list](../../tests/verified/numerics.txt), and the second command below checks it after `--cases rcvCount`.  `tests/native/verified.sh --module rcvCount` translates the module's 23 functions to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same 54 cases.

```sh
tests/verified/run.sh --cases rcvCount
tools/leanrun --timeout 10m lake env lean Demos/Rcv/File.lean
tests/native/verified.sh --module rcvCount
```

```
verified: passed 54 failed 0
'Demos.Rcv.File.rcvCount_file' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demos.Rcv.File.rcvCount_file_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
rcvCount: 23 of 23 functions, 23 of 23 exports
rcvCount: the clightgen program matches the translation
native verified: passed 54 failed 0
```

## The tabulator over bytes

### The reader

[`Read.lean`](Read.lean) states the reader of the canonical file beside `write`.  `read` splits the file at LF with `List.splitOn`, so that line `j` is piece `j - 1` and ends with LF exactly when another piece follows it.  It takes the lines in order, each with the role that the header gives it: the format line, the contest identifier, `k`, `n`, the `n` candidate lines, the order, `N`, and the `N` ballot lines.  A parser for each role states the form of the grammar and the constraints of the requirements' tables, and the first line that is absent, lacks its LF, or fails its role ends the reading with its number and role.  After the last ballot line the rest of the file must be the empty piece after the final LF, so a further line or a final run of bytes without LF gives the error of role `end`.  `reportFile` gives the report of a file, which the requirements' T1 calls `report b`: the error report `errorReport` of a malformed file and `report` of the structure of a well-formed one.  `lineOf`, `roleAt`, `meets`, and `faulty` state the requirements' error rule by line number, independently of the order in which `read` takes the lines.

Two fresh agents reviewed `Read.lean` against the requirements, each with models of its own, and [the review](review.md#review-of-the-reader) records their findings and the responses.

[`TabulateNative.lean`](TabulateNative.lean) is the executable `rcv-tabulate`, which runs the reader, the programs, and the statements of T2 natively.  Its mode `report` writes `reportFile` of a file, `compare` compares it with the reference's report beside each file, `summary` prints the reader's result for each file, and `programs` compares the reader program's words with `readResult` and the report that the reader program, the count over words, and the printer program give with the reference's.  The modes `t2` and `t2-random` tested the statements of T2 before their proofs: a file that `read` accepts must print as itself through `write` and its structure must meet the constraints and read back as itself, and for a file that `read` rejects the reported line must be the first faulty line with the role that `roleAt` gives it.  [`tests/rcv/reader_edges.py`](../../tests/rcv/reader_edges.py) adds to the edge cases an absent line and a final run without LF in each role from `contest` to `ballot`, numbers of up to 21 digits next to `2 ^ 32` and `2 ^ 64` in each place that holds a number, and names of spaces alone.  On the 633 files of `edges.py`, the 93 of `reader_edges.py`, and the 19 of the corpus, the reports of `reportFile` and of the programs equal the reference's byte for byte, and the statements of T2 hold, as they do for 20,000 random structures and 200,000 files mutated from their files, of which `read` accepts 19,980.

```sh
uv run tests/rcv/edges.py
uv run tests/rcv/reader_edges.py
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build rcv-tabulate
.lake/build/bin/rcv-tabulate compare tmp/rcv-edges/*.rcv
.lake/build/bin/rcv-tabulate compare tmp/rcv-reader/*.rcv
.lake/build/bin/rcv-tabulate compare tmp/rcv-data/canonical/*.rcv
.lake/build/bin/rcv-tabulate t2 tmp/rcv-edges/*.rcv
.lake/build/bin/rcv-tabulate t2-random 1 20000
```

```
633 files, 284 well formed, 349 malformed, 0 differ
93 files, 2 well formed, 91 malformed, 0 differ
19 files, 19 well formed, 0 malformed, 0 differ
633 files, 284 accepted, 349 rejected, 0 failed
20000 structures read back, 200000 mutated files, 19980 accepted, 180020 rejected, 0 failed
```

### Theorems of the reader

The theorems of T2 hold for every byte string and every structure, and each depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.

| Theorem | File | Statement |
|---|---|---|
| T2(a) `Demos.Rcv.Spec.read_write` | [`ReadProof.lean`](ReadProof.lean) | `read (write c) = .ok c` for every structure `c` that meets `Contest.WellFormed` |
| T2(b) `Demos.Rcv.Spec.write_of_read` | [`ReadProof.lean`](ReadProof.lean) | `read b = .ok c` implies `write c = b` and `c.WellFormed`, so a file that reads is the canonical file of its structure |
| T2(c) `Demos.Rcv.Spec.read_error_first` | [`ReadError.lean`](ReadError.lean) | If `b` is the file of no structure that meets the constraints, `read b` returns the error of a line `j ≥ 1` with the role `roleAt b j`, line `j` is faulty, and no line from 1 to `j - 1` is.  `reportFile_error_first` adds that `reportFile b` is the error report of line `j` |
| T2(d) `Demos.Rcv.ReadProgram.readNumber_whole` | [`ReadProgramProof.lean`](ReadProgramProof.lean) | The program's number reader over a whole buffer of fewer than `2 ^ 64` bytes returns `(true, v)` exactly when the buffer holds `decimal v.toNat`, the digits that the printer's `pushNumber` appends for `v` (`pushNumber_toList`) |

`read_write` splits the written file into its lines and the empty piece after the last LF (`write_splitOn`), and each line reads back as the field that `write` printed in it: the decimal forms through `number_decimal`, the position fields through `parsePosition_field`, and the lines of several parts through the spaces and commas that `write` places between parts that hold none.  `write_of_read` runs the other way: each parser that succeeds gives the field whose printing is its line (`eq_of_parseCandidate`, `eq_of_parseBallot`, and the others), and `List.intercalate_splitOn` joins the pieces back into the file.  `read_error_first` reads the pieces that `read` passes to line `j` as the pieces of the file from piece `j - 1` on (`readLine_drop`), so every line before the reported one meets its role.  T2(b) excludes the other result, since a file that reads is the file of a structure that meets the constraints.

### The reader and the printer as programs

[`ReadProgram.lean`](ReadProgram.lean) states the reader in the verified compiler's dialect.  `readContest` takes a buffer of bytes and returns the contest's words of the requirements' section "Word forms of the count" for a well-formed file, and `[0, j, code]` for a malformed file whose first faulty line is `j`, with the code of its role from 0 for `format` to 8 for `end`.  `findByte` finds the next LF, space, comma, or `|`, and the texts of the format are words of eight bytes that `matchWord` compares with the buffer.  `readNumber` reads at most 20 digits and tests before each digit that ten times the value read plus the digit stays below `2 ^ 64`.  The loops over the numbers of an order line, the indices of a field, and the fields of a ballot line recurse on a count of the parts left, and those over the candidate lines and the ballot lines on the number of lines left.

[`PrintProgram.lean`](PrintProgram.lean) states the printers.  `printReport b n res` collects the report's bytes in an array of words: the first two lines, lines 2 to `6 + n` of the file copied from `b`, the lines of each round from the count's result words, and the winner line.  `toBytes` then copies the array into a buffer.  `pushNumber` appends the decimal digits of a word with `digitCount` and `digitByte` of [the decimal text of `Int64`](../../Library/Numerics/Decimal/Int64Text/README.md), and the members of a mask print in increasing index.  `printError j code` prints the error report.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.ReadProgram.readContest_eq` | [`ReadProgramMain.lean`](ReadProgramMain.lean) | `(readContest b).toList = readResult (bytesOf b)` for every buffer of fewer than `2 ^ 64` bytes, where `readResult` of [`ReadWords.lean`](ReadWords.lean) gives the contest's words of a well-formed file and `[0, j, code]` of a malformed one |
| `Demos.Rcv.PrintProgram.printReport_eq` | [`PrintProof.lean`](PrintProof.lean) | For a structure `c` that meets the constraints and a buffer that holds `write c`, `printReport` on the buffer, `n`, and the result words of the count of `c` prints `report c`, when the report has fewer than `2 ^ 64` bytes |
| `Demos.Rcv.TabulateProgram.printError_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `printError` on a line `j < 2 ^ 64` and the code of a role `r` prints `errorReport j r` |

[`ReadProgramProof.lean`](ReadProgramProof.lean) reads the bytes from position `s` to position `e` as `slice b s e` and ties each loop of the program to the specification's split at the same separator through `findByte_split`: the position that `findByte` finds splits the slice as `List.splitOn` does.  [`ReadProgramMain.lean`](ReadProgramMain.lean) follows `readLines` line by line, through `readLines_split`, which separates the header lines from the rest.  [`PrintProof.lean`](PrintProof.lean) uses the theorems of [`Rounds.lean`](Rounds.lean): each round's continuing set is an increasing list of candidates from 1 to `n`, and each elimination names members of it, so the masks of the result words print the round's lines.

### The module's export returns the report of a file

`tabulate` of [`TabulateProgram.lean`](TabulateProgram.lean) composes the reader program, the count program `Demos.Rcv.Program.count`, and the printers: it prints the error report when the reader's first word is 0, and otherwise the report from the file, `n`, and the count of the reader's words.  [`Tabulate.lean`](Tabulate.lean) compiles the functions of the count, of the reader, and of the printers into one module, and [`TabulateCall.lean`](TabulateCall.lean) states the call theorems.  Each theorem depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone, as `#print axioms` at the end of `TabulateCall.lean` reports.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.TabulateProgram.tabulate_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `bytesOf (tabulate b) = reportFile (bytesOf b)` for every buffer of fewer than `2 ^ 32` bytes |
| T1 `Demos.Rcv.TabulateProgram.tabulate_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | `Verified.CallSpec compiled.module compiled.tables 63 tabulateSpec compiled.tabulate.bound`, where `tabulateSpec b` is the buffer of `reportFile (bytesOf b)`: function 63, called with a borrowed buffer from a ready store in which `top` can rise by the generated bound, returns without a trap an owned buffer of the report, leaves a ready store, and raises `top` by at most the bound |
| `readContest_callSpec`, `printReport_callSpec`, `printError_callSpec` | [`TabulateCall.lean`](TabulateCall.lean) | Functions 47, 60, and 62 compute `readResult` of the buffer's bytes, `printReport`, and `printError` |
| `Demos.Rcv.TabulateProgram.exports` | [`Tabulate.lean`](Tabulate.lean) | The exports `count`, `readContest`, `printReport`, `printError`, and `tabulate` are functions 22, 47, 60, 62, and 63 |

`tabulate_eq` follows the two results of the reader.  For a malformed file `read_error_lt` bounds the line number below `2 ^ 64`, and `printError_eq` gives the error report.  For a well-formed file, T2(b) gives the structure `c` whose writing is the file, `countWords_contestWords` equates the count of the reader's words with the result words of `countContest c`, `Demos.Rcv.Refine.count_eq` equates the program's count with the specification's, and `printReport_eq` prints `report c`, whose length `report_length_lt` bounds below `2 ^ 64` for a file of fewer than `2 ^ 32` bytes.  A buffer that a store holds has fewer than `2 ^ 32` bytes (`size_lt_of_borrowed`), so the call theorem covers every buffer.  The bound `compiled.tabulate.bound` is the generated one, and `tabulate_bound` of [`TabulateBound.lean`](TabulateBound.lean) closes it at `80 L + 33,702,909` bytes for a file of `L < 2 ^ 32` bytes.

### The closed form of the bound

[`TabulateBound.lean`](TabulateBound.lean) closes the generated bound of `tabulate` in the size of the file, and each of its theorems depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  A push onto a paid array costs 80 bytes.  The reader pushes one word for each candidate line, each index of the order line, and each position field of a ballot line, whose fields end at distinct commas and LFs, so its bound grows by 80 bytes for each byte of the file.  The printers push the report's bytes, of which the header lines are at most 20,777 and the rounds at most 64 of at most 63 candidates each, and copy the report into the buffer that they return.

| Theorem | Statement |
|---|---|
| `tabulate_bound` | `compiled.tabulate.bound b ≤ 80 * b.data.size + 33702909` for every buffer of fewer than `2 ^ 32` bytes |
| `readContest_bound` | `compiled.readContest.bound b ≤ 80 * b.data.size + 10704`: the two array literals of 312 bytes, at most 63 candidate lines and 63 indices of the order, and the fields of the ballot lines |
| `printReport_bound` | For `n` of at most 63 candidates and at most 64 rounds in `res`, `compiled.printReport.bound (b, n, res)` is at most 80 bytes for each byte of the header lines, the block of the report, and 30,247,832 bytes |
| `printError_bound` | `compiled.printError.bound (j, code)` is at most the block of the error report and 20,152 bytes |
| `count_bound_eq` | The tabulator's compilation and `Demos/Rcv/Compiled.lean` generate the same bound for `count`, which `Demos.Rcv.Program.count_bound` closes at 481,128 bytes |
| `headerText_le`, `reportFile_length_le` | The header lines of a structure that meets the constraints hold at most 20,777 bytes, and every report at most 1,301,030 |

The proofs bound each tail loop of the reader by induction on its count, with `Verified.Tail.costAt_rank_eq` and the generated step's value at each branch, and the printers' costs by `grw` with the bounds of their callees.  `report_length_le` of [`TabulateProof.lean`](TabulateProof.lean) bounds a report by its header lines and 1,280,253 bytes, and `report_length_lt` follows from it.  The page's executable `rcv-bound`, which [the browser page](#the-browser-page) describes, evaluates the generated bound in native Lean, and on the 725 edge files the bound of `tabulate_bound` is at least the generated one.

### Testing the tabulator

[`tests/rcv/tabulate.py`](../../tests/rcv/tabulate.py) compares the module, the WASI process, C, native Lean, and the reference on canonical files.  For each file it computes the reference's report and requires the module's export `tabulate` in the Wasmtime host, `rcv-tabulate report`, and the report that `edges.py`, `reader_edges.py`, or `check.py` wrote to give the same bytes.  Its options add to these outputs the standard output of [the WASI process](#the-wasi-process) in the Wasmtime host, whose control record must be `wasi-exit 0`, that of the native process `rcv-process`, and that of [the C executable](#the-c-translation) `rcv-tabulate-c`.  On the 633 edge files, the 93 files of the reader's edge cases, and the 19 contests of the corpus, all of them equal the reference's report.  The run with `/bin/cat` in place of the C executable reports all 93 of the reader's edge files as disagreements, so the comparison detects an executable that prints something else.  The verified compiler compiles `Tabulate.lean` in 841 s with a peak of 5.9 GB on edgexpert-18ff under `tools/leanrun --cpus 18 --threads 18 --memory-high 24G`, and in 862 s with a peak of 6.4 GB under `--cpus 8 --threads 8`, and the module has 32,293 bytes.

```sh
tools/leanrun --timeout 60m lake build Demos.Rcv.ProcessAxioms rcv-tabulate rcv-process
mkdir -p build/verified build/rcv
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Tabulate Demos.Rcv.TabulateProgram.compiled.module build/verified/rcvTabulate.wasm
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.ProcessModule Demos.Rcv.Process.module build/rcv/process.wasm
wasm-tools validate build/rcv/process.wasm
tests/rcv/native.sh
uv run tests/rcv/edges.py
uv run tests/rcv/reader_edges.py
uv run tests/rcv/check.py
uv run tests/rcv/tabulate.py --process build/rcv/process.wasm \
  --lean-process .lake/build/bin/rcv-process --native build/rcv/native/rcv-tabulate-c \
  tmp/rcv-edges tmp/rcv-reader tmp/rcv-data/canonical
```

```
tmp/rcv-edges: 633 files, 284 well-formed, 349 malformed
tmp/rcv-reader: 93 files, 2 well-formed, 91 malformed
tmp/rcv-data/canonical: 19 files, 19 well-formed, 0 malformed
0 files with a disagreement
```

In the verified compiler's tests the module is `rcvTabulate`: [the module registry](../../tests/verified/modules.txt) lists its compilation, and [the case generator](../../tests/TestSupport/Rcv/Cases.lean) gives its cases beside those of `rcvCount`, which the executable `verified-cases-rcv` prints for either name.  `tests/verified/run.sh --cases rcvTabulate` writes `build/verified/rcvTabulate.wasm`, validates it with `wasm-tools`, and compares 86 cases between the Wasmtime host and `Demos.Rcv.Spec.reportFile` in native Lean.  The cases are the canonical files of the contests of `Cases.lean`, of contests with ballot identifiers, contest identifiers of 1 and 64 bytes, and names of bytes outside ASCII, and of the 18 random contests of the count's cases, the worked example's file cut after each of its lines, that file without its final LF and with a further line or further bytes, and 16 edits of it that each break one line.  Each case writes its file under `build/verified/rcvTabulate/` and requires two retained blocks, the host's buffer, which the host allocates for an empty file as well, and the report.  [`TabulateFile.lean`](TabulateFile.lean) states that the written file holds `encode compiled.module` and decodes to `compiled.module`, and each of its two theorems depends on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.  `tests/native/verified.sh --module rcvTabulate` translates the module's 64 functions to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same 86 cases.

```sh
tests/verified/run.sh --cases rcvTabulate
tools/leanrun --timeout 10m lake env lean Demos/Rcv/TabulateFile.lean
tests/native/verified.sh --module rcvTabulate
```

```
verified: passed 86 failed 0
'Demos.Rcv.TabulateFile.rcvTabulate_file' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demos.Rcv.TabulateFile.rcvTabulate_file_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
rcvTabulate: 64 of 64 functions, 64 of 64 exports
rcvTabulate: the clightgen program matches the translation
native verified: passed 86 failed 0
```

## The process, C, and the page

### The WASI process

[`Process.lean`](Process.lean) runs the tabulator over stdin and stdout.  Its `begin` reads the whole standard input with `readAll 50000000`, which [the WASI guide](../../docs/wasi.md#operations-and-results) describes, into one buffer of 50,004,096 bytes whose unused tail receives each read of at most 4,096 bytes, and returns a state that holds `tabulate` of the input.  Each step writes the rest of the report, continuing after short writes, and the process stops with status 0 when the report is written.  A read or a write that returns an errno stops it with that errno, and an input of more than 50,000,000 bytes stops it with status 22, WASI's `fbig`, before `tabulate` and with nothing written.  [`ProcessWasi.lean`](ProcessWasi.lean) compiles the functions of `Tabulate.lean` and the process's own with `verified_compile_wasi`, which [the WASI guide](../../docs/wasi.md) describes, and [`ProcessModule.lean`](ProcessModule.lean) composes the command module, of 34,253 bytes.  Under `tools/leanrun --cpus 10 --threads 10 --memory-high 24G` on edgexpert-18ff, `lake env lean` takes 569 s on `ProcessWasi.lean`, with a peak of 6.3 GB, and 283 s on `ProcessModule.lean`, with a peak of 3.9 GB.  [The native executable](ProcessNative.lean) `rcv-process` runs the process on the operating system's stdin and stdout.

The theorems follow [the order book's process](../OrderBook/README.md#the-wasi-process) under [StreamFold's host assumptions](../StreamFold/StreamHost.lean).  [`ProcessAxioms.lean`](ProcessAxioms.lean) checks that every theorem of the namespace `Demos.Rcv.Process`, those that `verified_compile_wasi` generates among them, and the theorems of the closed form and of the C call depend on the axioms `propext`, `Classical.choice`, and `Quot.sound` alone.

| Theorem | File | Statement |
|---|---|---|
| `process_output` | [`ProcessCorrect.lean`](ProcessCorrect.lean) | From an empty output history, for an input of at most 50,000,000 bytes, every run of the native `begin` returns a running state with status 0, from which some execution of the native process writes exactly `expectedOutput` of the input, the bytes of `reportFile` of the input, and returns status 0 |
| `implements`, `run_initial` | [`ProcessProof.lean`](ProcessProof.lean) | Every modeled run of the module's `_start` that completes without exhausting Talos fuel matches a run of the native process, including runs that stop at an I/O error, a host trap, or a rejected exit |
| T1 `initial_terminates` | [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | For every input of at most 50,000,000 bytes, under StreamFold's host assumptions, a Talos host that satisfies `hostSpec`, and a host that accepts the exit status 0, `_start` from the module's initial store exits with status 0 after writing exactly `expectedOutput` of the input |
| `initial_exits_long` | [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | For every input of more than 50,000,000 bytes, under the same assumptions with a host that accepts the exit status 22, `_start` from the module's initial store exits with status 22 after writing nothing |
| `bytes`, `terminates_bytes` | [`ProcessProof.lean`](ProcessProof.lean), [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | One byte sequence encodes the module, decodes to it, is a valid binary, and carries `implements`, or `initial_terminates` and `initial_exits_long` |

[StreamFold's theorems on `readAll`](../StreamFold/ReadAll.lean) give, under the host assumptions, the whole input at EOF for an input of at most the limit and more than the limit's bytes for a longer one, and [`ProcessFuture.lean`](ProcessFuture.lean) states with them what `begin` returns: the running state of the report with nothing written (`begin_report`), or the stopped state with status 22 (`begin_long`).  The invariant `Future` relates a state after `begin` to the whole input: the input is read, and the output written so far followed by the output that remains is the report, which `reportFile_length_le` bounds at 1,301,030 bytes.  [`ProcessControl.lean`](ProcessControl.lean) proves the termination of the steps with a rank of the unwritten output and the host's credit for zero-byte writes.  [`ProcessCharges.lean`](ProcessCharges.lean) bounds `begin` by 4,083,707,053 bytes (`beginCharge_eq`): the buffer of `readAll`, 50,004,144 bytes, and the bound of `tabulate` on 50,000,000 bytes, `80 · 50,000,000 + 33,702,909`, which `tabulate_bound` gives since the WASI compilation's bound of `tabulate` is `compiled.tabulate.bound` by definition (`tabulate_bound_eq`).  A copy of a state costs at most 1,301,085 bytes (`copyLimit`) and a write step at most two copies (`stepCharge`), so the memory of a run, `processMemory`, is `beginCharge` and one copy, 4,085,008,138 bytes, which also covers a step with the copies of the states before and after it, and `processMemory_le` states that it fits above the literal pool, which ends at 4,096 bytes, in the 65,535 pages of the module's memory.  Neither theorem therefore has a memory premise, and `target_terminates` of [`ProcessTermination.lean`](ProcessTermination.lean) takes the status at which `begin` stops, so that the run above the limit, which stops in `begin`, has its own theorem.

`readAll` writes each read into the buffer in place, and the state that the process loop copies after each write step holds only the report, so no read and no step does work that grows with the input already read.  The table gives the times of the process's module in the Wasmtime 44 host on edgexpert-18ff, one process at a time, with the input from a file (`--stdin-file`) and from a pipe.  The last three rows come from the at-large file: the file twice and four times over, which are malformed and give short error reports, and one well-formed contest that holds ten copies of its ballots.  `tests/rcv/tabulate.py` finds each report equal to the reference's, and the process's peak resident memory is 19 MB on the first file and 205 MB on the last.  An input of 50,000,000 zero bytes takes 0.14 s from a file and 0.49 s from a pipe and gives the error report with status 0, and one more byte gives status 22 with nothing written.  The native process `rcv-process` takes 0.06 s on the first file, 0.21 s on the at-large file, and 1.84 s on the ten copies.  StreamFold's host assumptions fix the read capacity at 4,096 bytes, so a process with larger reads needs host assumptions of its own.

| Input | Bytes | File (s) | Pipe (s) |
|---|---|---|---|
| Oakland 2025 City Council D2 | 348,918 | 0.02 | 0.03 |
| Oakland 2024 City Council D1 | 906,118 | 0.04 | 0.04 |
| Oakland 2025 Mayor | 2,534,293 | 0.04 | 0.09 |
| Oakland 2022 City Auditor | 3,312,770 | 0.07 | 0.09 |
| Oakland 2024 City Council at large | 4,696,262 | 0.07 | 0.14 |
| The at-large file twice | 9,392,524 | 0.06 | 0.19 |
| The at-large file four times | 18,785,048 | 0.12 | 0.23 |
| Ten copies of the at-large ballots, one contest | 46,957,860 | 0.69 | 1.13 |

### The C translation

[`tests/rcv/native.sh`](../../tests/rcv/native.sh) builds `build/rcv/native/rcv-tabulate-c`, the module translated to C and compiled with CompCert, which reads a canonical file and writes its report.  `native-verified build` writes the C text of the translation of `compiled.module` with the 16,384 pages of `lx_mem` that `compiled.translation_eq` states, has `clightgen` read it back, compares that Clight with the translation, and compiles the text with `ccomp` only when they match.  `ccomp` links the object with the export tables, [`tabulate.c`](tabulate.c), and `tools/native-host.c`.  `tabulate.c` places the file's bytes in a block that the module's `alloc` returns, calls the export `tabulate`, tests `lx_status`, and writes the bytes of the returned buffer.  `tests/native/verified.sh --module rcvTabulate` runs the 86 cases of the verified compiler's tests on the same translation.

| Theorem | File | Statement |
|---|---|---|
| `tabulate_trapFree` | [`TabulateCall.lean`](TabulateCall.lean) | Function 63, from a store with room for `compiled.tabulate.bound b` bytes, returns without a trap the buffer of `reportFile` of the bytes of `b` |
| T1 `tabulate_native` | [`TabulateCall.lean`](TabulateCall.lean) | `NativeImpl tabulate_trapFree A X 16384 compiled.translation` for every `Archi` and every semantics of external functions: the C function of function 63 computes `tabulateSpec` as `tabulate_trapFree` states |
| `tabulate_native_size` | [`TabulateBound.lean`](TabulateBound.lean) | The C function returns without a trap the buffer of `reportFile` of a file of at most `L` bytes when `top + 80 L + 33,702,909` is at most the 1 GiB of `lx_mem` |
| `tabulate_native_12000000` | [`TabulateBound.lean`](TabulateBound.lean) | The same for every file of at most 12,000,000 bytes, from a heap whose `top` is at most 16,777,216 bytes |

`tabulate_native` rests on the items that [the trusted base](../../docs/trusted-base.md#c-c-files-and-native-executables) lists for C files, among them the Lean copy of Clight, CompCert's proofs and its unverified parts, and the host calling code, which for this executable is `tabulate.c` with `tools/native-host.c`.  The option `(cap := 16384)` of `Tabulate.lean` gives the translation 16,384 pages of `lx_mem`, 1,073,741,824 bytes, and leaves the module's bytes as they were.  With `tabulate_bound` the theorem's premise holds for files of up to about 12.8 MB, after the host's block for the file, which covers the corpus's largest file, of 4,696,262 bytes.  `tabulate_native_size` takes the relation of the C memory to the store, whose cap is then 16,384 pages, in place of the cap in the premise.  On the largest file of the corpus, the executable takes 0.07 s.

### The browser page

[The recount page](../../tests/web/rcv/index.html), which `uv run tests/web/serve.py` serves at http://127.0.0.1:8000/rcv/, recounts a canonical file that the reader chooses on their computer, with this module or with [the Maine module](Maine/README.md#the-browser-page).  The browser reads the file with the File API and sends nothing to the server, and the page shows the report's bytes as text, with a link that saves them, beside the SHA-256 of the module that it loaded.  [`tabulate.js`](../../tests/web/rcv/tabulate.js) calls the export `tabulate` as `tabulate_callSpec` requires.  For each file it creates a fresh instance of the module, whose store the generated `compiled.initial` and `Verified.Ready.initial` prove ready.  It calls `alloc` with the file's length, writes the file's bytes into the block, passes the block's root and the length to `tabulate`, and copies the bytes at the root and the length that the call returns.

The premise of the call theorem bounds the allocator's `top`, which the module does not export.  `top` lies inside the memory (`Heap.At`), and `alloc` raises it by at most 48 bytes and a block of `allocSize len` bytes (`Heap.allocate_top`), so the premise holds when the sum of the memory's size, `48 + allocSize len`, and the bound is at most 65,535 pages.  The page takes the bound `80 L + 33,702,909` of `tabulate_bound` for a file of `L` bytes, checks the sum before `alloc`, and grows the memory by the room it needs, so that neither `alloc` nor `tabulate` grows the memory.  Talos grows memory whenever the cap allows, while a browser may refuse, and the growth before the call turns such a refusal into a refusal of the file.  From the fresh instance's 16 pages, the cap admits files of up to 52,594,447 bytes, and the largest file of the corpus, 4,696,262 bytes, needs 414,100,181 bytes of room.

The page's JavaScript lies outside the theorems, as the requirements' list of what lies outside them states.  It is trusted to create the instance, to check the room, to place the file's bytes, and to copy the report, and the browser's engine is trusted to agree with Talos's semantics, as [the trusted base](../../docs/trusted-base.md#wasm-webassembly-modules-of-the-verified-compiler) states for every host.  The page decodes the report as UTF-8 for display, and the saved file holds the report's bytes.

[`tests/rcv/page.mjs`](../../tests/rcv/page.mjs) runs `tabulate.js` under Node on canonical files, with the page's bound, and requires each report to equal the reference's, with this module unless `--count maine` chooses the Maine module.  The executable `rcv-bound` of [`BoundMain.lean`](../../tests/TestSupport/Rcv/BoundMain.lean) prints each file's `compiled.tabulate.bound` in native Lean, and with `--bounds` the script requires the page's bound to be at least that value.  On the 633 edge files, the 93 files of the reader's edge cases, and the 19 contests of the corpus, the reports equal the reference's.  The page's bound is at least the generated bound on the 726 edge files, and the largest generated bound is 2,178,064 bytes, for a file of 61,449 bytes whose bound on the page is 38,618,829 bytes.  Native Lean's evaluation of the generated bound grows faster than the file: it takes a few seconds for a file of 61,449 bytes, and it had not finished the corpus's 3,312,770-byte file after 15 minutes, so the comparison leaves out the corpus.  [The recount page's description](../../tests/web/README.md#rcv-recount-rcv) gives the results of the page in headless Chromium.

```sh
uv run tests/rcv/edges.py
uv run tests/rcv/reader_edges.py
uv run tests/rcv/check.py
tools/leanrun --timeout 60m lake build rcv-bound
tools/leanrun --timeout 60m sh -c \
  '.lake/build/bin/rcv-bound tmp/rcv-edges/*.rcv tmp/rcv-reader/*.rcv > tmp/rcv-bounds.txt'
node tests/rcv/page.mjs --bounds tmp/rcv-bounds.txt tmp/rcv-edges tmp/rcv-reader \
  tmp/rcv-data/canonical
```

```
build/verified/rcvTabulate.wasm: SHA-256 769a3ba4114421d701f57d3fa31ffe9d8661d7fcf6c159e0fb206063e7c90dbc
tmp/rcv-edges: 633 files, 284 well-formed, 349 malformed, largest bound 38618829 bytes
tmp/rcv-reader: 93 files, 2 well-formed, 91 malformed, largest bound 33734909 bytes
tmp/rcv-data/canonical: 19 files, 19 well-formed, 0 malformed, largest bound 409403869 bytes
0 files refused or with a disagreement
```

## The Maine count

[The Maine count](Maine/README.md), increment 4 of the requirements' plan, counts single-winner contests under 21-A M.R.S. §723-A and the rules of 29-250 C.M.R. ch. 535, with the Oakland module's file format, reader, tally of a round, and report.  Its specification agrees byte for byte with the reference's Maine mode on its edge cases and on the Secretary of State's records.  Its theorems T1, T3 to T9, and T11 to T15 hold, with Oakland's T10 applied to its interpretation, and its module `build/verified/rcvMaine.wasm` runs on the recount page.  RCTab's rounds under configurations of the Maine count agree with the module's on its edge cases and corpus, apart from the behaviors of RCTab that [the Maine corpus's RCTab section](../../tests/rcv/maine/README.md#rctab) states.  Increment M3 of [its requirements' plan](Maine/requirements.md#plan) also calls for a WASI process and its C translation, which the module does not have yet.
