# Ranked-choice tabulation

This demo is a tabulator for single-winner ranked-choice contests, also called instant-runoff contests, under Section 1105 of the Oakland City Charter.  Its module reads a canonical ballot file, counts the contest in rounds under the charter's rules, and writes a report of every round, and its theorems state that the module returns, for every file, the report that a Lean specification of [the requirements](requirements.md) gives.  The module fixes the charter's rule at compile time, so no setting chosen at run time can change the count, and the second line of every report names the governing texts and the date on which they were read.

Anyone who holds a published contest's cast vote records can audit the contest with the tabulator: convert the records to the canonical file, recount the contest in a browser, at a command line, or with a C executable, and compare the report with the official one.  The motivating case is the 2022 contest for School Director, District 4, of the Oakland Unified School District, which Alameda County first certified under a setting of its tabulator that withheld 235 ballots from round 1 and elected a candidate whom the charter's count does not elect.  [The case study](#case-study-school-director-district-4-2022) recounts that contest from its published records with the module and reproduces both of the County's counts.

The module runs as an export in a WebAssembly host and on a browser page.  A WASI process compiled from the same functions reads a file on standard input and writes its report on standard output, the module's translation to C compiles with CompCert, an AArch64 image of the module runs without an operating system on QEMU's `virt` machine and reads the file over its UART, and native Lean runs the specification.  [The requirements](requirements.md) state the file, the interpretation of a ballot, the rounds, the report, and the theorems, [the review](review.md) records each reading of the governing texts and each departure of the County's practice from them, and [the test corpus](../../tests/rcv/README.md) pins the County's reports of Oakland's contests from 2022 to 2026 and D. Otis's cast vote records of 19 of them, a standardized form of the County's records on Harvard Dataverse.  [A second module](#the-maine-module) counts contests under Maine's statute with the same file format and a report that adds the lines of its initial test.

## Guarantees

`tabulate_callSpec` states the requirements' T1 for the module's export, and the theorems of the WASI process and of the C translation state it for those forms.  The bound in the call theorem is the one that the verified compiler generates, which `tabulate_bound` closes in the size of the file, and `reportFile b` is the specification's report of the bytes `b`: the error report of the first faulty line of a malformed file, and the report of the count of a well-formed one.  A name without a namespace is in `Demos.Rcv.TabulateProgram`.

| Form | Theorem | Conclusion | Premises |
|---|---|---|---|
| The module's export `tabulate` | `tabulate_callSpec`, [`TabulateCall.lean`](TabulateCall.lean) | Function 63 returns without a trap an owned buffer that holds `reportFile` of its argument's bytes, leaves a ready store, and raises the allocator's `top` by at most `compiled.tabulate.bound b` | A ready store, a borrowed buffer `b`, and room in the memory cap for `top` to rise by `compiled.tabulate.bound b` |
| The bound | `tabulate_bound`, [`TabulateBound.lean`](TabulateBound.lean) | `compiled.tabulate.bound b ≤ 80 L + 33,702,909` for a file of `L` bytes | `L < 2^32`, which every buffer in a store meets |
| The emitted file | `Demos.Rcv.TabulateFile.rcvTabulate_file` and `rcvTabulate_file_decode`, [`TabulateFile.lean`](TabulateFile.lean) | `build/verified/rcvTabulate.wasm` holds `encode compiled.module` and decodes to `compiled.module` | The file as it was when `tests/verified/run.sh` checked the theorem |
| The WASI process | `Demos.Rcv.Process.initial_terminates`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | `_start`, from the module's initial store, exits with status 0 after writing exactly the bytes of `reportFile` of the input | An input of at most 50,000,000 bytes, StreamFold's host assumptions, a Talos host that satisfies `hostSpec`, and a host that accepts the exit status 0 |
| | `Demos.Rcv.Process.initial_exits_long`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | `_start` exits with status 22 after writing nothing | An input of more than 50,000,000 bytes, the same host assumptions, and a host that accepts the exit status 22 |
| | `Demos.Rcv.Process.terminates_bytes`, [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | One byte sequence encodes the process's module, decodes to it, and is a valid binary, and the module satisfies both theorems above | None |
| The C translation | `tabulate_native`, [`TabulateCall.lean`](TabulateCall.lean) | The C function of function 63 returns without a trap the buffer of `reportFile` of its argument's bytes, as `tabulate_trapFree` states for the module | Every `Archi` and every semantics of external functions, and a C memory `lx_mem`, of the size that [the C translation](#the-c-translation) gives, that corresponds to a store with room for `compiled.tabulate.bound b` |
| | `tabulate_native_size`, [`TabulateBound.lean`](TabulateBound.lean) | The same | A file of at most `L` bytes and a heap whose `top` and `80 L + 33,702,909` bytes fit in `lx_mem`, which [the C translation](#the-c-translation) states for a fixed size of file |
| The AArch64 image | `TestSupport.A64.ImageFilesRcv.rcv_uart_report`, [the image's theorems](../../tests/TestSupport/A64/ImageFilesRcv.lean) | From a boot state whose memory holds the bytes of `rcv.img` at a base `B`, the machine reaches PSCI's `SYSTEM_OFF` with every store to the UART complete, after writing `reportFile msg` and the status byte 0 | `B` a multiple of 4096 with the image's memory in the RAM GiB, the MMU off, and a UART receiver that delivers the eight bytes of the length of `msg`, the lowest first, and then `msg`, a file of at most 8,800,000 bytes, with no byte carrying an error flag |
| | `rcv_uart_over` and `rcv_uart_flag`, [the image's theorems](../../tests/TestSupport/A64/ImageFilesRcv.lean) | The machine reaches `SYSTEM_OFF` after writing the status byte 64 alone, or 65 alone | A length above 8,800,000, or a byte that the program reads carrying an error flag after bytes without one |
| The browser page | `tabulate_callSpec` and `tabulate_bound` | The call that the page makes returns `reportFile` of the file | The page's code establishes the premises of `tabulate_callSpec`, as [the browser page](#the-browser-page) describes, and lies outside the theorems |
| The count over words, module `rcvCount` | `Demos.Rcv.Program.count_callSpec`, [`VerifiedCall.lean`](VerifiedCall.lean) | Function 22, the export `count`, returns without a trap an owned array that holds `Demos.Rcv.Spec.countArray` of its argument, the count's result words, and raises `top` by at most `compiled.count.bound ws`, which `Demos.Rcv.Program.count_bound` closes at 481,128 bytes | A ready store, a borrowed word array `ws`, and room for the bound |

The theorems about the specification's reader and count hold for every byte string, contest structure, or contest that meets the premises in the Statement column, and by `tabulate_callSpec` the properties of the count hold of every report that the module returns.  `countContest` is the count of a contest structure, the single count is the count without rule 3, and the county count is the requirements' statement of Alameda County's practice, which eliminates one candidate per round while three or more continue and ends at the first round with two or fewer.  T2(a) and T4 assume `Contest.WellFormed`, whose tie-break order is a permutation of the candidates, T9 assumes that the new order is such a permutation, and T11(a) assumes continuing sets without repeated candidates.

| Requirement | Lean names | Statement |
|---|---|---|
| T2 Reader | `Demos.Rcv.Spec.read_write`, `write_of_read`, [`ReadProof.lean`](ReadProof.lean), `read_error_first`, `reportFile_error_first`, [`ReadError.lean`](ReadError.lean), `Demos.Rcv.ReadProgram.readNumber_whole`, [`ReadProgramProof.lean`](ReadProgramProof.lean) | (a) `read (write c) = .ok c` for every structure `c` that meets `Contest.WellFormed`.  (b) `read b = .ok c` implies `write c = b` and `c.WellFormed`, so each structure has exactly one canonical file.  (c) If `b` is the file of no structure that meets the constraints, `read b` returns the error of a line `j ≥ 1` with the role `roleAt b j`, line `j` is faulty, no line before it is, and `reportFile b` is the error report of line `j`.  (d) The program's number reader over a whole buffer of fewer than `2^64` bytes returns `(true, v)` exactly when the buffer holds the decimal digits that the printer writes for `v` |
| T3 Winner | `Demos.Rcv.Winner.winner_iff`, `winner_majority`, `tied_final`, `rounds_le`, [`Winner.lean`](Winner.lean) | (a) The count names a winner exactly when round 1 has a continuing ballot.  (b) The winner holds more than half of the last round's continuing ballots.  (c) A last round after round 1 has one continuing candidate exactly when the round before it had two with equal votes, and that round then eliminates by order with the two as the tied set.  (d) The number of rounds is at most the larger of 1 and the number of counted candidates |
| T4 Elimination | `Demos.Rcv.Rounds.elimination`, [`Rounds.lean`](Rounds.lean) | For a structure that meets `Contest.WellFormed`, every round that eliminates has `Tᵣ > 0` and no candidate with a majority, and eliminates a batch of two or more candidates that equals a qualifying `L(X)` and contains every qualifying `L(Y)`, or, when no qualifying set has two or more candidates, the candidate that alone has the fewest votes, or the member latest in the order of the two or more candidates with the fewest votes, which form the tied set.  The last round eliminates no one and ends by rule 1, with the candidate that holds a majority as the winner, or by rule 2, with `Tᵣ = 0` and no winner |
| T5 Conservation | `Demos.Rcv.Rounds.conservation` | In every round the votes and the four inactive counts sum to the number of ballots, and `continuing` is the sum of the votes |
| T6 Locality | `Demos.Rcv.Rounds.locality` | Round 1's continuing set is the counted set `K`.  Each round's votes and inactive counts are the numbers of ballots whose interpretation against that round's continuing set counts for each candidate or has each reason, every round but the last eliminates, and the next round's continuing set is the current one minus the eliminated candidates |
| T7 Invariance | `Demos.Rcv.Rounds.invariance` | Ballots whose position words are a permutation of the contest's give the same count and the same report, which covers a permutation of the ballots and any change of their identifiers.  With T2 the statement holds of files |
| T8 Stability | `Demos.Rcv.Stability.stability_counts`, `stability_inactive`, `stability_rounds`, [`Stability.lean`](Stability.lean) | For continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for `w` against `S'` when `w ∈ S'`, and a ballot inactive against `S` is inactive against `S'` with the same reason.  From each round of the count to the next, no inactive count decreases, the votes of a candidate that continues do not decrease, and `continuing` does not increase |
| T9 Order | `Demos.Rcv.Rounds.order_choice` | If an order `π′`, a permutation of the candidates, places the eliminated candidate of each marked tie after the rest of its tied set, the count under `π′` equals the count under the contest's order, and the report's lines differ only in the order line |
| T10 Batch | `Demos.Rcv.Batch.batch_winner`, `batch_rounds`, `batch_members`, [`Batch.lean`](Batch.lean) | (a) The single count names the count's winner, or both name none.  (b) The counts of the count's rounds form a sublist of the single count's, or all but the last do, the single count names the count's winner, and its last continuing set strictly contains the count's.  (c) From a round of the single count with the continuing set of a round of the count that eliminates the batch `B`, each of the next `B.length` rounds ends the single count or eliminates exactly one member of `B` that continues in it |
| T11 Majority holder | `Demos.Rcv.Holder.holder_subset`, `county_majority`, `county_winner`, `county_tied`, `county_rounds_sublist`, [`Holder.lean`](Holder.lean) | (a) A candidate with a majority against a continuing set has one against every smaller continuing set that holds it, for sets without repeated candidates.  (b) A candidate with a majority in a round of the county count continues in every later round, and the county count names it.  (c) If the count names `w` and its last round is round 1 or has two or more continuing candidates, the county count names `w`, and if the count's last round has one candidate and is not round 1, the county count's last round has the counts of the count's round before it.  (d) The counts of the count's rounds with two or more continuing candidates form a sublist of the county count's |
| T12 Majority criterion | `Demos.Rcv.Properties.majority_criterion`, [`Properties.lean`](Properties.lean) | If more than half of the continuing ballots against `K` count for `w`, the count has one round and names `w`, and the single count and the county count name `w` |
| T13 Condorcet loser | `Demos.Rcv.Properties.condorcet_loser` | If `K` has two or more candidates and every other candidate of `K` beats `ℓ`, the count does not name `ℓ` |
| T14 Later-no-harm | `Demos.Rcv.Properties.later_no_harm` | If position `p` of a ballot marks only `w` and the count names `w`, a ballot whose positions 1 to `p` are the same, with any number of positions after `p`, gives in its place a count with the same rounds that names `w` |
| T15 Monotonicity fails | `Demos.Rcv.Properties.monotonicity_fails` | The two contests of the requirements meet the constraints and differ only in two ballots, on which the second raises `A` from the second position to the first.  The count names `A` for the first and `B` for the second, and round 1 of each eliminates one candidate with the fewest votes alone |

Every theorem of both tables depends on no axiom other than `propext`, `Classical.choice`, and `Quot.sound`.  The `#print axioms` commands at the ends of the theorem files and in [`ProcessAxioms.lean`](ProcessAxioms.lean) report these axioms, and the last covers every theorem of the namespace `Demos.Rcv.Process`, those that `verified_compile_wasi` generates among them.  `Beats` of `Properties.lean` states the requirements' term "beats": one candidate beats another when more ballots count for it than for the other against the continuing set of the two.  `Raises` states "raising": a position that marks only the candidate moves to an earlier position, and the other positions keep their order.

## Trusted base

The theorems about the module depend on the items that [the trusted base](../../docs/trusted-base.md) lists for WebAssembly modules, among them Lean's kernel, Talos's execution semantics and store definitions, the binary decoder, the agreement of Wasmtime or the browser's engine with Talos, and the host's placement of the argument bytes.  The WASI process adds the items for WASI Preview 1 modules, among them the host specification, Wasmtime's Preview 1, and StreamFold's host assumptions.  The C executable depends instead on the items for C files, among them Talos's store and memory definitions, the Lean copy of Clight, CompCert's proofs and its unverified parts, and the calling code of [`tabulate.c`](tabulate.c) and `tools/native-host.c`.  The AArch64 image depends on the items of [the A64 trusted base](../../docs/a64-bare-metal.md#trusted-base) in place of those of a WebAssembly host, among them the model of the processor, QEMU's loader, and QEMU's PL011 receiver and character backend, which give the program the file's bytes in order in a run without a break on the line.  No theorem checks that the specification states the requirements: two fresh agents reviewed the count against them and two more the reader, each with a model of its own, as [the review](review.md#review-of-the-specification) records.

The theorems concern the count of a canonical file, and [the requirements' list](requirements.md#what-lies-outside-the-theorems) gives what lies outside them.  The converters write canonical files from vendor exports without proof, the kinds of the candidates depend on filings outside the records, and the origin of the tie-break order is a fact outside the file.  Whether the records agree with the paper ballots is the question of a risk-limiting audit.  The page's JavaScript, the Python reference, and the scripts that convert the records and compare counts with the County's reports are code without proof, which the tests exercise.

## Running the tabulator

The commands below build the module, the WASI process, the C executable, and native Lean's executables from the repository root.  The Wasmtime host comes from `tools/build-wasmtime-host.sh`, which [the compiler manual](../../docs/verified-manual.md#the-wasmtime-host) describes, `wasm-tools` must be on the search path, and `tests/rcv/native.sh` needs CompCert 3.18's `ccomp` and `clightgen` on the search path or in the variables `CCOMP` and `CLIGHTGEN`.  The compilations of `Tabulate.lean` and `ProcessWasi.lean` reach 5.4 and 8.6 GiB of resident memory, above `tools/leanrun`'s default limit, so the build command raises the limit, and [the build costs](#running-times-and-build-costs) give their times.  `Tabulate.lean` imports the programs alone, so a change of a proof does not compile the module again.

```sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 90m --memory-high 12G lake build Demos.Rcv.ProcessAxioms rcv-tabulate rcv-process
mkdir -p build/verified build/rcv
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.Tabulate Demos.Rcv.TabulateProgram.compiled.module build/verified/rcvTabulate.wasm
tools/leanrun --timeout 20m lake env lean --run tools/Emit.lean \
  Demos.Rcv.ProcessModule Demos.Rcv.Process.module build/rcv/process.wasm
wasm-tools validate build/rcv/process.wasm
tests/rcv/native.sh
```

A converter writes a contest's canonical ballot file `FILE` from a vendor's records, and each other form of the table reads `FILE` and writes its report.  `uv run tests/rcv/fetch.py` downloads the corpus into `tmp/rcv-data`, and `uv run tests/rcv/check.py` writes the canonical files of its contests under `tmp/rcv-data/canonical`.  [The corpus's scripts](../../tests/rcv/README.md#scripts) describe the converters' options and the checks of the counts against the County's reports.

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

`tests/rcv/check.py` converts D. Otis's records, 30,983 ballots of five rankings each, to a canonical file of 803,011 bytes.  The candidates are those of the County's report in its order, with the write-ins as candidate 4 of kind `aggregate-writein`, the tie-break order is `1 2 3 4`, and each ballot line holds its record's `ballotID` as its identifier.  The module's export `tabulate`, run in the Wasmtime host on that file, returns the report below, of 766 bytes, and the WASI process, the C executable, native Lean, and the reference write the same bytes.

```
rcv-report 1
rule oakland-1105 revision 1, Oakland City Charter sections 1103 and 1105 (February 2007), Cal. Elec. Code sections 15341 (updated 1999-01-01) and 15342(d) (updated 2012-01-01), texts read 2026-11-09
contest Oakland_20221108_SchoolBoardD4
positions 5
candidates 4
candidate 1 listed MIKE HUTCHINSON
candidate 2 listed PECOLIA MANIGO
candidate 3 listed NICK RESNICK
candidate 4 aggregate-writein Write-in
order 1 2 3 4
ballots 30983
round 1
continuing 26432
votes 1 8227
votes 2 8190
votes 3 10015
inactive blank 4269
inactive uncounted 134
inactive overvote 148
inactive exhausted 0
eliminate lowest 2
round 2
continuing 24586
votes 1 12421
votes 3 12165
inactive blank 4269
inactive uncounted 134
inactive overvote 173
inactive exhausted 1821
winner 1
```

Round 1 has no majority, since Resnick's 10,015 votes are fewer than half of the 26,432 continuing ballots.  No qualifying set of rule 3 holds two or more candidates: Resnick's votes fall short of the 16,417 of Hutchinson and Manigo together, and the set below Hutchinson holds Manigo alone.  Rule 4 therefore eliminates Manigo, who has 37 fewer votes than Hutchinson.  In round 2 Manigo's 8,190 ballots count 4,194 for Hutchinson and 2,150 for Resnick, 1,821 are exhausted, and 25 are overvotes, so Hutchinson, 1,788 votes behind Resnick in round 1, finishes 256 votes ahead.  His 12,421 votes are more than half of the 24,586 continuing ballots, and rule 1 ends the count with Hutchinson as the winner.  The report marks no tie, so by T9 every tie-break order gives the same rounds.

The report's figures equal those of the County's corrected report, whose settings have `useFirstRoundSuspension="False"`, and the last two columns of the table give the two counts of [the faulty setting](#the-faulty-setting).  An empty cell is a figure that its source does not give: the reports of the module and the reference list only continuing candidates, and Table A gives only the candidates' votes, the suspended ballots, and the action of each round.  The Registrar's presentation, "Ranked-Choice Voting Tally, November 8, 2022 – General Election", which [the corpus](../../tests/rcv/README.md#sources) pins, gives Table A on slide 6.

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

### The comparison with the County's report

Apart from the 2022 suspension, the County's practice departs from the charter in two ways that change the rounds of a report: it eliminates one candidate per round where §1105(f) eliminates a batch, and it counts past a majority until two candidates remain.  T10 covers the first departure: the single count, which applies the charter's rules without the batch of rule 3, names the charter's winner, and where the charter's count eliminates a batch, the single count eliminates its members one per round.  [The comparison rule](requirements.md#comparison-with-alameda-countys-reports) therefore offsets the County's round numbers by `m` − 1 after a batch of `m`, and District 4's count has no batch, so the module's round `r` is the County's round `r`.

T11 compares the charter's count with the county count.  By T11(d), each round of the charter's count with two or more continuing candidates is a round of the county count with the same continuing set, votes, and inactive counts.  Both rounds of District 4 hold two or more candidates, and the county count has two rounds for three counted candidates, so its rounds are the module's, and T11(c) gives Hutchinson as its winner.  The charter's majority stop and the County's stop at two candidates fall in the same round, so the corrected report has no round beyond the charter's count.

The theorems relate the module's count to the county count, a Lean definition, and say nothing about the County's report.  `check.py` compares the report's figures with the reference's counts, and `district4.py` compares them with its own recount of D. Otis's records, both through the requirements' mapping of the categories: Blanks is `blank` plus `uncounted`, Overvotes is `overvote`, and Exhausted is `exhausted`.  Every figure of both rounds agrees, and the 4,403 Blanks include the 134 ballots that rank only write-ins, which the count passes over under Cal. Elec. Code §15341.  The converter that writes the canonical file has no proof, and `check.py` tests it by reading the identifiers and rankings back from the file and comparing them with D. Otis's records.

### The faulty setting

Each 2022 Oakland report of the corpus other than District 4's sets `useFirstRoundSuspension="True"`, which withheld ballots from round 1.  The requirements state its rule as the faulty setting: the county count, except that round 1 counts as suspended each ballot whose first position is empty or holds one uncounted candidate and whose interpretation in round 1 counts for a candidate or is `overvote`.  From round 2 on, every ballot counts as the requirements state.  `reference.py --suspend` applies the rule to the canonical file, `district4.py` and `recount.py --suspend` apply it to D. Otis's records, and the rule reproduces every round, Suspended rows included, of the six other 2022 reports with that setting whose contests have cast vote records in the corpus.

In District 4 the rule suspends 235 ballots, 100 whose first ranking is empty and 135 that rank a write-in first.  Under the charter, 115 of them count for Hutchinson in round 1, 37 for Manigo, and 61 for Resnick, and 22 are overvotes, as slide 5 of the Registrar's presentation shows.  The suspension takes 78 more votes from Hutchinson than from Manigo, so Hutchinson's lead of 37 votes becomes a deficit of 41, and round 1 eliminates him.  In round 2 his 8,112 ballots count 3,492 for Manigo and 2,327 for Resnick, and the suspended ballots return, 108 of them for Manigo and 71 for Resnick.  Resnick finishes with 12,352 votes against Manigo's 11,753, and the faulty setting names him.  Table A on slide 6, under the caption "Table A shows the certified results using the incorrect RCV configuration", gives the same votes in both rounds and the same 235 suspended ballots.

No module implements the faulty setting, since it departs from §1105(d)(1), which counts every ballot in round 1 for its first choice, and from §1105(g), which advances a ballot past a ranking with no candidate "in the first or any round".  A module counts under the governing texts that its rule identifier names.  The reference's report under the faulty setting has the rule line `rule alameda-county-count first-round-suspension` and the line `inactive suspended` in each round, so that no one can take it for the charter's report.

### Reproducing the case study

The commands below assume the Wasmtime host and `build/rcv/process.wasm` of [Running the tabulator](#running-the-tabulator).  They fetch the corpus, write the canonical files, print the WASI process's report of District 4, print the reference's report under the faulty setting, and recount D. Otis's records with `district4.py`, which compares its counts with the corrected report and with slides 5 and 6.  The slides' tables are images, so `district4.py` holds their figures as constants.  It prints the lines below and exits with status 0, and its line on the write-in gives round 1 with the aggregate write-in counted as a fourth candidate, figures that match neither of the County's counts.

```sh
uv run tests/rcv/fetch.py
uv run tests/rcv/check.py
build/tools/leanexe-wasmtime-host run build/rcv/process.wasm \
  < tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv
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

## Design

| File | Contents |
|---|---|
| [`Contest.lean`](Contest.lean) | The contest structure: the contest identifier and the candidates' names as bytes, the kinds, the tie-break order, and each ballot's optional identifier and position words, with `Contest.WellFormed`, the constraints |
| [`Spec.lean`](Spec.lean) | The interpretation of a ballot, the rounds, the count, the canonical file's writer `write`, the report, and the word forms |
| [`Read.lean`](Read.lean) | The reader `read` of the canonical file, the error rule by line number, and `reportFile` |
| [`Cases.lean`](Cases.lean) | `#guard` checks of the worked example, byte for byte, and of the requirements' edge cases |
| [`Variants.lean`](Variants.lean) | The single count and the county count |
| [`Rounds.lean`](Rounds.lean), [`Stability.lean`](Stability.lean), [`Batch.lean`](Batch.lean), [`Holder.lean`](Holder.lean), [`Winner.lean`](Winner.lean), [`Properties.lean`](Properties.lean) | T4 to T7 and T9, T8, T10, T11, T3, and T12 to T15 |
| [`ReadLemmas.lean`](ReadLemmas.lean), [`ReadProof.lean`](ReadProof.lean), [`ReadError.lean`](ReadError.lean) | T2(a) to (c) and the lemmas about the file's forms that the reader's and the printer's proofs share |
| [`Program.lean`](Program.lean) | The count over words in the verified compiler's dialect |
| [`RefineBits.lean`](RefineBits.lean), [`RefineTally.lean`](RefineTally.lean), [`RefineRule.lean`](RefineRule.lean), [`Refinement.lean`](Refinement.lean) | The refinement of the count over words: positions, masks, and loops as folds, the tally of a round, the decision of a round, and `count_eq` |
| [`Compiled.lean`](Compiled.lean), [`VerifiedCall.lean`](VerifiedCall.lean), [`File.lean`](File.lean) | The module `rcvCount`, its call theorem, and the theorems of its emitted file |
| [`ReadWords.lean`](ReadWords.lean), [`ReadProgram.lean`](ReadProgram.lean), [`ReadProgramProof.lean`](ReadProgramProof.lean), [`ReadProgramMain.lean`](ReadProgramMain.lean) | The reader's result words, the reader program, T2(d), and `readContest_eq` |
| [`PrintProgram.lean`](PrintProgram.lean), [`PrintProof.lean`](PrintProof.lean) | The printers of the report and of the error report, and `printReport_eq` |
| [`TabulateProgram.lean`](TabulateProgram.lean), [`TabulateProof.lean`](TabulateProof.lean) | `tabulate`, which composes the reader, the count, and the printers, and `tabulate_eq` |
| [`Tabulate.lean`](Tabulate.lean), [`TabulateCall.lean`](TabulateCall.lean), [`TabulateBound.lean`](TabulateBound.lean), [`TabulateFile.lean`](TabulateFile.lean) | The module `rcvTabulate`, its call theorems and the C theorem, the closed forms of the bounds, and the theorems of its emitted file |
| [`Process.lean`](Process.lean), [`ProcessFlat.lean`](ProcessFlat.lean), [`ProcessWasi.lean`](ProcessWasi.lean), [`ProcessModule.lean`](ProcessModule.lean) | The WASI process, the representation of its state, its compilation, and its command module |
| [`ProcessFuture.lean`](ProcessFuture.lean), [`ProcessControl.lean`](ProcessControl.lean), [`ProcessCorrect.lean`](ProcessCorrect.lean), [`ProcessSizes.lean`](ProcessSizes.lean), [`ProcessCharges.lean`](ProcessCharges.lean), [`ProcessRun.lean`](ProcessRun.lean), [`ProcessProof.lean`](ProcessProof.lean), [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean), [`ProcessAxioms.lean`](ProcessAxioms.lean) | The process's invariant, termination, and output, the allocation charges, the runs of a compiled process, the refinement, the theorems of the module, and the axiom audit |
| [`tabulate.c`](tabulate.c) | The calling code of the C executables |
| [`Native.lean`](Native.lean), [`RoundsNative.lean`](RoundsNative.lean), [`StabilityNative.lean`](StabilityNative.lean), [`PropertiesNative.lean`](PropertiesNative.lean), [`TabulateNative.lean`](TabulateNative.lean), [`ProcessNative.lean`](ProcessNative.lean) | The executables `rcv-spec`, `rcv-rounds`, `rcv-stability`, `rcv-properties`, `rcv-tabulate`, and `rcv-process` |

### The specification and the reader

The specification states the requirements' count over lists, natural numbers, and 64-bit position words, with no reference to a program, and every definition computes, so native Lean runs it on canonical files.  The count reads the kinds, the tie-break order, and the position words, while the names appear only in the file and the report, and the ballots' identifiers only in the file.  [`Contest.lean`](Contest.lean) states the contest structure, [`Spec.lean`](Spec.lean) the count, the writer, the report, and the word forms, and [`Read.lean`](Read.lean) the reader.

`interpret` examines a ballot's positions from the first against the continuing set.  `examine` applies the four rules of the interpretation and returns no outcome when it passes the last position, and `passedReason` then gives `blank`, `exhausted`, or `uncounted` from the ballot and the kinds alone.  `tally` interprets every ballot against the continuing set and counts the votes of each continuing candidate and the inactive ballots by reason.  `rule` applies the four rules of a round in order: the majority test `2 vᵣ(i) > Tᵣ`, the end with no winner when `Tᵣ = 0`, the batch of `batch`, which is the largest qualifying `L(X)` of two or more candidates under the strict test, and the elimination of the single candidate with the fewest votes or of the tied candidate latest in the order, which `latest` finds.  `count` runs rounds from the counted set until a rule ends the count, allowing one more round than there are counted candidates, and T3(d) shows that the count ends within that allowance.

`write` prints a contest structure as its canonical file, and `report` gives the report's bytes, whose header lines are lines 2 to `6 + n` of the file.  `countWords` reads a word array, returns `[0]` unless `Words.Valid` holds, and otherwise returns the result words of the count, and `contestWords` gives the contest words of a structure.  `Cases.lean` checks that `write` prints the worked example's structure as the requirements' ballot file and that `report` gives the requirements' report of it byte for byte, with the example's contest and result words, and its other checks cover the edge cases that the requirements list under "Tests", apart from the malformed files, with expected values worked out by hand from the rules.

[`Read.lean`](Read.lean) states the reader beside `write`.  `read` splits the file at LF with `List.splitOn`, so that line `j` is piece `j - 1` and ends with LF exactly when another piece follows it, and it takes the lines in order, each with the role that the header gives it: the format line, the contest identifier, `k`, `n`, the `n` candidate lines, the order, `N`, and the `N` ballot lines.  A parser for each role states the form of the grammar and the constraints of the requirements' tables, and the first line that is absent, lacks its LF, or fails its role ends the reading with its number and role.  After the last ballot line the rest of the file must be the empty piece after the final LF, so a further line or a final run of bytes without LF gives the error of role `end`.  `reportFile` is the requirements' `report b` of T1, and `lineOf`, `roleAt`, `meets`, and `faulty` state the requirements' error rule by line number independently of the order in which `read` takes the lines.

`read_write` splits the written file into its lines and the empty piece after the last LF, and each line reads back as the field that `write` printed in it: the decimal forms through `number_decimal`, the position fields through `parsePosition_field`, and the lines of several parts through the spaces and commas that `write` places between parts that hold none.  `write_of_read` runs the other way: each parser that succeeds gives the field whose printing is its line, and `List.intercalate_splitOn` joins the pieces back into the file.  `read_error_first` reads the pieces that `read` passes to line `j` as the pieces of the file from piece `j - 1` on (`readLine_drop`), so every line before the reported one meets its role.

### The proofs of the count's theorems

`run` takes the decision of a round as an argument, and `count` passes `rule`.  `Trace` describes the rounds of a count under any interpretation and any decision: a round in which the decision gives a winner is the last, and a round that eliminates is followed by the trace from its continuing set minus the eliminated candidates.  `Ends` states the properties of a decision that bound the rounds: every elimination names at least one candidate and only candidates of the continuing set, and a continuing set of at most one candidate ends the count.  `rule_ends` proves them for `rule`, and for such a decision `run_trace` gives a trace whenever the fuel is at least the larger of 1 and the size of the continuing set, so `count_trace` applies to `count`, whose fuel `K.length + 1` suffices.  `Trace.mem`, `Trace.head`, `Trace.next`, and `Trace.last_round` give each round's counts, continuing set, and decision, `run_perm` shows that the order of the ballots leaves the count unchanged, and `run_congr` equates the counts under two decisions that agree on every round of one of them.

[`Variants.lean`](Variants.lean) defines the single count and the county count as `run` from `K` with the count's interpretation and fuel and a decision of their own.  `ruleSingle` applies rules 1, 2, and 4, and `ruleCounty` applies rule 4 while three or more candidates continue and otherwise ends the count, where `countyWinner` names the candidate with more votes, the candidate alone, or none.  Both take rule 4 from `lowestDecision` and `ruleTied`, as `rule` does, and `ruleSingle_ends` and `ruleCounty_ends` prove `Ends` for them, so the lemmas about `Trace` apply to all three counts.

`Closed` states that an interpretation counts a ballot only for a member of the continuing set, and `Stable` states both statements of T8.  T10 holds for every interpretation with both properties, as `run_batch_winner`, `run_batch_rounds`, and `run_batch_members` state for the counts from any continuing set without repeated candidates, and `interpret_closed` and `interpret_stable` give the properties for `interpret`.  `BatchAt` collects the facts of a round that eliminates the batch `B = L(X)`, and `walk` follows the single count or the county count from such a round.  Against every set between the count's next continuing set and the batch round's, the members of `B` that continue have fewer votes than every other continuing candidate (`batch_lt`), so rule 4 eliminates one of them per round, and a candidate with a majority lies outside `B` and keeps it against the count's next continuing set (`batch_holder_rest`).  `county_holder` and `county_rounds` state T11(b) and T11(d) over traces, and `trace_tied` and `trace_tie` the two directions of T3(c).

The proof of T12 evaluates round 1 of the count and of the single count with `rule_holder` and `find_holder`, and it takes the county count's winner from `county_holder`.  `trace_not_loser` proves T13 over traces for every interpretation with `Closed` and `Stable`: when two or more candidates continue in the last round, the winner's majority persists by T11(a) against the pair of itself and any other candidate, and when the winner continues alone, the round before eliminated one candidate, which had the fewest votes against a set that holds both, so it beats the winner.  For T14, `interpret_prefix` shows that a ballot whose position marks only a continuing candidate has an interpretation that its positions up to that one determine, `trace_winner_all` keeps the count's winner in every round, and `trace_ballots` shows that ballots that give every round of a trace the same counts give the same trace.  T15 evaluates the counts and the constraints of its two contests in the kernel with `decide +kernel`.

### The program over words

[`Program.lean`](Program.lean) states the count over words in the verified compiler's dialect: `count` takes a contest array in the word form of the requirements and returns the result words of `Demos.Rcv.Spec.countArray`.  A set of candidates is a word with bit `i - 1` for candidate `i`, the form of the result words' masks, so the continuing set of a round is one word and a test of membership is a shift and a mask.  `validArray` checks the header, the length `3 + 2n + Nk`, the kinds, the order, and every position word in one pass over the array.  `countValid` runs the rounds in a `LeanExe.repeatWhile` whose fuel is one more than the number of counted candidates, the fuel of `Demos.Rcv.Spec.count`, and whose state holds the continuing set, whether the count has ended, the winner, the number of rounds, and the result words.

Each round reads the ballots from the input array.  `examineAt`, a tail recursion that the compiler turns into a loop, examines a ballot's positions from the first and stops at the position that decides the interpretation, and `classify` reads one position word: it passes 0, gives an overvote for a word with bit 63 or with two or more bits, and for a word with one bit, whose position `bitIndex` finds in six tests, gives a vote when the continuing set holds the candidate and passes otherwise.  The union of the words passed gives the reason of a ballot that passes its last position: `blank` when the union is 0, `exhausted` when it holds a counted candidate, and `uncounted` otherwise.  `tallyRound` adds each ballot's slot to an array of 68 counters, slot `i - 1` for a vote for candidate `i` and slots 64 to 67 for the four reasons, and the loop updates the array in place.  `decideRound` applies the four rules to the counters: `majorityOf`, `continuingOf`, `fewestOf`, `tiedOf`, and `latestOf` take `n` steps each, and `batchOf` computes `L(X)` with `lowerOf` for each continuing `X` in `n²` steps, so a round costs time linear in the ballot words plus a term in `n²`.

The refinement proves that the program computes the specification.  [`RefineBits.lean`](RefineBits.lean) relates `classify` to `Demos.Rcv.Spec.position`, relates the masks of increasing candidate lists to their bits through Mathlib's `Nat.bitIndices`, and turns each loop over the candidates into a fold over `members`, the candidates of a mask.  [`RefineTally.lean`](RefineTally.lean) shows that `examineAt` gives the slot of `Demos.Rcv.Spec.interpret` and that each counter of `tallyRound` counts the ballots of its slot.  [`RefineRule.lean`](RefineRule.lean) proves each loop of `decideRound` against the specification's `find?`, `batch`, `min?`, filters, and `latest`, and [`Refinement.lean`](Refinement.lean) shows that `validArray` decides `Words.Valid`, follows the rounds against `Demos.Rcv.Spec.run` one round at a time in `go_eq`, and concludes `count_eq`: `Demos.Rcv.Program.count ws = Demos.Rcv.Spec.countArray ws` for every array of fewer than `2^64` words.

`count_callSpec` of [`VerifiedCall.lean`](VerifiedCall.lean) composes the generated `compiled.count.trapFree` of [`Compiled.lean`](Compiled.lean) with `count_eq`.  The generated bound `compiled.count.bound ws` is 152 bytes for an invalid array, the block of the result `[0]`.  For a valid array it is the smaller of two accountings, and `count_bound` takes the one that charges each push 80 bytes: 232 bytes once for the literal `#[1, 0]`; in each of at most `c + 1` rounds, with `c` the number of counted candidates, 600 bytes for the block of 68 counters and `80 (n + 9)` bytes for the round's words; and `16 (s + 1) + 80` bytes for the move of the `s` result words to a block with room for the winner's word.  With `n` and `c` at most 63 and `s` at most 4,610, the bound is at most 481,128 bytes for every array.

### The reader and the printers

[`ReadProgram.lean`](ReadProgram.lean) states the reader in the verified compiler's dialect.  `readContest` takes a buffer of bytes and returns the contest's words of the requirements' section "Word forms of the count" for a well-formed file, and `[0, j, code]` for a malformed file whose first faulty line is `j`, with the code of its role from 0 for `format` to 8 for `end`.  `findByte` finds the next LF, space, comma, or `|`, and the texts of the format are words of eight bytes that `matchWord` compares with the buffer.  `readNumber` reads at most 20 digits and tests before each digit that ten times the value read plus the digit stays below `2^64`.  The loops over the numbers of an order line, the indices of a field, and the fields of a ballot line recurse on a count of the parts left, and those over the candidate lines and the ballot lines on the number of lines left.

[`PrintProgram.lean`](PrintProgram.lean) states the printers.  `printReport b n res` collects the report's bytes in an array of words: the first two lines, lines 2 to `6 + n` of the file copied from `b`, the lines of each round from the count's result words, and the winner line.  `toBytes` then copies the array into a buffer, `pushNumber` appends the decimal digits of a word with `digitCount` and `digitByte` of [the decimal text of `Int64`](../../Library/Numerics/Decimal/Int64Text/README.md), and the members of a mask print in increasing index.  `printError j code` prints the error report.

| Theorem | File | Statement |
|---|---|---|
| `Demos.Rcv.ReadProgram.readContest_eq` | [`ReadProgramMain.lean`](ReadProgramMain.lean) | `(readContest b).toList = readResult (bytesOf b)` for every buffer of fewer than `2^64` bytes, where `readResult` of [`ReadWords.lean`](ReadWords.lean) gives the contest's words of a well-formed file and `[0, j, code]` of a malformed one |
| `Demos.Rcv.PrintProgram.printReport_eq` | [`PrintProof.lean`](PrintProof.lean) | For a structure `c` that meets the constraints and a buffer that holds `write c`, `printReport` on the buffer, `n`, and the result words of the count of `c` prints `report c`, when the report has fewer than `2^64` bytes |
| `Demos.Rcv.TabulateProgram.printError_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `printError` on a line `j < 2^64` and the code of a role `r` prints `errorReport j r` |
| `Demos.Rcv.TabulateProgram.tabulate_eq` | [`TabulateProof.lean`](TabulateProof.lean) | `bytesOf (tabulate b) = reportFile (bytesOf b)` for every buffer of fewer than `2^32` bytes |

[`ReadProgramProof.lean`](ReadProgramProof.lean) reads the bytes from position `s` to position `e` as `slice b s e` and ties each loop of the reader program to the specification's split at the same separator through `findByte_split`, and [`ReadProgramMain.lean`](ReadProgramMain.lean) follows `readLines` line by line.  T2(d), `readNumber_whole`, relates the program's `readNumber` to the digits that the printer's `pushNumber` appends (`pushNumber_toList`).  [`PrintProof.lean`](PrintProof.lean) uses the theorems of `Rounds.lean`: each round's continuing set is an increasing list of candidates from 1 to `n`, and each elimination names members of it, so the masks of the result words print the round's lines.

### The export `tabulate` and its bound

`tabulate` of [`TabulateProgram.lean`](TabulateProgram.lean) composes the reader program, the count program `Demos.Rcv.Program.count`, and the printers: it prints the error report when the reader's first word is 0, and otherwise the report from the file, `n`, and the count of the reader's words.  [`Tabulate.lean`](Tabulate.lean) compiles the functions of the count, of the reader, and of the printers into one module.  [`TabulateCall.lean`](TabulateCall.lean), which imports the module and the proofs, states that the module's exports `count`, `readContest`, `printReport`, `printError`, and `tabulate` are functions 22, 47, 60, 62, and 63 (`exports`), and it states `tabulate_callSpec` and the call theorems `readContest_callSpec`, `printReport_callSpec`, and `printError_callSpec` of the parts.

`tabulate_eq` follows the two results of the reader.  For a malformed file `read_error_lt` bounds the line number below `2^64`, and `printError_eq` gives the error report.  For a well-formed file, T2(b) gives the structure `c` whose writing is the file, `countWords_contestWords` equates the count of the reader's words with the result words of `countContest c`, `Demos.Rcv.Refine.count_eq` equates the program's count with the specification's, and `printReport_eq` prints `report c`, whose length `report_length_lt` bounds below `2^64` for a file of fewer than `2^32` bytes.  A buffer that a store holds has fewer than `2^32` bytes (`size_lt_of_borrowed`), so the call theorem covers every buffer.

[`TabulateBound.lean`](TabulateBound.lean) closes the generated bound of `tabulate` in the size of the file.  A push onto a paid array costs 80 bytes.  The reader pushes one word for each candidate line, each index of the order line, and each position field of a ballot line, whose fields end at distinct commas and LFs, so its bound grows by 80 bytes for each byte of the file.  The printers push the report's bytes, of which the header lines are at most 20,777 and the rounds at most 64 of at most 63 candidates each, and copy the report into the buffer that they return.  The proofs bound each tail loop of the reader by induction on its count, with `Verified.Tail.costAt_rank_eq` and the generated step's value at each branch, and the printers' costs by `grw` with the bounds of their callees.

| Theorem | Statement |
|---|---|
| `tabulate_bound` | `compiled.tabulate.bound b ≤ 80 * b.data.size + 33702909` for every buffer of fewer than `2^32` bytes |
| `readContest_bound` | `compiled.readContest.bound b ≤ 80 * b.data.size + 10704`: the two array literals, at most 63 candidate lines and 63 indices of the order, and the fields of the ballot lines |
| `printReport_bound` | For `n` of at most 63 candidates and at most 64 rounds in `res`, `compiled.printReport.bound (b, n, res)` is at most 80 bytes for each byte of the header lines, the block of the report, and 30,247,832 bytes |
| `printError_bound` | `compiled.printError.bound (j, code)` is at most the block of the error report and 20,152 bytes |
| `count_bound_eq` | The tabulator's compilation and [`Compiled.lean`](Compiled.lean) generate the same bound for `count`, which `Demos.Rcv.Program.count_bound` closes at 481,128 bytes |
| `headerText_le`, `reportFile_length_le` | The header lines of a structure that meets the constraints hold at most 20,777 bytes, and every report at most 1,301,030 |

### The WASI process

[`Process.lean`](Process.lean) runs the tabulator over stdin and stdout.  Its `begin` reads the whole standard input with `readAll 50000000`, which [the WASI guide](../../docs/wasi.md#operations-and-results) describes, into one buffer with room for 50,004,096 bytes, whose unused tail receives each read of at most 4,096 bytes, and returns a state that holds `tabulate` of the input.  Each step writes the rest of the report, continuing after short writes, and the process stops with status 0 when the report is written.  A read or a write that returns an errno stops it with that errno, and an input of more than 50,000,000 bytes stops it with status 22, WASI's `fbig`, before `tabulate` and with nothing written.  [`ProcessWasi.lean`](ProcessWasi.lean) compiles the functions of `Tabulate.lean` and the process's own with `verified_compile_wasi`, [`ProcessModule.lean`](ProcessModule.lean) composes the command module, and [`ProcessNative.lean`](ProcessNative.lean) is the executable `rcv-process`, which runs the process on the operating system's stdin and stdout.

The theorems follow [the order book's process](../OrderBook/README.md#the-wasi-process) under [StreamFold's host assumptions](../StreamFold/StreamHost.lean).  The Oakland and the Maine processes share their state, their steps, and the form of `begin`, so the lemmas about the steps and the runs hold for both: [`ProcessFlat.lean`](ProcessFlat.lean) holds the state's `Flat` instances and its type `stateTy`, `beginWith tab` is `begin` for a report function `tab`, and [`ProcessRun.lean`](ProcessRun.lean) states the runs of every `Compiled start`, a program that `verified_compile_wasi` compiled with the entry `processEntry`, together with the facts that the generic WASI theorems take and the relations of its `begin` and `step` to the native ones.  `implements`, `terminates_of_room`, and `exits_long_of_room` are the instances of `Compiled.implements`, `Compiled.terminates_of_room`, and `Compiled.exits_long_of_room` for this process's `compiledProcess`.

| Theorem | File | Statement |
|---|---|---|
| `process_output` | [`ProcessCorrect.lean`](ProcessCorrect.lean) | From an empty output history, for an input of at most 50,000,000 bytes, every run of the native `begin` returns a running state with status 0, from which some execution of the native process writes exactly `expectedOutput` of the input, the bytes of `reportFile` of the input, and returns status 0 |
| `implements`, `run_initial` | [`ProcessProof.lean`](ProcessProof.lean) | Every modeled run of the module's `_start` that completes without exhausting Talos fuel matches a run of the native process, including runs that stop at an I/O error, a host trap, or a rejected exit |
| `bytes` | [`ProcessProof.lean`](ProcessProof.lean) | One byte sequence encodes the module, decodes to it, is a valid binary, and has `implements` |
| `processMemory_le` | [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | The memory of a run, 4,085,008,138 bytes, fits above the literal pool in the 65,535 pages of the module's memory |

[StreamFold's theorems on `readAll`](../StreamFold/ReadAll.lean) give, under the host assumptions, the whole input at EOF for an input of at most the limit and more than the limit's bytes for a longer one, and [`ProcessFuture.lean`](ProcessFuture.lean) states with them what `beginWith tab` returns: the running state of `tab` of the input with nothing written (`beginWith_report`, and for `begin` `begin_report`), or the stopped state with status 22 (`beginWith_long` and `begin_long`).  The invariant `Future` relates a state after `begin` to the whole input: the input is read, and the output written so far followed by the output that remains is the report, whose length `reportFile_length_le` bounds.  [`ProcessControl.lean`](ProcessControl.lean) proves the termination of the steps with a rank of the unwritten output and the host's credit for zero-byte writes.

[`ProcessCharges.lean`](ProcessCharges.lean) bounds the allocation of `begin` by 4,083,707,053 bytes (`beginCharge_eq`): the allocation of `readAll`'s buffer, 50,004,144 bytes, and the bound of `tabulate` on 50,000,000 bytes, `80 · 50,000,000 + 33,702,909`, which `tabulate_bound` gives since the WASI compilation's bound of `tabulate` is `compiled.tabulate.bound` by definition (`tabulate_bound_eq`).  A copy of a state costs at most 1,301,085 bytes (`copyLimit`) and a write step at most two copies (`stepCharge`), so the memory of a run, `processMemory`, is `beginCharge` and one copy, which also covers a step with the copies of the states before and after it.  `processMemory_le` states that it fits above the literal pool, which ends at 4,096 bytes, in the 65,535 pages of the module's memory, so neither `initial_terminates` nor `initial_exits_long` has a memory premise.  `Compiled.target_terminates` of `ProcessRun.lean` takes the status at which `begin` stops, so that the run above the limit, which stops in `begin`, has its own theorem.

`readAll` writes each read into the buffer in place, and the state that the process loop copies after each write step holds only the report, so no read and no step does work that grows with the input already read.  StreamFold's host assumptions fix the read capacity at 4,096 bytes, so a process with larger reads needs host assumptions of its own.  [The running times](#running-times-and-build-costs) give the process's times on inputs of up to 50,000,001 bytes.

### The C translation

[`tests/rcv/native.sh`](../../tests/rcv/native.sh) builds `build/rcv/native/rcv-tabulate-c`, the module translated to C and compiled with CompCert, which reads a canonical file and writes its report.  `native-verified build` writes the C text of the translation of `compiled.module` that `compiled.translation_eq` states, has `clightgen` read it back, compares that Clight with the translation, and compiles the text with `ccomp` only when they match.  `ccomp` links the object with the export tables, [`tabulate.c`](tabulate.c), and `tools/native-host.c`.  `tabulate.c` places the file's bytes in a block that the module's `alloc` returns, calls the export `tabulate`, tests `lx_status`, and writes the bytes of the returned buffer.  The option `(cap := 11520)` of `Tabulate.lean` gives the translation 11,520 pages of `lx_mem`, 754,974,720 bytes, which leave about 26 MiB free below `lx_in` in the 1 GiB of RAM of the bare-metal machine of `tests/baremetal/verified.sh`, and leaves the module's bytes as they are.  `tabulate_native_size` of [`TabulateBound.lean`](TabulateBound.lean) states that the C function returns the report of a file of at most `L` bytes when `top + 80 L + 33,702,909` is at most the size of `lx_mem`, and `tabulate_native_8800000` states it for every file of at most 8,800,000 bytes from a heap whose `top` is at most 16,777,216 bytes, which covers the corpus's largest file, of 4,696,262 bytes.

### The AArch64 image

[The image's program](../../tests/TestSupport/A64/Rcv.lean) runs `tabulate`, function 63 of `compiled.module`, on the AArch64 bare-metal path of [the A64 document](../../docs/a64-bare-metal.md), whose code generator reads the same module that the C translator reads.  The image's entry routine reads from the PL011 UART a length of eight bytes, the lowest first, and then the file, of at most 8,800,000 bytes, into a block from the module's allocator, calls `tabulate`, writes the bytes of the report, and ends with the status byte 0.  A length above the limit ends the run with the status byte 64 alone, and a byte that the UART receives with an error flag with 65 alone.  The memory's cap of 11,392 pages, 712 MiB, holds the file's block and the bound `80 L + 33,702,909` of `tabulate_bound` above the heap's start for every file within the limit, and the stack's room of 512 KiB holds the 6,240 bytes that the calls of `tabulate` use, so the run reaches neither the trap of the allocator nor that of the stack.  `rcv_runs` of [`RcvRuns.lean`](../../tests/TestSupport/A64/RcvRuns.lean) joins `tabulate_trapFree` and `tabulate_bound` to the program's theorem, and [the image's theorems](../../tests/TestSupport/A64/ImageFilesRcv.lean) carry it to the bytes of the image file, whose comparison with the generator's output the kernel checks in 107 s with a peak of 26.6 GiB.  [The trusted base](#trusted-base) gives the items that the image's theorems depend on.

### The browser page

[The recount page](../../tests/web/rcv/index.html), which `uv run tests/web/serve.py` serves at http://127.0.0.1:8000/rcv/, recounts a canonical file that the user chooses on their computer, with this module or with [the Maine module](Maine/README.md#the-browser-page).  The browser reads the file with the File API and sends nothing to the server, and the page shows the report's bytes as text, with a link that saves them, beside the SHA-256 of the module that it loaded.  [`tabulate.js`](../../tests/web/rcv/tabulate.js) calls the export `tabulate` as `tabulate_callSpec` requires.  For each file it creates a fresh instance of the module, whose store the generated `compiled.initial` and `Verified.Ready.initial` prove ready, calls `alloc` with the file's length, writes the file's bytes into the block, passes the block's root and the length to `tabulate`, and copies the bytes at the root and the length that the call returns.

The premise of the call theorem bounds the allocator's `top`, which the module does not export.  `top` lies inside the memory (`Heap.At`), and `alloc` raises it by at most 48 bytes and a block of `allocSize len` bytes (`Heap.allocate_top`), so the premise holds when the sum of the memory's size, `48 + allocSize len`, and the bound is at most 65,535 pages.  The page takes the bound `80 L + 33,702,909` of `tabulate_bound` for a file of `L` bytes, checks the sum before `alloc`, and grows the memory by the room it needs, so that neither `alloc` nor `tabulate` grows the memory.  Talos grows memory whenever the cap allows, while a browser may refuse, and the growth before the call turns such a refusal into a refusal of the file.  From the fresh instance's 16 pages, the cap admits files of up to 52,594,447 bytes, and the corpus's largest file needs 414,100,181 bytes of room.

The page's JavaScript lies outside the theorems.  It is trusted to create the instance, to check the room, to place the file's bytes, and to copy the report, and the browser's engine is trusted to agree with Talos's semantics, as [the trusted base](../../docs/trusted-base.md#wasm-webassembly-modules-of-the-verified-compiler) states for every host.  The page decodes the report as UTF-8 for display, and the saved file holds the report's bytes.

## Tests

### The statements decided natively

The executables `rcv-rounds`, `rcv-stability`, and `rcv-properties` decide the conclusions of the count's theorems natively through the specification, on the contest words of the edge cases and on seeded random contests, and they reject false variants of the statements, which shows that each test can fail.  Each check transcribes a theorem's conclusion as a Boolean function over the specification's definitions, and each executable prints its counts and exits with status 1 when a statement fails.  The random contests come from seeded generators, so each command gives the same counts on every run.

[`RoundsNative.lean`](RoundsNative.lean), the executable `rcv-rounds`, decides T4, T5, T6, T7, and T9.  Its `edges` mode reads contest-word files, and its `random` mode draws seeded contests in which a ballot has an identifier with probability one in three.  The conclusions hold on the 285 valid contests of the edge cases' word files and on 10,000 random contests of up to eight candidates of every kind, five positions, and 60 ballots, which together have 19,189 rounds, among them 919 batches, 3,829 lowest eliminations, and 4,156 eliminations by order.  Of 41,686 orders tried for T9, 34,292 meet its hypothesis, 4,168 of them in counts with a marked tie and with an order other than the contest's, and each gives the same count and the stated report lines, while the other 7,394 change the count.  The runs reject T4 with the earliest instead of the latest tied member on 3,017 contests, T4 with the smallest qualifying set of two or more instead of the largest on 91, T5 with the continuing ballots counted twice on 9,125, and T6 with an unchanged continuing set on 4,085.

```sh
uv run tests/rcv/edges.py
tools/leanrun --timeout 20m lake build rcv-rounds
.lake/build/bin/rcv-rounds edges tmp/rcv-edges/*.words
.lake/build/bin/rcv-rounds random 1 4000 5 4 12
.lake/build/bin/rcv-rounds random 2 4000 6 4 30
.lake/build/bin/rcv-rounds random 3 2000 8 5 60
```

[`StabilityNative.lean`](StabilityNative.lean), the executable `rcv-stability`, decides T3, T8, T10, and T11.  The conclusions hold on the 304 valid contests of the edge cases' and the corpus's word files, on 300,000 random contests of up to seven candidates of every kind, four positions, and 40 ballots, on 200,000 random interpretations with `Closed` and `Stable`, and on the 460,460 contests of every multiset of up to six ballots from 20 ballots over three listed candidates and a write-in, under two orders.  The random contests have 563,444 rounds, 74,565 batches, 3,568 single counts that end inside a batch, and 27,803 tied final rounds, the random interpretations 66,556 batches and 1,930 single counts that end inside one, and the exhaustive contests 95,750 tied final rounds.  Each ballot of a random interpretation has an order of preference over some candidates and a reason: against a set, it counts for the first candidate of the order in the set, and otherwise it is inactive with the reason.  Every interpretation with `Closed` and `Stable` treats each ballot in this way, since the sets against which a ballot is inactive are closed under subsets and share the reason of the empty set, and T8's first statement makes the choices on pairs of candidates a linear order whose first member in a set is the choice on the set.

The mode `planted` rejects T10(a) under an interpretation that counts a ballot for a candidate outside the set, as finding 1 of [the review](review.md#review) describes, on 1,216 cases, T10(c) without the end of the single count on 1,182 batches, T11(c) without its premise on 9,182 contests, and T8 for an overvote of continuing marks alone on 2,229,689 pairs of a ballot and two sets.  The mode `rounds` writes the round lines and the winner line of the count, the single count, or the county count of each contest-word file, and [`tests/rcv/variants.py`](../../tests/rcv/variants.py) requires them to equal those of `tests/rcv/reference.py` in its default, `--single`, and `--county` modes.  They agree on the 285 valid contests of the edge cases' word files, whose three counts have 658, 758, and 749 rounds, and on the 19 contests of the corpus, with 33, 46, and 60 rounds, while a copy of the reference whose single count keeps rule 3 fails 36 of the comparisons.

```sh
uv run tests/rcv/edges.py
uv run tests/rcv/check.py
tools/leanrun --timeout 20m lake build rcv-stability
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

[`PropertiesNative.lean`](PropertiesNative.lean), the executable `rcv-properties`, decides T12 to T15.  It reads the contest words of the 285 valid contests of the edge cases, generates 34,000 seeded random contests of every kind of candidate, in which half of the ballots rank distinct candidates and one candidate takes the first position of up to 60 percent of the ballots, and counts the 106,260 contests of every multiset of up to five ballots of a 20-ballot alphabet under two orders.  On these inputs T12 holds for 88,790 candidates with a majority in round 1, 70,876 of them among three or more counted candidates, T13 for 89,043 counted candidates whom every other beats, 24,087 of them in counts of two or more rounds, and T14 for 3,766,242 replacements of a ballot, 1,163,880 of them in counts of two or more rounds, and `rcv-properties t15` reproduces the two counts of T15.  The checks of T14 and of monotonicity take at most 48 positions of each contest, spread evenly over its ballots.

The runs reject T12 with half of the continuing ballots in place of more than half for 42,332 candidates, and T12 with the county count ending after round 1 for 70,876.  T13 fails without its premise that `K` has two or more candidates for 9,925 candidates and with ties allowed in the premise for 8,558, and the Condorcet winner criterion, which instant runoff does not meet, fails for 827.  For T14, a change of a position before `p` changes the count in 509,465 of 907,670 replacements, a change of position `p` in 4,082,451 of 4,354,218, and a change of the positions after `p` when the count does not name `w` in 551,391 of 3,785,073, and moving the winner's single position to the front of a ballot changes the winner in 28 of 190,820 cases, the failure of monotonicity that T15 states.

```sh
uv run tests/rcv/edges.py
tools/leanrun --timeout 20m lake build rcv-properties
.lake/build/bin/rcv-properties t15
.lake/build/bin/rcv-properties edges tmp/rcv-edges/*.words
.lake/build/bin/rcv-properties random 1 10000 5 4 30
.lake/build/bin/rcv-properties random 2 4000 8 5 60
.lake/build/bin/rcv-properties random 3 20000 3 3 12
.lake/build/bin/rcv-properties exhaustive 5
```

### The forms compared with the reference

[`tests/rcv/compare.py`](../../tests/rcv/compare.py) compares the count over words.  For each word array it computes the reference's result words and requires the module `rcvCount`'s export `count` in the Wasmtime host, `rcv-spec array`, the specification, `rcv-spec program`, the program run natively, and the result file that `edges.py` or `check.py` wrote to give the same bytes.  A disagreement between `rcv-spec program` and the module points to the compilation, and one between it and `rcv-spec array` to the program.

```sh
tools/leanrun --timeout 60m lake build Demos.Rcv.VerifiedCall rcv-spec
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

`rcv-spec`, the executable of [`Native.lean`](Native.lean), reads a canonical file with a parser of its own and accepts it only when `write` prints the parsed structure as the file's exact bytes and the structure meets `Contest.WellFormed`.  Its modes `array` and `program` give the result words of `countArray` and of the program run natively, which `compare.py` uses, and its mode `district4` compares the round lines of the specification's report of the District 4 file with those of the requirements' District 4 report.  On the file that `check.py` writes, `rcv-spec district4 tmp/rcv-data/canonical/Oakland_20221108_SchoolBoardD4.rcv` prints `30983 ballots, 19 round lines, 0 differ from the requirements`.

[`tests/rcv/tabulate.py`](../../tests/rcv/tabulate.py) compares the tabulator on canonical files.  For each file it computes the reference's report and requires the module's export `tabulate` in the Wasmtime host, `rcv-tabulate report`, and the report that `edges.py`, `reader_edges.py`, or `check.py` wrote to give the same bytes, and its options add the standard output of the WASI process in the Wasmtime host, whose control record must be `wasi-exit 0`, of the native process `rcv-process`, and of the C executable `rcv-tabulate-c`.  [`tests/rcv/reader_edges.py`](../../tests/rcv/reader_edges.py) adds to the edge cases an absent line and a final run without LF in each role from `contest` to `ballot`, numbers of up to 21 digits next to `2^32` and `2^64` in each place that holds a number, and names of spaces alone.  The run with `/bin/cat` in place of the C executable reports all 93 of the reader's edge files as disagreements, so the comparison detects an executable that prints something else.

```sh
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

[`TabulateNative.lean`](TabulateNative.lean), the executable `rcv-tabulate`, runs the reader, the programs, and the statements of T2 natively.  Its mode `compare` compares `reportFile` with the reference's report beside each file, `programs` compares the reader program's words with `readResult` and the report that the reader program, the count over words, and the printer program give with the reference's, and `t2` and `t2-random` decide the statements of T2: a file that `read` accepts must print as itself through `write`, and its structure must meet the constraints and read back as itself, and for a file that `read` rejects the reported line must be the first faulty line with the role that `roleAt` gives it.  On the 633 edge files, the 93 of the reader's edge cases, and the 19 of the corpus, the reports of `reportFile` and of the programs equal the reference's byte for byte, and the statements of T2 hold, as they do for 20,000 random structures and 200,000 files mutated from them, of which `read` accepts 19,980.

```sh
tools/leanrun --timeout 20m lake build rcv-tabulate
.lake/build/bin/rcv-tabulate compare tmp/rcv-edges/*.rcv
.lake/build/bin/rcv-tabulate compare tmp/rcv-reader/*.rcv
.lake/build/bin/rcv-tabulate compare tmp/rcv-data/canonical/*.rcv
.lake/build/bin/rcv-tabulate programs tmp/rcv-edges/*.rcv
.lake/build/bin/rcv-tabulate programs tmp/rcv-reader/*.rcv
.lake/build/bin/rcv-tabulate programs tmp/rcv-data/canonical/*.rcv
.lake/build/bin/rcv-tabulate t2 tmp/rcv-edges/*.rcv
.lake/build/bin/rcv-tabulate t2 tmp/rcv-reader/*.rcv
.lake/build/bin/rcv-tabulate t2 tmp/rcv-data/canonical/*.rcv
.lake/build/bin/rcv-tabulate t2-random 1 20000
```

```
633 files, 284 well formed, 349 malformed, 0 differ
93 files, 2 well formed, 91 malformed, 0 differ
19 files, 19 well formed, 0 malformed, 0 differ
633 files, 0 with other words, 0 with another report
93 files, 0 with other words, 0 with another report
19 files, 0 with other words, 0 with another report
633 files, 284 accepted, 349 rejected, 0 failed
93 files, 2 accepted, 91 rejected, 0 failed
19 files, 19 accepted, 0 rejected, 0 failed
20000 structures read back, 200000 mutated files, 19980 accepted, 180020 rejected, 0 failed
```

[`tests/rcv/page.mjs`](../../tests/rcv/page.mjs) runs the page's calling code `tabulate.js` under Node on canonical files, with the page's bound, and requires each report to equal the reference's, with this module unless `--count maine` chooses the Maine module.  The executable `rcv-bound` of [`BoundMain.lean`](../../tests/TestSupport/Rcv/BoundMain.lean) prints each file's `compiled.tabulate.bound` in native Lean, and with `--bounds` the script requires the page's bound to be at least that value.  On the 633 edge files, the 93 files of the reader's edge cases, and the 19 contests of the corpus, the reports equal the reference's.  The page's bound is at least the generated bound on all 726 edge files, and the largest generated bound is 2,178,064 bytes, for a file of 61,449 bytes whose bound on the page is 38,618,829 bytes.  The page's bound is the closed form of `tabulate_bound`, which the theorem proves at least the generated bound for every file of fewer than `2^32` bytes, and the comparison with native Lean tests that relation on the edge files alone: native Lean's evaluation of the generated bound takes 24 s on the file of 61,449 bytes and 82 s on the corpus's smallest file, of 348,918 bytes, and it had not finished any of the four largest files of the Oakland and Maine corpora, of 4,385,795 to 8,262,002 bytes, after 44 minutes.  The script prints the module's SHA-256 and then the lines below, and [the recount page's description](../../tests/web/README.md#rcv-recount-rcv) gives the results of the page in headless Chromium.

```sh
tools/leanrun --timeout 60m lake build rcv-bound
tools/leanrun --timeout 60m sh -c \
  '.lake/build/bin/rcv-bound tmp/rcv-edges/*.rcv tmp/rcv-reader/*.rcv > tmp/rcv-bounds.txt'
node tests/rcv/page.mjs --bounds tmp/rcv-bounds.txt tmp/rcv-edges tmp/rcv-reader \
  tmp/rcv-data/canonical
```

```
tmp/rcv-edges: 633 files, 284 well-formed, 349 malformed, largest bound 38618829 bytes
tmp/rcv-reader: 93 files, 2 well-formed, 91 malformed, largest bound 33734909 bytes
tmp/rcv-data/canonical: 19 files, 19 well-formed, 0 malformed, largest bound 409403869 bytes
0 files refused or with a disagreement
```

### The verified compiler's tests

In the verified compiler's tests the modules are `rcvCount` and `rcvTabulate`: [the module registry](../../tests/verified/modules.txt) lists their compilations, and [the case generator](../../tests/TestSupport/Rcv/Cases.lean) gives their cases, which the executable `verified-cases-rcv` prints.  `tests/verified/run.sh --cases rcvCount` writes `build/verified/rcvCount.wasm`, validates it with `wasm-tools`, and compares 54 cases between the Wasmtime host and `Demos.Rcv.Spec.countArray` in native Lean.  Its cases hold the contest words of the contests of `Cases.lean`, its other arrays, most of them invalid, and random contests that SplitMix64 draws from fixed seeds, with up to 63 candidates, 63 positions, and 20,000 ballots, some of which three candidates dominate while the others form a tail that qualifies for a batch.  `tests/verified/run.sh --cases rcvTabulate` compares 86 cases with `Demos.Rcv.Spec.reportFile`: the canonical files of those contests, of contests with ballot identifiers, contest identifiers of 1 and 64 bytes, and names of bytes outside ASCII, the worked example's file cut after each of its lines, that file without its final LF and with a further line or further bytes, and edits of it that each break one line.  `tests/native/verified.sh --module NAME` translates each module to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same cases, and `lake env lean` on the file modules checks the file theorems against the files that `run.sh` wrote.

```sh
tests/verified/run.sh --cases rcvCount
tools/leanrun --timeout 10m lake env lean Demos/Rcv/File.lean
tests/native/verified.sh --module rcvCount
tests/verified/run.sh --cases rcvTabulate
tools/leanrun --timeout 10m lake env lean Demos/Rcv/TabulateFile.lean
tests/native/verified.sh --module rcvTabulate
```

```
verified: passed 54 failed 0
'Demos.Rcv.File.rcvCount_file' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demos.Rcv.File.rcvCount_file_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
rcvCount: 23 of 23 functions, 23 of 23 exports
rcvCount: the clightgen program matches the translation
native verified: passed 54 failed 0
verified: passed 86 failed 0
'Demos.Rcv.TabulateFile.rcvTabulate_file' depends on axioms: [propext, Classical.choice, Quot.sound]
'Demos.Rcv.TabulateFile.rcvTabulate_file_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
rcvTabulate: 64 of 64 functions, 64 of 64 exports
rcvTabulate: the clightgen program matches the translation
native verified: passed 86 failed 0
```

### The AArch64 image's runs

[`tests/baremetal/a64-rcv.sh`](../../tests/baremetal/a64-rcv.sh) builds and emits [the AArch64 image](#the-aarch64-image), checks QEMU's loading of it, with `--check` has the kernel check the image's theorems, and runs the image under QEMU 8.2.2 on the canonical files of each directory that it names.  [`a64_rcv.py`](../../tests/baremetal/a64_rcv.py) gives the UART a file backend that holds the eight bytes of the file's length and then the file, and it requires QEMU's exit status 0 and the UART's output to be the report of `rcv-tabulate-c` and the status byte 0, after it checks that the C executable's report equals the WASI process's.  It reads QEMU's position in the input file and the size of the UART's output every millisecond and splits each run's time into the startup, until the program has read the file's first byte, which includes the clear of the area's 712 MiB, the input, the computation, from QEMU's read of the last byte to the report's first byte, and the output, through QEMU's exit.  The runs took a quota of two cores on edgexpert-18ff, an AArch64 host, while other jobs ran there, and every report equals the reference's.

```sh
tests/baremetal/a64-rcv.sh --check tmp/rcv-data/canonical tmp/rcv-edges tmp/rcv-reader
ACCEL=kvm tests/baremetal/a64-rcv.sh tmp/rcv-data/canonical tmp/rcv-edges tmp/rcv-reader
```

| Files | Accelerator | Passed | Startup per run (s) | Input (s) | Computation (s) | Output (s) |
|---|---|---|---|---|---|---|
| The corpus, 19 files, 26,587,260 bytes | TCG | 19 | 0.41 to 0.44 | 373.1 | 4.55 | 0.14 |
| | KVM | 19 | 0.07 to 0.09 | 405.5 | 0.80 | 0.23 |
| The edge files, 726 files, 987,806 bytes | TCG | 726 | 0.41 to 0.44 | 15.9 | 4.79 | 5.01 |
| | KVM | 726 | 0.06 to 0.09 | 20.3 | 0.12 | 6.22 |

The input dominates every run: it takes 14.0 µs per byte over the corpus under TCG and 15.3 under KVM, and 12.9 to 18.5 for each file of 100,000 bytes or more.  The corpus's largest file, of 4,696,262 bytes, takes 65.0 s of input, 0.92 s of computation, and 0.01 s to write its report of 1,833 bytes under TCG, and 67.5 s, 0.18 s, and 0.01 s under KVM, where the C executable takes 0.07 s for the whole run.  The kernel's check of the image's theorems takes 107 s with a peak of 26.6 GiB, and each run of QEMU a peak of 774 MiB.

### Running times and build costs

The first table gives wall times of the WASI process in the Wasmtime 44 host, with the input from a file (`--stdin-file`) and from a pipe, of the native process `rcv-process`, with the input from a file, and of the C executable `rcv-tabulate-c`.  Each time is the median of three runs on edgexpert-18ff, an AArch64 host, under a CPU quota of two processors while other jobs ran there.  The inputs that hold the at-large file twice and four times over are malformed and give short error reports, the ten copies form one well-formed contest, and `tests/rcv/tabulate.py` finds the report of each of these inputs equal to the reference's.  The C executable ran on the inputs of fewer than 20,000,000 bytes.

| Input | Bytes | WASI, file (s) | WASI, pipe (s) | Native process (s) | C (s) |
|---|---|---|---|---|---|
| Oakland 2025 City Council, District 2 | 348,918 | 0.04 | 0.03 | 0.06 | < 0.01 |
| Oakland 2024 City Council, District 1 | 906,118 | 0.03 | 0.04 | 0.07 | 0.01 |
| Oakland 2025 Mayor | 2,534,293 | 0.05 | 0.10 | 0.19 | 0.05 |
| Oakland 2022 City Auditor | 3,312,770 | 0.08 | 0.09 | 0.15 | 0.04 |
| Oakland 2024 City Council, at large | 4,696,262 | 0.08 | 0.14 | 0.21 | 0.07 |
| The at-large file twice | 9,392,524 | 0.08 | 0.18 | 0.17 | 0.05 |
| The at-large file four times | 18,785,048 | 0.06 | 0.29 | 0.18 | 0.06 |
| Ten copies of the at-large ballots, one contest | 46,957,860 | 0.49 | 1.00 | 1.85 | |
| Zero bytes | 50,000,000 | 0.08 | 0.40 | 0.13 | |
| Zero bytes | 50,000,001 | 0.07 | 0.65 | 0.04 | |

The process's peak resident memory is 16 MiB on the first file and 198 MiB on the ten copies.  The 50,000,000 zero bytes give the error report with status 0, and one more byte gives status 22 with nothing written, from a file, from a pipe, and in the native process.  The C executable's peak is 21 MiB on the at-large file.

The second table gives the time and the peak resident memory of `lake env lean` on the three largest compilations, with their imports built, under `tools/leanrun --cpus 2 --threads 2 --memory-high 12G` on the same host.  `Tabulate.lean` runs `verified_compile` on the module, `ProcessWasi.lean` runs `verified_compile_wasi` on the module's functions and the process's, and `ProcessModule.lean` composes the command module and checks its validity and encoding.  `lake build` compiles independent files at the same time, so the build command of [Running the tabulator](#running-the-tabulator) gives the runner a limit of 12 GiB, above the largest peak.

| File | Time (s) | Peak memory (GiB) |
|---|---|---|
| [`Tabulate.lean`](Tabulate.lean) | 905 | 5.4 |
| [`ProcessWasi.lean`](ProcessWasi.lean) | 761 | 8.6 |
| [`ProcessModule.lean`](ProcessModule.lean) | 343 | 5.9 |

## The Maine module

[The Maine module](Maine/README.md) counts single-winner contests under 21-A M.R.S. §723-A and the rules of 29-250 C.M.R. ch. 535, with this module's file format, reader, tally of a round, and report lines, to which it adds the lines of its initial test.  Its examination of a ballot ends at two consecutive skipped rankings, an initial test elects a candidate ranked first alone on more than half of all ballots, and its rounds eliminate one candidate at a time until two remain, with no majority stop and no batch.  It has the forms of this module, with the export `tabulate` of `build/verified/rcvMaine.wasm`, a WASI process, a C translation, and the recount page's choice of module, and the same kinds of theorems, among them T11's statement that the initial test changes no winner.  Its README gives the theorems, the commands, and the tests, and [the Maine corpus](../../tests/rcv/maine/README.md) compares its counts with the Secretary of State's reports and with RCTab's.
