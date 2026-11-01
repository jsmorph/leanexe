# Order book: price-time matching for one instrument

[The program](Program.lean) is a deterministic step function over the two-sided central limit order book of one instrument.  It matches limit and market orders by price-time priority, with self-trade prevention, engine-assigned order ids, cancels, and reductions that keep priority, and it writes an event for every acceptance, rejection, trade, cancellation, and reduction.  The host sequences and authenticates commands, keeps the command log, and maps the engine's ids to client tags from the events, and recovery replays the log, which the stream theorems justify.  [The requirements](requirements.md) state the book in English, [the specification](Spec.lean) states them over lists, and [the refinement](Refinement.lean) proves that the program, which holds the book in fixed arrays, computes the specification.  `verified_compile` compiles the program into a module of 15,662 bytes and its translation to C, and [the call theorems](VerifiedCall.lean) carry the refinement to the module's exports.  [A WASI process](#the-wasi-process) runs the book over stdin and stdout, and `initial_terminates` proves the output and the exit of its module.  [The journal's design entry](../../devnotes.md#2026-10-31-the-design-of-a-two-sided-order-book) gives the decisions and their reasons.

## Book and interface

Prices run from 1 to 1,023 ticks, quantities from 1 to 2^32 − 1, and the book holds at most 4,096 resting orders.  Commands and events are records of seven words, which [the requirements](requirements.md#records) lay out: `limit`, `market`, `cancel`, and `reduce` commands, and `accepted`, `rejected`, `trade`, `cancelled`, and `reduced` events.  The program keeps five slot arrays of 4,097 words, the order id, account, remaining quantity, level, and next slot of each order, and two level arrays of 2,048 words, the first and last slot of the chain of orders at each side and price, with slot 0 as the end of a chain.  A book is these seven arrays, the next id, and the count of resting orders.

The module exports `run` and `top`.  `run` takes the seven arrays, which it consumes, the next id, the count, and a borrowed stream of command words, and returns the new book's seven arrays, next id, and count, and the event words.  `top` reads a book and returns the best bid price and the total quantity at it, and the best ask price and the total quantity at it, with 0 for both values of an empty side.  The reflector rejects the parameter of type `Unit` of `init`, so the module has no `init`, and a host passes arrays of zeros, next id 1, and count 0 for the empty book, which `init_inv` and `toSpec_init` describe.

## Files

| File | Content |
|---|---|
| [`requirements.md`](requirements.md), [`review.md`](review.md) | Requirements in English and the record of the specification's reviews |
| [`Spec.lean`](Spec.lean), [`Theorems.lean`](Theorems.lean) | Specification over lists of resting orders, and its theorems |
| [`Samples.lean`](Samples.lean), [`SpecRun.lean`](SpecRun.lean) | Command streams for each case of the requirements, and their printed events and books |
| [`Program.lean`](Program.lean) | Program over slot and level arrays, in the verified compiler's dialect |
| [`Abstract.lean`](Abstract.lean), [`Invariant.lean`](Invariant.lean) | Specification's book of a program's book, `toSpec`, and the representation invariant `Inv` |
| [`RefineChains.lean`](RefineChains.lean), [`RefineEffects.lean`](RefineEffects.lean), [`RefineHelpers.lean`](RefineHelpers.lean), [`RefineMatch.lean`](RefineMatch.lean), [`RefineStep.lean`](RefineStep.lean), [`RefineStream.lean`](RefineStream.lean), [`Refinement.lean`](Refinement.lean) | Refinement proof, from the chains of the levels to the stream theorems |
| [`Flat.lean`](Flat.lean), [`Verified.lean`](Verified.lean) | Representations for the compiler and the `verified_compile` command |
| [`VerifiedCall.lean`](VerifiedCall.lean) | Call theorems of the exports `run` and `top` |
| [`ProgramCounts.lean`](ProgramCounts.lean), [`Bound.lean`](Bound.lean) | Counts of events and array sizes on every book, and closed forms of `run`'s generated bound |
| [`Process.lean`](Process.lean), [`ProcessNative.lean`](ProcessNative.lean) | WASI process over stdin and stdout, and its native executable |
| [`ProcessCodec.lean`](ProcessCodec.lean), [`ProcessBatch.lean`](ProcessBatch.lean), [`ProcessControl.lean`](ProcessControl.lean), [`ProcessFuture.lean`](ProcessFuture.lean), [`ProcessCorrect.lean`](ProcessCorrect.lean) | Little-endian codec, batch lemma, output bounds and termination, invariant, and the native process's correctness |
| [`ProcessWasi.lean`](ProcessWasi.lean), [`ProcessModule.lean`](ProcessModule.lean), [`ProcessProof.lean`](ProcessProof.lean) | `verified_compile_wasi` of the process, its command module, and the module's refinement of the native process |
| [`ProcessTermination.lean`](ProcessTermination.lean), [`ProcessSizes.lean`](ProcessSizes.lean), [`ProcessCharges.lean`](ProcessCharges.lean), [`ProcessCompiledCorrect.lean`](ProcessCompiledCorrect.lean) | Typed termination, sizes of reached states, allocation charges, and the compiled process's correctness |
| [`tests/orderbook/`](../../tests/orderbook/README.md) | Comparisons of the program with the specification and with a Python reference written from the requirements, and tests of the WASI process |
| [`tests/TestSupport/OrderBook/Cases.lean`](../../tests/TestSupport/OrderBook/Cases.lean) | Module cases, which compare the module with native Lean |

## Theorems

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `run_valid`, `step_valid`, `empty_valid` | [Specification's theorems](Theorems.lean) | Next id below 2^64 − 1 throughout | `Spec.Valid` holds of the empty book and after every step and stream: sides in priority order and uncrossed, prices and quantities in range, distinct ids below the next id, and at most 4,096 resting orders. |
| `fill_shape`, `fill_prefix`, `submit_conserves`, the `rejects_` theorems, `step_cancel`, `step_reduce` | [Specification's theorems](Theorems.lean) | Valid book and a command | Matching exhausts a prefix of the opposite side at the makers' prices, quantities are conserved, and each rejection happens exactly for its stated reason. |
| `Spec.run_append` | [Specification's theorems](Theorems.lean) | First part of a whole number of records | Two runs on the parts give the book and the events of one run. |
| `run_eq` | [Refinement](Refinement.lean) | `Inv b`, a stream of fewer than 2^64 − 6 words, and a next id plus the number of records of at most 2^64 − 1 | `run` keeps `Inv`, `toSpec` of its book is the book of `Spec.run`, and its event words are `Spec.encodeAll` of the events of `Spec.run`.  `step_eq` states the same of one step. |
| `top_eq`, `init_inv`, `toSpec_init` | [Step's proof](RefineStep.lean) | `Inv b` for `top_eq` | `top` gives `Spec.top`, and the empty book satisfies `Inv` and reads as `Spec.empty`. |
| `Refinement.run_append` | [Stream theorems](RefineStream.lean) | First part of a whole number of records | On any book, `run` in two parts gives the book and the event words of one run. |
| `compiled.run.trapFree`, `compiled.top.trapFree`, `compiled.bytes` | [Compilation](Verified.lean) | Allocator invariant, a memory cap of at most 65,535 pages, represented arguments, and room for the generated bound | Entries 13 and 8 return `run` and `top` of their arguments without a trap, and the module's bytes decode to the module. |
| `compiled.run.native`, `compiled.top.native` | [Compilation](Verified.lean) | C global environment that holds the translation's globals, memory, and functions, and the premises of the entry's theorem | C translation's `run` and `top` compute the functions as the entries' theorems state. |
| `run_call` | [Call theorems](VerifiedCall.lean) | Ready store, `Inv b`, the size and next-id bounds of `run_eq`, the book's arrays owned and apart from each other and from the borrowed stream, and room for `compiled.run.bound` | Entry 13 consumes the arrays and returns without a trap a book that satisfies `Inv`, whose `toSpec` is the book of `Spec.run`, and the words `Spec.encodeAll` of its events, and leaves a ready store in which the stream stays borrowed and `top` rises by at most the bound. |
| `top_call`, `top_callSpec` | [Call theorems](VerifiedCall.lean) | Ready store, `Inv b`, the book's arrays borrowed, and room for `compiled.top.bound` | Entry 8 returns without a trap the four words of `Spec.top`, and every borrowed array stays borrowed. |
| `orderbook_module` | [Call theorems](VerifiedCall.lean) | None | Module's bytes decode to the module, whose exports `run` and `top` are entries 13 and 8. |
| `step_out_size`, `step_sizes` | [Program's counts](ProgramCounts.lean) | None | On any book, a record adds at most 5,122 events and keeps the sizes of the seven arrays. |
| `run_bound_le`, `compiled_run_bound`, `runBoundOf_74` | [Allocation bound](Bound.lean) | `Inv b`, the size and next-id bounds of `run_eq`, a stream of at most `k` records, and the equations that `verified_compile` generates for `run.bound` and for the costs of `run`, `stepArrays`, `submitArrays`, `fillArrays`, and `emit` | Generated bound of `run` is at most `runBoundOf k` = 393,464 + 3,147,280 `k` + 458,976 `k` (`k` − 1) bytes, and `runBoundOf 74` is 2,712,680,536. |
| `run_bound_le_sized`, `compiled_run_bound_sized`, `runBound_74` | [Allocation bound](Bound.lean), [charges](ProcessCharges.lean) | Equations of `run_bound_le`, seven arrays of the program's sizes on any book, and at most `k` records | Generated bound of `run` is at most `runBoundSized k`, 3,383,146,584 bytes for 74 records, for `Verified.compiled` and for the process's compilation. |
| `process_output` | [Native process's correctness](ProcessCorrect.lean) | StreamFold's `StreamHost`, an empty output history, and fewer than 2^64 − 1 records in the input's whole words | Some execution of the native process reads the whole input, writes `expectedOutput` of it, and returns `expectedStatus` of it. |
| `implements`, `run_initial` | [Module's refinement](ProcessProof.lean) | Talos host that meets `hostSpec`, and a run that does not exhaust its fuel | Every such run of the compiled `_start` matches a run of the native process, including runs that stop at an I/O error, a host trap, or a rejected exit. |
| `initial_terminates` | [Compiled process's correctness](ProcessCompiledCorrect.lean) | `StreamHost`, a host that meets `hostSpec` and accepts the statuses 0 and 28, empty histories, and fewer than 2^64 − 1 records in the input's whole words | From the module's initial store, `_start` exits after writing exactly `expectedOutput` of the input, with status `expectedStatus` of it, at every fuel above a bound. |
| `terminates_bytes`, `bytes` | [Compiled process's correctness](ProcessCompiledCorrect.lean), [module's refinement](ProcessProof.lean) | None | One byte sequence encodes and decodes the module and is a valid binary, and the module satisfies `initial_terminates` and `implements`. |

No theorem of the order book uses an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, as the `#print axioms` lines at the ends of the modules report.  `run_call` starts from `compiled.run.trapFree` rather than from `Verified.Call`, because `Verified.Call` admits only arguments that move no object, while `run` consumes the book's arrays.  `run_call` and `top_call` take room for the bounds that the compiler generates, so they hold for whatever bound the compiler states.

## The allocation bound

`compiled.run.bound`, which [the manual's section on bounds](../../docs/verified-manual.md#bounds-and-total-execution) defines, counts the bytes by which `top` can rise during a call, with no reuse of freed blocks.  For this program it charges the credits of the seven book arrays for the call, and at each record it charges them again with the credit of the event array, at 16 bytes for each word and length word: 393,408 bytes for the book's arrays and 16 bytes for the event array's length word and for each event word so far.  A record whose remainder is cancelled pays the event array's credit once more, and every pushed word costs 80 bytes, so a trade's event costs 560 bytes.  The charge at each record follows from a rule of [the internals guide](../../Verified/README.md): the value of a loop whose state is a pair is unpaid, so the book that `stepArrays` returns from the matching loop is unpaid, and the next call of `stepArrays` pays the credits of its paid parameters.  The bound therefore grows with the number of records times the number of event words, while the module's memory stays near the arrays that it holds.

| Stream | Records | Event words | `compiled.run.bound` in bytes | Module's memory after the call in bytes |
|---|---|---|---|---|
| Sample 1 of [the samples](Samples.lean), from the empty book | 3 | 42 | 1,578,120 | 1,048,576 |
| Market sell that trades with 4,096 makers, from a book of 4,096 bids | 1 | 28,686 | 3,540,648 | 1,048,576 |
| `matching-fuel-sell` of [the edge streams](../../tests/TestSupport/OrderBook/Edges.lean), the 4,096 bids and the sell, from the empty book | 4,097 | 57,358 | 2,557,511,336 | 1,638,400 |

The bounds are values of a term that `simp` obtains from `compiled.run.bound` with the `bound_eq` and `cost_eq` equations that `verified_compile` generates, evaluated as compiled Lean code.  Lean's interpreter evaluates the definition of the bound by interpreting the program's syntax and does not finish long streams, and on the streams that it finished, the two values agree.  The Wasmtime host measured the memory in its session mode, 1,048,576 bytes before each call.  The third row's bound lies below 4,294,901,760 bytes, the room that the largest memory cap gives, but a stream with more records or more events can exceed that room.  A host then runs the stream in parts, each in a call whose bound fits the memory cap, and `Refinement.run_append` with `Spec.run_append` states that the parts give the book and the events of one run.  `run_bound_le` of [the closed form](Bound.lean) states that the generated bound of a call on at most `k` records from a book that satisfies `Inv` is at most `runBoundOf k`, which counts 4,098 events at every record, so a part of at most 74 records, the most that one read of the process passes to `run`, has a bound of at most 2,712,680,536 bytes.

## The WASI process

[The process](Process.lean) runs the book over stdin and stdout.  It reads command records as little-endian 64-bit words in reads of at most 4,096 bytes, passes the whole records of the carry and each read to one call of `Program.run`, writes the event words in the same form, and keeps the bytes of a partial record in the state.  At EOF it runs the whole words of the carry as one short record, which the book rejects as malformed, and stops with status 28 when bytes that fill no word remain and with status 0 otherwise.  `process_output` states the native process's result under [StreamFold's host assumptions](../StreamFold/StreamHost.lean), and [the native executable](ProcessNative.lean) runs it on the operating system's stdin and stdout.

`verified_compile_wasi`, which [the WASI guide](../../docs/wasi.md) describes, compiles the program's functions from `emit` to `run` and the process's own functions into a command module of 38,627 bytes, in about 5 minutes, and [the module's refinement](ProcessProof.lean) relates its `_start` to the native process.  `initial_terminates` adds termination and the exact output and status, from `compiled_process_total_run` with the control rank of [the typed termination](ProcessTermination.lean) and the charges of [the charges module](ProcessCharges.lean).  A state's copy costs at most `copyLimit`, 17,179,317 bytes: the book's arrays, 197,040 bytes, a carry below 56 bytes, and an output of at most the event bytes of 74 records at `Spec.capacity + 2` events each, which the invariant `Future` bounds.  A step costs at most `stepCharge R = copyLimit + R + 21,435,213` bytes, where `R` bounds `run`'s generated bound on a batch of at most 518 words from any book whose arrays have the program's sizes.  [The closed form](Bound.lean) gives `R = runBoundSized 74 = 3,383,146,584`, so a run needs 3,456,119,748 bytes above the literal pool, which `initial_room` decides, and `initial_terminates` has the premise of `process_output`, fewer than 2^64 − 1 records.

The WASI compiler's resource rules bound each effect body for every reply that the host may give, so the charge of a read step covers a batch of any 518 words, which need not lie in the input, and cannot depend on the input's records.  `run_bound_le` needs the invariant and room for the next ids of the batch, which a reached book has only when the input leaves room for 74 more records, so the charge uses `run_bound_le_sized`, which needs only the arrays' sizes.  [The program's counts](ProgramCounts.lean) supply its two facts on every book: a record adds at most 5,122 events, the accepted event, one event for each of matching's 5,120 iterations, and a final cancellation (`Program.step_out_size`), and every step keeps the sizes of the seven arrays (`Program.step_sizes`).  The record at index `i` of a batch, counting from 0, then charges at most 3,835,408 + 1,147,328 `i` bytes, against 3,147,280 + 917,952 `i` under the invariant's 4,098 events.

The effect bodies destructure the state's 13 fields, and each level of the destructured environment holds the previous level twice.  The elaborator's conversion of a call's arguments to the state then unfolds a tree exponential in that depth, and its evaluation of `Prog.flags` walks the bodies of every earlier function, so the charges read the program's flags from `flags_toList`, which the kernel decides, and evaluate the environment with the simproc `envGetOfIndex`, which `simp` applies once to each shared subterm.  Running sum's proofs need neither, since its state has 7 fields and its program is smaller.

## Limits of the theorems

The call theorems state the module's behavior on a book that satisfies `Inv`, which the empty book satisfies and `run` keeps, so the arrays that one call returns satisfy the invariant that the next call requires.  They exclude a stream whose records, added to the next id, exceed 2^64 − 1, as in the edge streams that start near 2^64, which the module's cases still compare with native Lean.  The module statements describe execution in Talos's semantics, and the agreement of Wasmtime with Talos, the decoder's reading of the bytes, Wasmtime's instantiation, and the host's placement of the arguments are assumptions of [the trusted base](../../docs/trusted-base.md).  For the C translation, `compiled.run.native` and `compiled.top.native` replace these assumptions with those that the trusted base lists for C files, among them CompCert and the Lean copy of Clight.  `process_output` and `initial_terminates` take StreamFold's host assumptions and an input of fewer than 2^64 − 1 records.  The process module's theorems take a Talos host that meets `hostSpec`, which `initial_terminates` also requires to accept the statuses 0 and 28, and [the trusted base](../../docs/trusted-base.md#i-wasi-preview-1-modules) assumes the fidelity of that host model to Preview 1 and to Wasmtime.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.OrderBook.VerifiedCall Demos.OrderBook.Bound
tests/orderbook/run.sh
tests/verified/run.sh --cases orderbook
CCOMP=ccomp CLIGHTGEN=clightgen tests/native/verified.sh --module orderbook
d=build/verified/orderbook
build/tools/leanexe-wasmtime-host call build/verified/orderbook.wasm top list:i64,i64,i64,i64 \
  file-u64:$d/sample-3.after.oid.bin file-u64:$d/sample-3.after.acct.bin \
  file-u64:$d/sample-3.after.qty.bin file-u64:$d/sample-3.after.lvl.bin \
  file-u64:$d/sample-3.after.nxt.bin file-u64:$d/sample-3.after.head.bin \
  file-u64:$d/sample-3.after.tail.bin i64:7 i64:4
tests/orderbook/process.sh
build/tools/leanexe-wasmtime-host --stdin-file build/orderbook/lean/sample-01.bin \
  --stdout-file events.bin --control-file control.txt run build/orderbook-process/process.wasm
```

`tests/orderbook/run.sh` compares the program with the specification and with the Python reference on the samples, the edge streams, and random streams, as [its README](../../tests/orderbook/README.md) describes.  `tests/verified/run.sh --cases orderbook` writes `build/verified/orderbook.wasm`, validates it, and compares 196 cases between Wasmtime and native Lean from [the case generator](../../tests/TestSupport/OrderBook/Cases.lean), which writes each case's arrays as files under `build/verified/orderbook/`.  The cases run `run` on the samples, the single records, the edge streams, and random streams that SplitMix64 draws from fixed seeds, from the empty book and from the books that the first part of each stream leaves, and `top` on every book that `run` returns.  Each case of `run` requires nine retained blocks, the book's seven arrays, the event array, and the host's stream, and at most nine allocations plus one for each doubling of the event array's capacity, a count that a copy of a book array in the steps of a stream would exceed.  83 of the 98 cases of `run` reach that count exactly, and the others lie one below it.  Each case of `top` allocates nothing beyond the host's seven arrays.  The last command reads the book after sample 3 from the files that the cases write and prints `11`, `25`, `12`, and `25` on four lines: a best bid of 25 at 11 and a best ask of 25 at 12.  The native driver translates the module to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same cases.

`tests/orderbook/process.sh` tests the WASI process, as [the tests' README](../../tests/orderbook/README.md) describes: the axiom audits of the native and compiled proofs, the emission of `build/orderbook-process/process.wasm`, scripted-host runs of the native process, and the streams of `run.sh`, ends of input, interactive output, and I/O errors through the native executable and through the module in the Wasmtime host.  The last command runs the first sample through the module, writes its event words to `events.bin`, and writes `wasi-exit 0` to `control.txt`.  The driver passed every case: 94 streams through both executables, 28 ends of input, and the interactive and I/O-error cases.  The scripted-host runs, with records split across reads, short and zero-byte writes, and read and write errnos, exercise only the native process, because one run of the module in Talos on the empty input did not finish in 15 minutes.

## References

- M. D. Gould, M. A. Porter, S. Williams, M. McDonald, D. J. Fenn, and S. D. Howison, "Limit Order
  Books," *Quantitative Finance* 13(11):1709–1742, 2013,
  [doi:10.1080/14697688.2013.803148](https://doi.org/10.1080/14697688.2013.803148),
  [arXiv:1012.0349](https://arxiv.org/abs/1012.0349).  Section II defines limit and market orders
  and price-time priority.
- [Talos](https://github.com/jsmorph/talos), the WebAssembly interpreter in Lean whose semantics the
  module theorems use, at the revision that `lake-manifest.json` pins.
- WASI Preview 1, [the `wasi_snapshot_preview1`
  declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx)
  of `fd_read`, `fd_write`, and `proc_exit`, at the revision that [the WASI guide](../../docs/wasi.md)
  follows.
- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009, [doi:10.1145/1538788.1538814](https://doi.org/10.1145/1538788.1538814).
- S. Blazy and X. Leroy, "Mechanized Semantics for the Clight Subset of the C Language," *Journal
  of Automated Reasoning* 43(3):263–288, 2009,
  [doi:10.1007/s10817-009-9148-3](https://doi.org/10.1007/s10817-009-9148-3).
