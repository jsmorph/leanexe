# Order book: price-time matching for one instrument

[The program](Program.lean) is a deterministic step function over the two-sided book of one instrument.  It matches limit and market orders by price-time priority, with self-trade prevention, engine-assigned order ids, cancels, and reductions that keep priority, and it writes an event for every acceptance, rejection, trade, cancellation, and reduction.  The host sequences and authenticates commands, keeps the command log, and maps the engine's ids to client tags from the events, and recovery replays the log, which the stream theorems justify.  [The requirements](requirements.md) state the book in English, [the specification](Spec.lean) states them over lists, and [the refinement](Refinement.lean) proves that the program, which holds the book in fixed arrays, computes the specification.  `verified_compile` compiles the program into a module of 15,662 bytes and its translation to C, and [the call theorems](VerifiedCall.lean) carry the refinement to the module's exports.  [The journal's design entry](../../devnotes.md#2026-10-31-the-design-of-a-two-sided-order-book) gives the decisions and their reasons.

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
| [`tests/orderbook/`](../../tests/orderbook/README.md) | Native comparison with the specification and with a Python reference written from the requirements |
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

No theorem of the order book uses an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, as the `#print axioms` lines at the ends of the modules report.  `run_call` starts from `compiled.run.trapFree` rather than from `Verified.Call`, because `Verified.Call` admits only arguments that move no object, while `run` consumes the book's arrays.  `run_call` and `top_call` take room for the bounds that the compiler generates, so they hold for whatever bound the compiler states.

## The allocation bound

`compiled.run.bound` counts the bytes by which `top` can rise during a call, with no reuse of freed blocks.  For this program it charges, at each record, the credits of the loop state's seven book arrays and of its event array, at 16 bytes for each word and length word: 393,408 bytes for the book's arrays and 16 bytes for each event word so far.  At each trade and at each cancelled remainder it charges the event array's credit again, 16 bytes for each event word so far, and every pushed word costs 80 bytes.  The bound therefore grows with the number of records times the number of event words and with the square of the event words, while the module's memory stays near the arrays that it holds.

| Stream | Records | Event words | `compiled.run.bound` in bytes | Module's memory after the call in bytes |
|---|---|---|---|---|
| Sample 1 of [the samples](Samples.lean), from the empty book | 3 | 42 | 1,578,824 | 1,048,576 |
| Market sell that trades with 4,096 makers, from a book of 4,096 bids | 1 | 28,686 | 943,359,656 | 1,048,576 |
| `matching-fuel-sell` of [the edge streams](../../tests/TestSupport/OrderBook/Edges.lean), the 4,096 bids and the sell, from the empty book | 4,097 | 57,358 | 5,376,378,536 | 1,638,400 |

Lean's interpreter evaluated the bound of the first two rows, and the third row's bound follows from the cost equations that `verified_compile` generates and the evaluated sweep.  The Wasmtime host measured the memory in its session mode, 1,048,576 bytes before each call.  The third row's bound exceeds 4,294,901,760 bytes, the room that the largest memory cap gives, so `run_call` does not cover that stream in one call.  A host therefore runs a long stream in parts, each in a call whose bound fits the memory cap, and `Refinement.run_append` with `Spec.run_append` states that the parts give the book and the events of one run.

## Limits of the theorems

The call theorems state the module's behavior on a book that satisfies `Inv`, which the empty book satisfies and `run` keeps, so the arrays that one call returns satisfy the invariant that the next call requires.  They exclude a stream whose records, added to the next id, exceed 2^64 − 1, as in the edge streams that start near 2^64, which the module's cases still compare with native Lean.  The module statements describe execution in Talos's semantics, and the agreement of Wasmtime with Talos, the decoder's reading of the bytes, Wasmtime's instantiation, and the host's placement of the arguments are assumptions of [the trusted base](../../docs/trusted-base.md).  For the C translation, `compiled.run.native` and `compiled.top.native` replace these assumptions with those that the trusted base lists for C files, among them CompCert and the Lean copy of Clight.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.OrderBook.VerifiedCall
tests/orderbook/run.sh
tests/verified/run.sh --cases orderbook
CCOMP=ccomp CLIGHTGEN=clightgen tests/native/verified.sh --module orderbook
d=build/verified/orderbook
build/tools/leanexe-wasmtime-host call build/verified/orderbook.wasm top list:i64,i64,i64,i64 \
  file-u64:$d/sample-3.after.oid.bin file-u64:$d/sample-3.after.acct.bin \
  file-u64:$d/sample-3.after.qty.bin file-u64:$d/sample-3.after.lvl.bin \
  file-u64:$d/sample-3.after.nxt.bin file-u64:$d/sample-3.after.head.bin \
  file-u64:$d/sample-3.after.tail.bin i64:7 i64:4
```

`tests/orderbook/run.sh` compares the program with the specification and with the Python reference on the samples, the edge streams, and random streams, as [its README](../../tests/orderbook/README.md) describes.  `tests/verified/run.sh --cases orderbook` writes `build/verified/orderbook.wasm`, validates it, and compares 196 cases between Wasmtime and native Lean from [the case generator](../../tests/TestSupport/OrderBook/Cases.lean), which writes each case's arrays as files under `build/verified/orderbook/`.  The cases run `run` on the samples, the single records, the edge streams, and random streams that SplitMix64 draws from fixed seeds, from the empty book and from the books that the first part of each stream leaves, and `top` on every book that `run` returns.  Each case of `run` requires nine retained blocks, the book's seven arrays, the event array, and the host's stream, and at most nine allocations plus one for each doubling of the event array's capacity, a count that a copy of a book array in the steps of a stream would exceed.  83 of the 98 cases of `run` reach that count exactly, and the others lie one below it.  Each case of `top` allocates nothing beyond the host's seven arrays.  The last command reads the book after sample 3 from the files that the cases write and prints `11`, `25`, `12`, and `25` on four lines: a best bid of 25 at 11 and a best ask of 25 at 12.  The native driver translates the module to C, compares the Clight that `clightgen` reads back from the printed C with the translation, compiles the C with CompCert's `ccomp`, and runs the same cases.

## References

- [Order book requirements](requirements.md)
- [Order book tests](../../tests/orderbook/README.md)
- [Verified Compiler Manual: Bounds and total execution](../../docs/verified-manual.md#bounds-and-total-execution)
- [Trusted base](../../docs/trusted-base.md)
- [Talos](https://github.com/jsmorph/talos)
- [Wasmtime documentation](https://docs.wasmtime.dev/)
- [CompCert](https://compcert.org/)
