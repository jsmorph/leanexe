# Clob: an order book

## What it is

[The program](Program.lean) is the bid side of a central limit order book, held as two arrays of
words: the prices in descending order and the size at each price.  `addBid` adds size at a price, to
an existing level or to a new level at its sorted position, `cancelBid` reduces or removes a level,
and `applyCommand` dispatches on a command kind.  `runCommands` applies a stream of commands, three
words each, and `runOut` also records the best bid after each command.  `marketBuy` fills a quantity
against ask levels, and `depth` totals the size at or above a price.  [The module
definition](Module.lean) compiles the fifteen functions into the 4,957-byte `clob.wasm`.

## What it shows

The CLOB was the first program of this branch, built in increments that each reached bytes and a
theorem, and it uses most of the array rules.  `fillLevel`, `insertLevel`, `setLevel`, and
`removeLevel` update arrays with `set!`, `insertIdx!`, and `eraseIdxIfInBounds`, in place when the
array is owned and at its last use.  `addBid` and `cancelBid` call those functions with consumed
arguments, typed `Moved (Array UInt64)` in their theorems, and `stepCommand` pushes onto an output
array in place.  `fillKeep` passes an array that it also returns, so the compiler copies it before
the call, and `fillTwice` passes the result of one call to the next.  `Live`, the invariant of a
body that calls functions and releases temporaries, carries the proofs of the composite functions.

| Theorem | Statement |
|---------|-----------|
| `marketBuy_implements` … `fillKeep_implements` | Each of functions 2 to 16 of `clob.module` implements its Lean function, with consumed arrays typed `Moved`. |
| `clob_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all fifteen functions. |
| `runCommands_append` | Running a command stream in two chunks, the first of whole commands, gives the book of running it at once. |
| `runOut_book` | The book that `runOut` leaves is the book of `runCommands`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The last two theorems concern the Lean program alone, and
since `clob_bytes` states that the module computes `runCommands` and `runOut`, they hold for its
results.  [The manual's section on ownership](../../docs/manual.md#ownership) explains consumed and
borrowed arguments, using `fillTuple` from this example.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Clob.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Clob.Module Examples.Clob.clob.module build/clob/clob.wasm
build/tools/leanexe-wasmtime-host call build/clob/clob.wasm addBid list:array-u64,array-u64 \
  array-u64:105,101 array-u64:4,6 i64:103 i64:5
build/tools/leanexe-wasmtime-host call build/clob/clob.wasm runCommands \
  list:array-u64,array-u64 array-u64: array-u64: array-u64:0,100,5,0,102,3,1,100,2
uv run tests/modules/chunks.py
```

The commands build the proofs, write the module, call it in the Wasmtime host, and run the chunk
test, with the setup of [the repository README](../../README.md#commands).  The first call adds 5 at
103 to a book of two levels and prints the prices `[105, 103, 101]` and the sizes `[4, 5, 6]`.  The
second starts from an empty book, adds 5 at 100 and 3 at 102, cancels 2 at 100, and prints `[102,
100]` and `[3, 3]`.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 3,990 cases of
[`Cases.lean`](Cases.lean) with native Lean and checks the allocation and free counts of the
functions that consume arrays, and [`tests/modules/chunks.py`](../../tests/modules/chunks.py) runs
one command stream whole, in chunks, and one command at a time, and checks that the books agree.

## Related examples

[`Updates`](../Updates/README.md) tests chains of in-place updates.
[`SumCount`](../SumCount/README.md) and [`PairSum`](../PairSum/README.md) are the smallest programs
with arrays.  The GPT-2 functions in [`Gpt`](../Gpt/README.md) use `Live` on a larger scale.  The
LTG entries [`in-place-update`](../../ltg/entries/in-place-update/README.md),
[`array-build`](../../ltg/entries/array-build/README.md),
[`index-loop`](../../ltg/entries/index-loop/README.md),
[`function-call`](../../ltg/entries/function-call/README.md), and
[`release-temporary`](../../ltg/entries/release-temporary/README.md) cite this example's proofs as
worked examples.

## References

- M. D. Gould, M. A. Porter, S. Williams, M. McDonald, D. J. Fenn, and S. D. Howison, "Limit Order
  Books," *Quantitative Finance* 13(11):1709–1742, 2013,
  [arXiv:1012.0349](https://arxiv.org/abs/1012.0349).
- [The design record](../../docs/design.md#decisions), which records the choice of the CLOB as the
  first program.
