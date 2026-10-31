# Clob: an order book

## The bid side of an order book

[The program](Verified.lean) is the bid side of a central limit order book, held as two arrays of
words: the prices in descending order and the size at each price.  `addBid` adds size at a price, to
an existing level or to a new level at its sorted position, `cancelBid` reduces or removes a level,
and `applyCommand` dispatches on a command kind.  `runCommands` applies a stream of commands, three
words each, and `runOut` also records the best bid after each command.  `marketBuy` fills a quantity
against ask levels and returns the filled quantity and its cost, and `depth` totals the size at or
above a price.  The command `verified_compile compiled := [marketBuy, …, depth]` after the
definitions compiles them into `compiled.module` and states their theorems.

## In-place array updates and command streams

`fillLevel` and `setLevel` update a side with `set!`, and `insertLevel` and `removeLevel` insert and
remove a level with `LeanExe.insertAt` and `LeanExe.eraseAt`.  When such an update is the last use
of an owned array, the code changes the array in its own block, and it copies any other array
first.  `stepCommand` extends its output array with the best price and size, in place when the
array is owned and its block has room.  `fillKeep` passes the sizes to `fillLevel` and also returns
them, so the call consumes a copy, and `fillTwice` passes the array that one call returns to the
next.  [The verified compiler manual's section on
ownership](../../docs/verified-manual.md#ownership) states how the reflector chooses whether each
array parameter is owned or borrowed, and an owned parameter has type `Moved (Array UInt64)` in the
theorems.

The program keeps the definitions of the order book that the LeanExe compiler compiled, which [the
journal](../../devnotes.md#2026-10-06-the-verified-compiler) records, except in `marketBuy`,
`addBid`, `cancelBid`, `insertLevel`, and `removeLevel`.  `marketBuy` returns the filled quantity
and its cost as a pair, where the earlier program returned the array `#[filled, cost]`.  The
conditions of `addBid` and `cancelBid` compare words with `&&` and `==`, where the earlier program
tested propositions with `∧` and `=`.  `insertLevel` inserts with `LeanExe.insertAt` in place of
`insertIdx!`, so an insertion past the end of a side leaves the side unchanged where `insertIdx!`
panics, and `removeLevel` erases with `LeanExe.eraseAt`, which is the earlier program's
`eraseIdxIfInBounds`.  `findLevel` returns at most the number of prices, so `addBid`, `cancelBid`,
and the command runs give the same books in both programs, except where `addBid` inserts past the
end of a sizes array shorter than its prices array.

| Theorem | Statement |
|---------|-----------|
| `compiled.marketBuy.implements` … `compiled.depth.implements` | Each of functions 2 to 16 of `compiled.module`, called with words that represent the arguments of its Lean function, returns words that represent that function's result, or traps at `unreachable` where the function's `aborts` flag allows it. |
| `compiled.marketBuy.trapFree` … `compiled.depth.trapFree` | Each of those functions returns its result without a trap and raises `top` by at most `compiled.f.bound`.  When the function's `aborts` flag is set, the theorem requires room for that rise within the memory cap. |
| `compiled.bytes` | `encode` succeeds on `compiled.module` with bytes that decode to it, and every `implements` theorem holds. |
| `runCommands_append` | Running a command stream of fewer than 2^62 words in two chunks, the first of whole commands, gives the book of running it at once. |
| `runOut_book` | For a command stream of fewer than 2^64 words, `runOut` leaves the book of `runCommands`. |
| `clob_file`, `clob_file_decode` | `build/verified/clob.wasm`, as written, holds `encode compiled.module` and decodes to `compiled.module`. |

[The compilation](Verified.lean) holds the generated theorems and proves `runCommands_append` and
`runOut_book` from the folds of [the command lemmas](Commands.lean).  Those two concern the Lean
definitions, and since the `implements` theorems state that the module computes `runCommands` and
`runOut`, they hold for the module's results.  [The file theorems](File.lean) read the module that
`tests/verified/run.sh` writes, and without `--cases` that driver requires the axiom reports of both
to name only `propext`, `Classical.choice`, and `Quot.sound`.  The second file theorem depends on
every `implements` theorem through `compiled.bytes`, so its report covers them all.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.Clob.Verified LeanExe.Pipeline.FileBytes
tests/verified/run.sh --cases clob
tests/native/verified.sh --module clob
tools/leanrun --timeout 10m lake env lean Demos/Clob/File.lean
build/tools/leanexe-wasmtime-host call build/verified/clob.wasm addBid list:array-u64,array-u64 \
  array-u64:105,101 array-u64:4,6 i64:103 i64:5
build/tools/leanexe-wasmtime-host call build/verified/clob.wasm runCommands \
  list:array-u64,array-u64 array-u64: array-u64: array-u64:0,100,5,0,102,3,1,100,2
```

The commands build the compilation and the support of the file theorems, write and test the
module, check the file theorems, and call the module in the Wasmtime host, with the setup of [the
repository README](../../README.md#commands).  The first call adds 5 at 103 to a book of two levels
and prints the prices `[105, 103, 101]` and the sizes `[4, 5, 6]`.  The second starts from an empty
book, adds 5 at 100 and 3 at 102, cancels 2 at 100, and prints `[102, 100]` and `[3, 3]`.

`tests/verified/run.sh --cases clob` writes `build/verified/clob.wasm`, validates it with
`wasm-tools`, and compares each `clob` case of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime with native Lean.  The cases call every
function on books of up to eight levels with descending prices, on books whose sides differ in
length, and on a level of the largest size, and they pass positions inside, at, and past the end of
a side.  Their command streams hold additions, cancellations, and commands of an unknown kind at
prices near the book's, and the last stream of each book ends in a partial command, which the runs
ignore.  The command `lake env lean Demos/Clob/File.lean` checks the file theorems against the
written file and prints their axiom reports.  [The native driver](../../tests/native/verified.sh)
runs the same cases on the module's translation to C, compiled with CompCert.

## Related examples

[`Updates`](../../Examples/Updates/README.md) tests chains of in-place updates.
[`SumCount`](../../Examples/SumCount/README.md) and [`PairSum`](../../Examples/PairSum/README.md)
are the smallest programs with arrays.  [`Drone`](../Drone/README.md) has loops with tuple states
over arrays at a larger scale.

## References

- M. D. Gould, M. A. Porter, S. Williams, M. McDonald, D. J. Fenn, and S. D. Howison, "Limit Order
  Books," *Quantitative Finance* 13(11):1709–1742, 2013,
  [arXiv:1012.0349](https://arxiv.org/abs/1012.0349).
- [Design: Decisions](../../docs/design.md#decisions).
