# Lists: `List UInt64` on the heap

## Three functions on `List UInt64`

[The program](Program.lean) has three functions on Lean's `List UInt64`.  `listSum` folds addition
over a list, `listRange n` builds the words below `n` in increasing order with a loop that puts one
cell in front at each step, and `sumRange n` builds `listRange n`, sums it, and releases it.
`verified_compile compiled := [listSum, listRange, sumRange]` in [the verified
compilation](Compiled.lean) compiles the definitions into the 1,975-byte `exampleLists.wasm` of [the
module registry](../../tests/verified/modules.txt).  The registry names it `exampleLists`, since
`lists` names [the list fixture](../../Verified/Examples/Lists.lean) of the verified compiler.

The sum and range implementations come from [the word-list library](../../Library/Lists/README.md).
The reflector inlines the library's `range` into `listRange`.  The example retains the composition
that builds and releases a temporary list.

## Lists as chains of heap records

A list lives on the heap as a chain of records of two slots, the element and the pointer to the
rest, and the empty list is the null pointer.  `List UInt64` has a built-in `Encode` instance,
which states the record layout that the theorems use, and [the verified compiler
manual](../../docs/verified-manual.md#types) describes recursive types and their records.
`List.foldl` compiles to a loop that follows the tail pointers, a loop whose state is a list
allocates a record at each step, and `sumRange` releases the whole chain after the fold.  The
functions take or build lists, so their generated `implements` theorems allow a stop at
`unreachable`, and `compiled.f.trapFree` excludes it when `top` can rise by the function's bound,
which `compiled.listRange.bound_eq` states as a loop cost of 64 bytes at each step.

| Theorem | Statement |
|---------|-----------|
| `compiled.listSum.implements`, `compiled.listRange.implements`, `compiled.sumRange.implements` | Functions 2 to 4 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' values or stop at `unreachable`. |
| `compiled.listSum.trapFree`, `compiled.listRange.trapFree`, `compiled.sumRange.trapFree` | Functions 2 to 4 return their Lean functions' values without a trap when `top` can rise by the function's bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `exampleLists_file`, `exampleLists_file_decode` | `build/verified/exampleLists.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Lists.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Lists.Compiled Examples.Lists.compiled.module build/verified/exampleLists.wasm
build/tools/leanexe-wasmtime-host call build/verified/exampleLists.wasm listRange chain-u64 i64:4
build/tools/leanexe-wasmtime-host call-stats build/verified/exampleLists.wasm sumRange i64 i64:100
tests/verified/run.sh --cases exampleLists
tests/native/verified.sh --module exampleLists
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository README](../../README.md#commands).
The first call prints `[0, 1, 2, 3]`, which the host reads by walking the records and checking each
header, and the second prints 4950 and `stats 100 100`, the allocation and free counters.  [The
verified driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in
Wasmtime against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on
the module's translation to C, compiled with CompCert.  The cases state that the host's cells stay
allocated after `listSum`, that `listRange n` leaves its `n` cells allocated, and that `sumRange n`
allocates `n` cells and frees them all.

## Related examples

[`Words`](../Words/README.md) has the same layout for a list type that the program declares, with a
tail-recursive sum.  [`Trees`](../Trees/README.md) has records with two children.
[`SumArray`](../SumArray/README.md) folds over an array, where the elements are contiguous.  The LTG
entries [`list-cell`](../../ltg/entries/list-cell/README.md),
[`list-fold-loop`](../../ltg/entries/list-fold-loop/README.md), and
[`release-list`](../../ltg/entries/release-list/README.md) hold proof guidance for list cells,
folds over lists, and their release.

## References

- [Verified Compiler Manual: The Wasmtime host](../../docs/verified-manual.md#the-wasmtime-host).
