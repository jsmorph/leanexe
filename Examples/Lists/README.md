# Lists: `List UInt64` on the heap

## Three functions on `List UInt64`

[The program](Program.lean) has three functions on Lean's `List UInt64`.  `listSum` folds addition
over a list, `listRange n` builds the words below `n` in increasing order with a loop that puts one
cell in front at each step, and `sumRange n` builds `listRange n`, sums it, and releases it.  [The
module definition](Module.lean) compiles the three into the 1,648-byte `lists.wasm`.

The sum and range implementations come from [the word-list library](../../Library/Lists/README.md).  The example retains the composition that builds and releases a temporary list.

## Lists as chains of heap records

A list lives on the heap as a chain of records of two slots, the element and the pointer to the
rest, and the empty list is the null pointer.  `List.foldl` compiles to a loop that follows the tail
pointers, a loop whose state is a list allocates a record at each step, and `sumRange` releases the
whole chain at the end with `Stmt.releaseNode_spec`.  The host's counters show the release:
`sumRange 100` makes 100 allocations and 100 frees.

| Theorem | Statement |
|---------|-----------|
| `listSum_implements` | Function 2 of `lists.module` implements `listSum`: with the list's records in memory, a call returns the sum or stops at `unreachable`. |
| `listRange_implements` | Function 3 implements `listRange`: a call returns a chain of records, owned by the caller, that represents `listRange n`, or stops at `unreachable`. |
| `sumRange_implements` | Function 4 implements `sumRange`. |
| `lists_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements all three functions. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  `List UInt64` has a built-in `Encode` instance, which states
the record layout that the theorems use.  [The LeanExe compiler
manual](../../docs/leanexe-manual.md#records-and-user-types) describes recursive types and their
records.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Lists.Verify
mkdir -p build/lists
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Lists.Module Examples.Lists.lists.module build/lists/lists.wasm
build/tools/leanexe-wasmtime-host call build/lists/lists.wasm listRange chain-u64 i64:4
build/tools/leanexe-wasmtime-host call-stats build/lists/lists.wasm sumRange i64 i64:100
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The first call prints `[0, 1, 2, 3]`, which the
host reads by walking the records and checking each header, and the second prints 4950 and `stats
100 100`.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 55 cases of
[`Cases.lean`](Cases.lean) with native Lean, and checks the counters of `sumRange` for five lengths.

## The verified compiler's module

`verified_compile compiled := [listSum, listRange, sumRange]` in [the verified
compilation](Compiled.lean) compiles the three definitions, in the order of the LeanExe module, into
the 1,975-byte `exampleLists.wasm` of [the module registry](../../tests/verified/modules.txt).  The
registry names it `exampleLists`, since `lists` names [the list
fixture](../../Verified/Examples/Lists.lean) of the verified compiler.  The host passes and reads
the same chains of records for both modules, and the reflector inlines the library's `range` into
`listRange`.  The functions take or build lists, so their generated `implements` theorems allow a
stop at `unreachable`, and `compiled.f.trapFree` excludes it when `top` can rise by the function's
bound, which `compiled.listRange.bound_eq` states as a loop cost of 64 bytes at each step.

| Theorem | Statement |
|---------|-----------|
| `compiled.listSum.implements`, `compiled.listRange.implements`, `compiled.sumRange.implements` | Functions 2 to 4 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' values or stop at `unreachable`. |
| `compiled.listSum.trapFree`, `compiled.listRange.trapFree`, `compiled.sumRange.trapFree` | The same calls return without a trap when `top` can rise by the function's bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements all three functions. |
| `exampleLists_file`, `exampleLists_file_decode` | `build/verified/exampleLists.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

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

The first call prints `[0, 1, 2, 3]`, and the second prints 4950 and `stats 100 100`, as the LeanExe
module's calls do.  [The verified driver](../../tests/verified/run.sh) runs the inputs of
[`Cases.lean`](Cases.lean) in Wasmtime against native Lean, and [the native
driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled with
CompCert.  The cases state that the host's cells stay allocated after `listSum`, that `listRange n`
leaves its `n` cells allocated, and that `sumRange n` allocates `n` cells and frees them all.

## Related examples

[`Words`](../Words/README.md) has the same layout for a list type that the program declares, with a
tail-recursive sum.  [`Trees`](../Trees/README.md) has records with two children.
[`SumArray`](../SumArray/README.md) folds over an array, where the elements are contiguous.  The LTG
entries [`list-cell`](../../ltg/entries/list-cell/README.md),
[`list-fold-loop`](../../ltg/entries/list-fold-loop/README.md), and
[`release-list`](../../ltg/entries/release-list/README.md) describe the rules.

## References

- [LeanExe Compiler Manual: The Wasmtime host](../../docs/leanexe-manual.md#the-wasmtime-host).
