# Lists: `List UInt64` on the heap

## What it is

[The program](Program.lean) has three functions on Lean's `List UInt64`.  `listSum` folds addition
over a list, `listRange n` builds the words below `n` in increasing order with a loop that puts one
cell in front at each step, and `sumRange n` builds `listRange n`, sums it, and releases it.  [The
module definition](Module.lean) compiles the three into the 1,648-byte `lists.wasm`.

## What it shows

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
the record layout that the theorems use.  [The manual](../../docs/manual.md#records-and-user-types)
describes recursive types and their records.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Lists.Verify
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

## Related examples

[`Words`](../Words/README.md) has the same layout for a list type that the program declares, with a
tail-recursive sum.  [`Trees`](../Trees/README.md) has records with two children.
[`SumArray`](../SumArray/README.md) folds over an array, where the elements are contiguous.  The LTG
entries [`list-cell`](../../ltg/entries/list-cell/README.md),
[`list-fold-loop`](../../ltg/entries/list-fold-loop/README.md), and
[`release-list`](../../ltg/entries/release-list/README.md) describe the rules.

## References

- [The manual's section on records and user types](../../docs/manual.md#records-and-user-types).
- [The manual's section on the Wasmtime host](../../docs/manual.md#the-wasmtime-host), for the
  `chain-u64` argument and result kinds.
