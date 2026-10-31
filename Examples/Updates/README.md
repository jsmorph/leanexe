# Updates: chains of array updates

## Four functions that update arrays

[The program](Program.lean) has four functions that update arrays of words.  `pushTwo` pushes two
words, `setTwice` sets one element and then another from the old value of the first, and
`insertErase` inserts a word and then removes one.  `pushCopy` returns `xs` with a word pushed
together with `xs` itself, so the push must copy.
`verified_compile compiled := [pushTwo, setTwice, insertErase, pushCopy]` in [the verified
compilation](Compiled.lean) compiles them, in the order of the program, into the 3,185-byte
`exampleUpdates.wasm` of [the module registry](../../tests/verified/modules.txt).  The registry
names it `exampleUpdates`, since `updates` names [the update
fixture](../../Verified/Examples/Updates.lean) of the verified compiler.

## In-place updates and the copies in `setTwice` and `pushCopy`

The verified compiler takes the array of `pushTwo`, `insertErase`, and `pushCopy` as an owned
argument, of type `Moved (Array UInt64)` in the theorems, and it borrows the array of `setTwice`,
which reads the array after the first update and therefore copies it at that update.  An owned
array that an update, a push, an insertion, or a removal uses for the last time changes in its own
block, so each update in the chains of `pushTwo` and `insertErase` changes the array that the
previous one returned, and a push or an insertion that finds no room moves the array to a block of
at least twice its capacity.  The push of `pushCopy` copies `xs` once into a block with room, since
the result holds `xs` as well.  [The verified compiler manual's section on
ownership](../../docs/verified-manual.md#ownership) states when an update changes an array in place
and when it copies.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, for each function `f` | Functions 2 to 5 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' arrays, owned by the caller, or stop at `unreachable`. |
| `compiled.f.trapFree` | Calls of these functions return without a trap when `top` can rise by the function's allocation bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `exampleUpdates_file`, `exampleUpdates_file_decode` | `build/verified/exampleUpdates.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Updates.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Updates.Compiled Examples.Updates.compiled.module build/verified/exampleUpdates.wasm
build/tools/leanexe-wasmtime-host call build/verified/exampleUpdates.wasm pushTwo array-u64 \
  array-u64:1,2 i64:3 i64:4
build/tools/leanexe-wasmtime-host call build/verified/exampleUpdates.wasm insertErase array-u64 \
  array-u64:1,2,3 i64:1 i64:0 i64:9
tests/verified/run.sh --cases exampleUpdates
tests/native/verified.sh --module exampleUpdates
```

The commands build the module and its theorems, write the module, call it in the Wasmtime host, and
run the drivers, with the setup of [the repository README](../../README.md#commands).  The first
call prints `[1, 2, 3, 4]`.  The second inserts 9 at position 1 and then removes position 0, and
prints `[9, 2, 3]`.

[The verified compiler's cases](../../Verified/Examples/Cases.lean) take the arguments `pushArgs`
and `updateArgs` of [`Cases.lean`](Cases.lean), with positions inside and past the end of each
array, and [the verified driver](../../tests/verified/run.sh) compares the results in Wasmtime with
native Lean.  [The native driver](../../tests/native/verified.sh) runs the same cases on the
module's translation to C, compiled with CompCert.  The cases state one block left allocated by
`pushTwo` and `insertErase`, which consume the host's array, and two by `setTwice` and `pushCopy`,
with at most three allocations for `pushTwo`, whose pushes onto an empty array grow it twice, and at
most two for the others.  The full run of the verified driver also checks the file module against
the written file and requires both file theorems to report only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Related examples

[`Clob`](../../Demos/Clob/README.md) proves functions that update their arrays in place, with
`set!`, `insertIdx!`, `eraseIdxIfInBounds`, and `push`.  [`SumCount`](../SumCount/README.md) returns
a new array without updating one.  The GPT-2 cache in [`Gpt`](../../Demos/Gpt/README.md) grows by
`++` in place.

## References

- [Verified Compiler Manual: Ownership](../../docs/verified-manual.md#ownership).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
