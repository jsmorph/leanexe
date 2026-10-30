# Updates: chains of array updates

## Four functions that update arrays

[The program](Program.lean) has four functions that update arrays of words.  `pushTwo` pushes two
words, `setTwice` sets one element and then another from the old value of the first, and
`insertErase` inserts a word and then removes one.  `pushCopy` returns `xs` with a word pushed
together with `xs` itself, so the push must copy.  [The module definition](Module.lean) compiles the
four into the 2,714-byte `updates.wasm`.

## In-place updates and the copy in `pushCopy`

An update of an owned array at its last use writes the array in place, and an update may apply to
the result of another update, as in `(xs.push a).push b`, so the intermediate array never exists as
a separate copy.  A push that runs out of room moves the array to a block of twice the capacity
first.  When the code uses the array again, as `pushCopy` does, the compiler copies it through the
copying template, and `pushCopy_implements` proves that case.  The in-place templates that the other
three functions use have rule theorems, which [`Clob`](../../Demos/Clob/README.md) applies, and this example
tests the three functions by execution only.

| Theorem | Statement |
|---------|-----------|
| `pushCopy_implements` | Function 5 of `updates.module` implements `pushCopy` on an array that the call consumes: a call returns the pair `(xs.push v, xs)`, a new array and the moved input, or stops at `unreachable`. |
| `updates_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `pushCopy`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The proof loads the size with `Stmt.arraySize_spec` and
proves the copy with `Stmt.pushBuild_spec`, the rule of the push's build statement.  [The LeanExe
compiler manual's section on arrays](../../docs/leanexe-manual.md#arrays) lists the update
operations and when each one copies.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Updates.Verify
mkdir -p build/updates
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Updates.Module Examples.Updates.updates.module build/updates/updates.wasm
build/tools/leanexe-wasmtime-host call build/updates/updates.wasm pushTwo array-u64 \
  array-u64:1,2 i64:3 i64:4
build/tools/leanexe-wasmtime-host call build/updates/updates.wasm insertErase array-u64 \
  array-u64:1,2,3 i64:1 i64:0 i64:9
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The first call prints `[1, 2, 3, 4]`.  The
second inserts 9 at position 1 and then removes position 0, and prints `[9, 2, 3]`.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 1,400 cases of
[`Cases.lean`](Cases.lean) with native Lean, including positions past the end.

## The verified compiler's module

`verified_compile compiled := [pushTwo, setTwice, insertErase, pushCopy]` in [the verified
compilation](Compiled.lean) compiles the four definitions, in the order of the LeanExe module, into
the 3,185-byte `exampleUpdates.wasm` of [the module registry](../../tests/verified/modules.txt).
The registry names it `exampleUpdates`, since `updates` names [the update
fixture](../../Verified/Examples/Updates.lean) of the verified compiler.  The compiler takes the
array of `pushTwo`, `insertErase`, and `pushCopy` as an owned argument, `Moved`, and it borrows the
array of `setTwice`, which reads the array after the first update and therefore copies it.  The
generated `implements` theorems cover all four functions, where `updates_bytes` covers `pushCopy`
alone, and `compiled.f.trapFree` excludes the stop at `unreachable` when `top` can rise by the
function's bound.

| Theorem | Statement |
|---------|-----------|
| `compiled.pushTwo.implements` … `compiled.pushCopy.implements` | Functions 2 to 5 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, return their Lean functions' arrays, owned by the caller, or stop at `unreachable`. |
| `compiled.pushTwo.trapFree` … `compiled.pushCopy.trapFree` | The same calls return without a trap when `top` can rise by the function's bound within the memory cap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements all four functions. |
| `exampleUpdates_file`, `exampleUpdates_file_decode` | `build/verified/exampleUpdates.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

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

The calls print `[1, 2, 3, 4]` and `[9, 2, 3]`, as the LeanExe module's calls do.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state one block left allocated by
`pushTwo` and `insertErase`, which consume the host's array, and two by `setTwice` and `pushCopy`,
with at most three allocations for `pushTwo`, whose pushes onto an empty array grow it twice, and at
most two for the others.

## Related examples

[`Clob`](../../Demos/Clob/README.md) proves functions that update their arrays in place, with `set!`,
`insertIdx!`, `eraseIdxIfInBounds`, and `push`.  [`SumCount`](../SumCount/README.md) returns a new
array without updating one.  The GPT-2 cache in [`Gpt`](../../Demos/Gpt/README.md) grows by `++` in place.
The LTG entries [`in-place-update`](../../ltg/entries/in-place-update/README.md) and
[`array-build`](../../ltg/entries/array-build/README.md) describe the in-place and copying
templates.

## References

- [LeanExe Compiler Manual: Ownership](../../docs/leanexe-manual.md#ownership).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
