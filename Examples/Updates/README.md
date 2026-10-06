# Updates: chains of array updates

## What it is

[The program](Program.lean) has four functions that update arrays of words.  `pushTwo` pushes two
words, `setTwice` sets one element and then another from the old value of the first, and
`insertErase` inserts a word and then removes one.  `pushCopy` returns `xs` with a word pushed
together with `xs` itself, so the push must copy.  [The module definition](Module.lean) compiles the
four into the 2,714-byte `updates.wasm`.

## What it shows

An update of an owned array at its last use writes the array in place, and an update may apply to
the result of another update, as in `(xs.push a).push b`, so the intermediate array never exists as
a separate copy.  A push that runs out of room moves the array to a block of twice the capacity
first.  When the code uses the array again, as `pushCopy` does, the compiler copies it through the
copying template, and `pushCopy_implements` proves that case.  The in-place templates that the other
three functions use have rule theorems, which [`Clob`](../Clob/README.md) applies, and this example
tests the three functions by execution only.

| Theorem | Statement |
|---------|-----------|
| `pushCopy_implements` | Function 5 of `updates.module` implements `pushCopy` on an array that the call consumes: a call returns the pair `(xs.push v, xs)`, a new array and the moved input, or stops at `unreachable`. |
| `updates_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `pushCopy`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The proof loads the size with `Stmt.arraySize_spec` and
proves the copy with `Stmt.pushBuild_spec`, the rule of the push's build statement.  [The manual's
section on arrays](../../docs/manual.md#arrays) lists the update operations and when each one
copies.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Updates.Verify
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

## Related examples

[`Clob`](../Clob/README.md) proves functions that update their arrays in place, with `set!`,
`insertIdx!`, `eraseIdxIfInBounds`, and `push`.  [`SumCount`](../SumCount/README.md) returns a new
array without updating one.  The GPT-2 cache in [`Gpt`](../Gpt/README.md) grows by `++` in place.
The LTG entries [`in-place-update`](../../ltg/entries/in-place-update/README.md) and
[`array-build`](../../ltg/entries/array-build/README.md) describe the in-place and copying
templates.

## References

- [The manual's section on ownership](../../docs/manual.md#ownership), which gives the rules that
  decide whether an update is in place.
- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `push`, `set!`,
  `insertIdx!`, and `eraseIdxIfInBounds`.
