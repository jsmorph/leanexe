# Remove the first zero

This example is [main's Demo 12](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-12/README.md), carried to this
branch's pipeline.  [The request](request.txt) asks for an array of at most eight words without
its first zero, with the other words in order, for the input itself when it has no zero, and for
the empty array when the input is longer.  [The specification](Spec.lean)
states that behavior with `Array.findIdx?` and `Array.eraseIdx!`, as main's did.

The dialect compiles neither `Array.findIdx?`, which returns an `Option`, nor `Array.eraseIdx!`,
so [the program](Program.lean) computes the same array another way.
`firstZero` is a loop over the first `count` words that keeps the index of the first zero, or
`count` when there is none, and `compute` builds the result by copying the words before that
index and shifting the rest down by one.  [The module definition](Module.lean)
compiles both functions into a 1,742-byte `removeZero.wasm` that exports `firstZero` and `compute`.

| Theorem | Statement |
|---------|-----------|
| `firstZero_cases` | `firstZero` gives `count` when the first `count` words hold no zero, and otherwise the index of the first zero. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `removeZero_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only
`propext`, `Classical.choice`, and `Quot.sound`.  `compute_eq` connects the loop to
`Array.findIdx?` and the build to `Array.eraseIdx!` through the core lemmas
`Array.findIdx?_eq_some_iff_getElem` and `Array.getElem_eraseIdx`.  Main's theorem also stated
termination with a heap reserve.  Here the theorem allows a trap, and the [increment
example](../Increment/README.md) shows the total form.

```sh
tools/leanrun --timeout 60m lake build Examples.RemoveZero.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.RemoveZero.Module Examples.RemoveZero.removeZero.module build/removeZero/removeZero.wasm
build/tools/leanexe-wasmtime-host call build/removeZero/removeZero.wasm compute array-u64 \
  array-u64:7,0,9,0
```
