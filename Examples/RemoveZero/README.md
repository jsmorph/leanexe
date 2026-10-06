# Remove the first zero

## What it is

This example takes a request in English to a specification, a program, and a theorem that the
module's bytes compute the specification.  [The request](request.txt) asks for an array of at
most eight words without its first zero, with the other words in order, for the input itself when
it has no zero, and for the empty array when the input is longer.  [The specification](Spec.lean)
states that behavior with `Array.findIdx?` and `Array.eraseIdx!`.

The dialect compiles neither `Array.findIdx?`, which returns an `Option`, nor `Array.eraseIdx!`, so
[the program](Program.lean) computes the same array another way.  `firstZero` is a loop over the
first `count` words that keeps the index of the first zero, or `count` when there is none, and
`compute` builds the result by copying the words before that index and shifting the rest down by
one.  [The module definition](Module.lean) compiles both functions into a 1,742-byte
`removeZero.wasm` that exports `firstZero` and `compute`.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `firstZero_cases` | `firstZero` gives `count` when the first `count` words hold no zero, and otherwise the index of the first zero. |
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `removeZero_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`, `Classical.choice`, and
`Quot.sound`.  `compute_eq` connects the loop to `Array.findIdx?` and the build to `Array.eraseIdx!`
through the core lemmas `Array.findIdx?_eq_some_iff_getElem` and `Array.getElem_eraseIdx`.  The
theorem allows a trap, and the [increment example](../Increment/README.md) shows the total form.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.RemoveZero.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.RemoveZero.Module Examples.RemoveZero.removeZero.module build/removeZero/removeZero.wasm
build/tools/leanexe-wasmtime-host call build/removeZero/removeZero.wasm compute array-u64 \
  array-u64:7,0,9,0
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints `[7, 9, 0]`.  [The module
tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run 10 inputs in Wasmtime against
`expected`, including the empty array, arrays of zeros, a zero first and last, and nine words.

## Related examples

[`Increment`](../Increment/README.md) builds its result in the same way and has a complete-execution
theorem.  [`Updates`](../Updates/README.md) removes an element with `eraseIdxIfInBounds`, in place
when the array is owned.  The LTG entries [`index-loop`](../../ltg/entries/index-loop/README.md) and
[`array-build`](../../ltg/entries/array-build/README.md) describe the rules.

## References

- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `Array.findIdx?`
  and `Array.eraseIdx!`.
- [The manual's section on
  restrictions](../../docs/manual.md#restrictions-and-how-to-write-around-them), on writing around
  constructs the dialect lacks.
