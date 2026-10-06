# Folds: sum, product, and exclusive or

## What it is

This example computes three folds of an array of words: the wrapping sum, the wrapping product, and
the bitwise exclusive or.  [The request](request.txt) asks for the three folds over an array of any
length, with scalar results.  The request defines each result as a left fold, so each program is its
own specification and the example has no `Spec.lean`.

[The programs](Program.lean) are `xs.foldl (· + ·) 0`, `xs.foldl (· * ·) 1`, and `xs.foldl (· ^^^ ·)
0`.  The compiler translates each to the fold template: an assignment of the initial value to an
accumulator, then a loop that loads each element and applies the operation.  [The module
definitions](Module.lean) compile `sumArray` alone into `sumArray.wasm`, and `productArray` and
`xorArray` into a 1,534-byte `folds.wasm` that exports both.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `Func.foldl_implements` | A function whose body is the fold template with any operation other than division and remainder computes `xs.foldl op.apply init`. |
| `sumArray_bytes` | The bytes of `sumArray.module` decode to a module whose export implements `sumArray`. |
| `folds_bytes` | The bytes of `folds.module` decode to a module whose functions 2 and 3 implement `productArray` and `xorArray`. |

`Func.foldl_implements` is in [the fold rule](../../LeanExe/IR/Fold.lean), and each program's
theorem applies it with its operation and initial value.  The theorems are in [the
proofs](Verify.lean).  They use only `propext`, `Classical.choice`, and `Quot.sound`.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.SumArray.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumArray.Module Examples.SumArray.folds.module build/folds/folds.wasm
build/tools/leanexe-wasmtime-host call build/folds/folds.wasm productArray i64 array-u64:2,3,7
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints 42, the product of 2, 3, and 7.
[The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run 35 arrays in
Wasmtime against native Lean for each export, including the empty array and words near 2^64.

## Related examples

[`SumSquares`](../SumSquares/README.md) and [`Mean`](../Mean/README.md) fold over arrays of floats.
[`PairSum`](../PairSum/README.md) folds over a temporary array, and [`Lists`](../Lists/README.md)
folds over a list.  The LTG entry [`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md)
describes the rule.

## References

- [The Lean 4 reference on
  arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/), for `Array.foldl`.
- [The manual's section on folds](../../docs/manual.md#folds).
