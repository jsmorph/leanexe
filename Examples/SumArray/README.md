# Folds: sum, product, and exclusive or

This example stands for [main's Demo
10](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-10/README.md)
and [Demo
11](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-11/README.md),
which return the wrapping product and the bitwise exclusive or of an array of at most eight words as
a one-word array, and the empty array for a longer input.  [The request](request.txt) here asks for
the three folds over an array of any length, with scalar results, and adds the sum of Iteration 3a.
Each request defines its result as a left fold, so each program is its own specification and the
example has no `Spec.lean`.

[The programs](Program.lean) are `xs.foldl (· + ·) 0`, `xs.foldl (· * ·) 1`, and `xs.foldl (· ^^^ ·)
0`.  The compiler translates each to the fold template: an assignment of the initial value to an
accumulator, then a loop that loads each element and applies the operation.  [The module
definitions](Module.lean) compile `sumArray` alone into `sumArray.wasm`, and `productArray` and
`xorArray` into a 1,534-byte `folds.wasm` that exports both.

| Theorem | Statement |
|---------|-----------|
| `Func.foldl_implements` | A function whose body is the fold template with any operation other than division and remainder computes `xs.foldl op.apply init`. |
| `sumArray_bytes` | The bytes of `sumArray.module` decode to a module whose export implements `sumArray`. |
| `folds_bytes` | The bytes of `folds.module` decode to a module whose functions 2 and 3 implement `productArray` and `xorArray`. |

`Func.foldl_implements` is in [the fold rule](../../LeanExe/IR/Fold.lean), and each program's
theorem applies it with its operation and initial value.  The theorems are in [the
proofs](Verify.lean).  They use only `propext`, `Classical.choice`, and `Quot.sound`.  Main's proofs
concerned one 1,979-byte binary each and took 572 and 676 lines.  The module tests run 35 arrays in
Wasmtime against native Lean for each export, including the empty array and words near 2^64.

```sh
tools/leanrun --timeout 60m lake build Examples.SumArray.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumArray.Module Examples.SumArray.folds.module build/folds/folds.wasm
build/tools/leanexe-wasmtime-host call build/folds/folds.wasm productArray i64 array-u64:2,3,7
```
