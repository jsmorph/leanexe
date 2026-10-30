# Folds: sum, product, and exclusive or

## Request and programs

This example computes three folds of an array of words: the wrapping sum, the wrapping product, and
the bitwise exclusive or.  [The request](request.txt) asks for the three folds over an array of any
length, with scalar results.  The request defines each result as a left fold, so each program is its
own specification and the example has no `Spec.lean`.

The implementations live in [the word-reduction library](../../Library/Numerics/Reductions/Word/Program.lean).  This example retains the fold-template proofs, compilation modules, and cases.

[The programs](Program.lean) are `xs.foldl (· + ·) 0`, `xs.foldl (· * ·) 1`, and `xs.foldl (· ^^^ ·)
0`.  The compiler translates each to the fold template: an assignment of the initial value to an
accumulator, then a loop that loads each element and applies the operation.  [The module
definitions](Module.lean) compile `sumArray` alone into `sumArray.wasm`, and `productArray` and
`xorArray` into a 1,534-byte `folds.wasm` that exports both.

## One fold rule for three programs

| Theorem | Statement |
|---------|-----------|
| `Func.foldl_implements` | A function whose body is the fold template with any operation other than division and remainder computes `xs.foldl op.apply init`. |
| `sumArray_bytes` | The bytes of `sumArray.module` decode to a module whose export implements `sumArray`. |
| `folds_bytes` | The bytes of `folds.module` decode to a module whose functions 2 and 3 implement `productArray` and `xorArray`. |

`Func.foldl_implements` is in [the fold rule](../../LeanExe/IR/Fold.lean), and each program's
theorem applies it with its operation and initial value.  The theorems are in [the
proofs](Verify.lean).  They use only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.SumArray.Verify
mkdir -p build/folds
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumArray.Module Examples.SumArray.folds.module build/folds/folds.wasm
build/tools/leanexe-wasmtime-host call build/folds/folds.wasm productArray i64 array-u64:2,3,7
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints 42, the product of 2, 3, and 7.
[The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run 35 arrays in
Wasmtime against native Lean for each export, including the empty array and words near 2^64.

## The verified compiler's modules

[The verified compilation](Compiled.lean) divides the three folds as the LeanExe modules do:
`verified_compile compiledSum := [sumArray]` writes the 1,503-byte `sumArray.wasm`, and
`verified_compile compiledFolds := [productArray, xorArray]` the 1,666-byte `folds.wasm`, both of
[the module registry](../../tests/verified/modules.txt).  The folds read their borrowed array and
allocate nothing, so each generated `implements` theorem states that its function returns the fold
without a trap, and the generated `native` theorem states the same of its C function.  [The
library's module](../../Library/Numerics/Reductions/Word/Compiled.lean) compiles the same three
definitions in one module, `libwordreductions`.

| Theorem | Statement |
|---------|-----------|
| `compiledSum.sumArray.implements` | Function 2 of `compiledSum.module`, called with a borrowed array from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `sumArray xs` without a trap. |
| `compiledFolds.productArray.implements`, `compiledFolds.xorArray.implements` | Functions 2 and 3 of `compiledFolds.module` return `productArray xs` and `xorArray xs` in the same way. |
| `compiledSum.bytes`, `compiledFolds.bytes` | `encode` succeeds on each module, its bytes decode to the module, and the module implements its functions. |
| `sumArray_file`, `sumArray_file_decode`, `folds_file`, `folds_file_decode` | `build/verified/sumArray.wasm` and `build/verified/folds.wasm` hold the modules' encodings and decode to the modules, as [the file module of `sumArray`](FileSum.lean) and [that of `folds`](FileFolds.lean) state. |

```sh
tools/leanrun --timeout 60m lake build Examples.SumArray.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumArray.Compiled Examples.SumArray.compiledFolds.module build/verified/folds.wasm
build/tools/leanexe-wasmtime-host call build/verified/folds.wasm productArray i64 array-u64:2,3,7
tests/verified/run.sh --cases sumArray
tests/verified/run.sh --cases folds
tests/native/verified.sh --module folds
```

The call prints 42, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the arrays of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean for each export, and [the native driver](../../tests/native/verified.sh) runs
them on the modules' translations to C, compiled with CompCert.  The cases state one block that
stays allocated, the input array.

## Related examples

[`SumSquares`](../../Library/Numerics/Statistics/SumSquares/README.md) and [`Mean`](../../Library/Numerics/Statistics/Mean/README.md) fold over arrays of floats.
[`PairSum`](../PairSum/README.md) folds over a temporary array, and [`Lists`](../Lists/README.md)
folds over a list.  The LTG entry [`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md)
describes the rule.

## References

- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
- [LeanExe Compiler Manual: Folds](../../docs/leanexe-manual.md#folds).
