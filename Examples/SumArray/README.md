# Folds: sum, product, and exclusive or

## Request and programs

This example computes three folds of an array of words: the wrapping sum, the wrapping product, and
the bitwise exclusive or.  [The request](request.txt) asks for the three folds over an array of any
length, with scalar results.  The request defines each result as a left fold, so each program is its
own specification.

The implementations live in [the word-reduction
library](../../Library/Numerics/Reductions/Word/Program.lean), and [the programs](Program.lean) of
this example export them.  `sumArray` is `xs.foldl (· + ·) 0`, `productArray` is
`xs.foldl (· * ·) 1`, and `xorArray` is `xs.foldl (· ^^^ ·) 0`.  The command
`verified_compile compiledSum := [sumArray]` in [the verified compilation](Compiled.lean) compiles
`sumArray` alone into the 1,503-byte `sumArray.wasm`, and
`verified_compile compiledFolds := [productArray, xorArray]` compiles the other folds into the
1,666-byte `folds.wasm`, both of [the module registry](../../tests/verified/modules.txt).  [The
library's module](../../Library/Numerics/Reductions/Word/Compiled.lean) compiles the same
definitions in one module, `libwordreductions`.

## Folds without a trap

The folds read their borrowed array and allocate nothing, so each generated `implements` theorem
states that its function returns the fold without a trap.  The generated `native` theorem of each
function states the same of its C function in the module's translation.  Each program folds over
the whole array, from `start = 0` to `stop = xs.size`, the only bounds of `xs.foldl` that the
reflector accepts, as [the verified compiler manual's section on loops and
builds](../../docs/verified-manual.md#loops-and-builds) states.

| Theorem | Statement |
|---------|-----------|
| `compiledSum.sumArray.implements` | Function 2 of `compiledSum.module`, called with a borrowed array from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `sumArray xs` without a trap. |
| `compiledFolds.productArray.implements`, `compiledFolds.xorArray.implements` | Functions 2 and 3 of `compiledFolds.module` return `productArray xs` and `xorArray xs` in the same way. |
| `compiledSum.bytes`, `compiledFolds.bytes` | `encode` succeeds on each module, its bytes decode to the module, and the module implements its functions. |
| `sumArray_file`, `sumArray_file_decode`, `folds_file`, `folds_file_decode` | `build/verified/sumArray.wasm` and `build/verified/folds.wasm` hold the modules' encodings and decode to the modules, as [the file module of `sumArray`](FileSum.lean) and [that of `folds`](FileFolds.lean) state. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.SumArray.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumArray.Compiled Examples.SumArray.compiledFolds.module build/verified/folds.wasm
build/tools/leanexe-wasmtime-host call build/verified/folds.wasm productArray i64 array-u64:2,3,7
tests/verified/run.sh --cases sumArray
tests/verified/run.sh --cases folds
tests/native/verified.sh --module sumArray
tests/native/verified.sh --module folds
```

The first commands build the verified compilations and their theorems, write the module of
`productArray` and `xorArray`, and call it in the Wasmtime host, with the setup of [the repository
README](../../README.md#commands).  The call prints 42, the product of 2, 3, and 7.  [The verified
driver](../../tests/verified/run.sh) runs the arrays of [`Cases.lean`](Cases.lean), including the
empty array and words near 2^64, in Wasmtime against native Lean for each export, and [the native
driver](../../tests/native/verified.sh) runs them on the modules' translations to C, compiled with
CompCert.  The cases state one block that stays allocated, the input array.  Without `--cases`, the
verified driver also checks the file module against the written file and requires the axiom reports
of both file theorems to name only `propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`SumSquares`](../../Library/Numerics/Statistics/SumSquares/README.md) and
[`Mean`](../../Library/Numerics/Statistics/Mean/README.md) fold over arrays of floats.
[`PairSum`](../PairSum/README.md) folds over a temporary array, and [`Lists`](../Lists/README.md)
folds over a list.

## References

- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
- [Verified Compiler Manual: Loops and builds](../../docs/verified-manual.md#loops-and-builds).
