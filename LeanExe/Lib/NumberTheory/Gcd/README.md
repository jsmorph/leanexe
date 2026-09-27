# Euclidean GCD

`gcd` computes the greatest common divisor of two unsigned 64-bit integers using Euclid's remainder loop.  It accepts zero inputs, including `gcd 0 0 = 0`.

[LeanExe](../../../../README.md) compiles the Lean function and its callers to WebAssembly (WASM).  The [command-line examples](../../../../libraries/README.md#setup-and-commands) run that WASM in Wasmtime.  The [binary GCD implementation](../BinaryGcd/README.md) computes the same result using shifts and subtraction.

## Verification status

Lean checks the source types.  Passing execution tests establish agreement between WASM, native Lean, and mathematical references on the tested inputs.  Formal correctness and termination proofs for this source function, its generated WASM, and its clients remain deferred.

## Use

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  From the repository root, these commands build the source and compiler, compile the imported functions, and run the examples:

```sh
tools/seminum gcd 48 18
# 6
tools/seminum fraction 48 18
# 8/3
tools/seminum ratio 2 1,3,2 2,2
# 5/2
```

Arguments are decimal integers from zero through `18446744073709551615`.  Fraction reduction requires a positive denominator.  Invalid input exits with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.NumberTheory.Gcd.Basic

def LeanExe.Examples.commonFactor (a b : UInt64) : UInt64 :=
  LeanExe.Lib.NumberTheory.gcd a b
```

The API is `gcd (a b : UInt64) : UInt64`.  The intended result is `Nat.gcd a.toNat b.toNat`, represented as a word.  The [source](Basic.lean) uses one remainder per iteration and constant working storage.  The [client programs](../../../Examples/Seminum.lean) use it to reduce a fraction and a ratio of polynomial values.

## Tests and report

From the repository root, `node test/seminum.js` compares WASM and native Lean with an arbitrary-precision integer GCD reference.  The native test also compares each GCD result with Lean's `Nat.gcd`.  Inputs include zero, maximum words, powers of two, consecutive large Fibonacci numbers, and generated full-width pairs.  Client cases check fraction reduction, polynomial ratios, and rejection of a zero denominator.  CLI tests check results and invalid-input diagnostics.

The [test source](../../../../test/seminum.js) and [native reference driver](../../../../test/SeminumNative.lean) define the cases.  The [technical report](report.pdf) explains the recurrence and clients and includes the executable source.  `tools/seminum reports` rebuilds the PDF from [its LaTeX source](report.tex).

## Annotated references

- [Paul E. Black, “Euclid's algorithm,” NIST DADS](https://xlinux.nist.gov/dads/HTML/euclidalgo.html): supplies the remainder recurrence used here.  This component extends the entry's positive-input description with explicit zero-input behavior and a `UInt64` API.
