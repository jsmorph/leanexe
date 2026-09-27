# Binary GCD

`gcdBinary` computes the greatest common divisor of two unsigned 64-bit integers using shifts, comparisons, and subtraction.  It accepts zero inputs, including `gcdBinary 0 0 = 0`.

[LeanExe](../../../../README.md) compiles the Lean function and its callers to WebAssembly (WASM).  The [command-line examples](../../../../libraries/README.md#setup-and-commands) run that WASM in Wasmtime.  The [Euclidean GCD implementation](../Gcd/README.md) uses remainders.

## Verification status

Lean checks the source types.  For both GCD implementations, passing execution tests establish agreement between WASM, native Lean, and mathematical references on the tested inputs.  Formal correctness and termination proofs for this source function, its generated WASM, and its fraction client remain deferred.

## Use

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  From the repository root, these commands build and execute the WASM examples:

```sh
tools/seminum gcd-binary 48 18
# 6
tools/seminum fraction-binary 48 18
# 8/3
```

Arguments are decimal integers from zero through `18446744073709551615`.  Fraction reduction requires a positive denominator.  Invalid input exits with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.NumberTheory.BinaryGcd.Basic

def LeanExe.Examples.commonFactorBinary (a b : UInt64) : UInt64 :=
  LeanExe.Lib.NumberTheory.gcdBinary a b
```

The API is `gcdBinary (a b : UInt64) : UInt64`.  The intended result is `Nat.gcd a.toNat b.toNat`, represented as a word.  The [source](Basic.lean) handles zero before its shift loops, removes common powers of two, reduces odd operands by subtraction, and restores the common power.  It uses constant working storage.  The [fraction client](../../../Examples/Seminum.lean) shares result handling with the Euclidean client.

## Tests and report

From the repository root, `node test/seminum.js` compares both GCD implementations on the same inputs.  WASM and native Lean results agree with an arbitrary-precision integer GCD reference, and the native test also checks Lean's `Nat.gcd`.  Inputs include zero, maximum words, powers of two, consecutive large Fibonacci numbers, and generated full-width pairs.  Fraction cases check reduction and rejection of a zero denominator.  CLI tests check results and invalid-input diagnostics.

The [test source](../../../../test/seminum.js) and [native reference driver](../../../../test/SeminumNative.lean) define the cases.  The [technical report](report.pdf) explains the algorithm and includes the executable source.  `tools/seminum reports` rebuilds the PDF from [its LaTeX source](report.tex).

## Annotated references

- [Paul E. Black, “binary GCD,” NIST DADS](https://xlinux.nist.gov/dads/HTML/binaryGCD.html): describes the parity and subtraction identities used here and identifies Knuth's Algorithm 4.5.2B.  This implementation counts common shifts, handles zero before the loops, and orders odd operands before subtraction.
