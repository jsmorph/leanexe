# Binary GCD

This implementation computes the greatest common divisor with shifts, comparisons, and subtraction.  It solves the same task as the [Euclidean implementation](../Gcd/README.md) through a different algorithm.  Both accept all `UInt64` pairs and use zero for `gcd 0 0`.

## Use

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  These commands build and execute the WASM clients:

```sh
tools/seminum gcd-binary 48 18
# 6
tools/seminum fraction-binary 48 18
# 8/3
```

```lean
import LeanExe.Lib.NumberTheory.BinaryGcd.Basic

def LeanExe.Examples.commonFactorBinary (a b : UInt64) : UInt64 :=
  LeanExe.Lib.NumberTheory.gcdBinary a b
```

The API is `gcdBinary (a b : UInt64) : UInt64`.  The [source](Basic.lean) removes common powers of two, reduces odd operands by subtraction, and restores the common power.  The [fraction client](../../../Examples/Seminum.lean) calls this implementation and shares result handling with the Euclidean client.

## Specification and tests

The intended result is `Nat.gcd a.toNat b.toNat`, represented as a word.  The implementation handles zero before its shift loops.  It uses constant working storage.  Correctness proofs are deferred.

`node test/seminum.js` compares both algorithms on the same inputs, compares their WASM and native Lean results, and checks the native values against `Nat.gcd`.  Cases include maximum words, zero inputs, powers of two, large consecutive Fibonacci numbers, and fraction clients.  This comparison establishes agreement on the tested cases.  Performance comparisons remain future work.

The [technical report](report.pdf) includes the source, algorithm explanation, and client commands.  Rebuild it with `tools/seminum reports`.

## Annotated references

- [Paul E. Black, “binary GCD,” NIST DADS](https://xlinux.nist.gov/dads/HTML/binaryGCD.html): describes the parity and subtraction identities used here and identifies Knuth's Algorithm 4.5.2B.  This implementation counts common shifts, handles zero before the loops, and orders odd operands before subtraction.
