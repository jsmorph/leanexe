# Checked Horner evaluation

This implementation evaluates a polynomial with nonnegative integer coefficients and argument.  It belongs to the polynomial library.  Coefficients appear in ascending degree order: `1,3,2` represents `1 + 3x + 2x²`.  An empty array represents zero.

## Use

```sh
tools/seminum polynomial 2 1,3,2
# 15
tools/seminum polynomial 99 '[]'
# 0
tools/seminum ratio 2 1,3,2 2,2
# 5/2
```

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  The command builds and executes the generated WASM.  Every argument and coefficient must fit in `UInt64`.  Invalid input or arithmetic overflow exits with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.Polynomial.Horner.Basic

def LeanExe.Examples.quadratic (x : UInt64) : Option UInt64 :=
  LeanExe.Lib.Polynomial.eval #[1, 3, 2] x
```

The API is `eval (coefficients : Array UInt64) (x : UInt64) : Option UInt64`.  The [source](Basic.lean) returns `none` before a Horner step would overflow.  At zero, evaluation returns the constant coefficient or zero for an empty array.  Trailing zero coefficients are accepted.

## Specification and tests

The intended successful result is the exact nonnegative integer polynomial value.  The implementation processes coefficients from highest degree to lowest and checks each multiplication and addition against `2^64 - 1`.  It reads the input array and keeps constant working storage.  Correctness proofs are deferred.

The [polynomial-ratio client](../../../Examples/Seminum.lean) evaluates numerator and denominator polynomials and calls the number-theory library to reduce the fraction.  Either evaluation can report overflow, and a zero denominator is rejected.

`node test/seminum.js` compares WASM with native Lean and an arbitrary-precision sum-of-powers reference.  Cases cover empty and constant polynomials, zero, maximum words, exact boundary results, overflow, and composed clients.  The [technical report](report.pdf) includes the executable source and the overflow-check derivation.  Rebuild it with `tools/seminum reports`.

## Annotated references

- [NIST DLMF, §1.11(i), equations 1.11.1–1.11.4](https://dlmf.nist.gov/1.11.i): gives Horner's recurrence and its polynomial-evaluation identity.  This implementation adds an integer overflow check and an optional result.
