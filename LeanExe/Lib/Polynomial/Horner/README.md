# Horner evaluation with overflow checks

`eval` evaluates a polynomial with nonnegative integer coefficients and argument, checking for overflow before each multiply-add step.  Coefficients appear in ascending degree order: `1,3,2` represents `1 + 3x + 2x²`.  An empty array represents zero.

[LeanExe](../../../../README.md) compiles the Lean function and its callers to WebAssembly (WASM).  The [command-line examples](../../../../libraries/README.md#setup-and-commands) run that WASM in Wasmtime.

## Verification status

Lean checks the source types.  Passing execution tests establish agreement between WASM, native Lean, and an arbitrary-precision polynomial reference on the tested inputs, including overflow cases.  Formal proofs of polynomial correctness, overflow detection, termination, and the behavior of the generated WASM and clients remain deferred.

## Use

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  From the repository root, these commands build and execute the WASM examples:

```sh
tools/seminum polynomial 2 1,3,2
# 15
tools/seminum polynomial 99 '[]'
# 0
tools/seminum ratio 2 1,3,2 2,2
# 5/2
```

Every argument and coefficient must fit in `UInt64`.  Invalid input or arithmetic overflow exits with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.Polynomial.Horner.Basic

def LeanExe.Examples.quadratic (x : UInt64) : Option UInt64 :=
  LeanExe.Lib.Polynomial.eval #[1, 3, 2] x
```

The API is `eval (coefficients : Array UInt64) (x : UInt64) : Option UInt64`.  The intended successful result is the exact nonnegative integer polynomial value.  The [source](Basic.lean) processes coefficients from highest degree to lowest and returns `none` before a step would exceed `2^64 - 1`.  At zero, evaluation returns the constant coefficient or zero for an empty array.  Trailing zero coefficients are accepted.  The loop reads the input array and keeps constant working storage.

The [polynomial-ratio client](../../../Examples/Seminum.lean) evaluates numerator and denominator polynomials and calls GCD to reduce the fraction.  Either evaluation can report overflow, and a zero denominator is rejected.

## Tests and report

From the repository root, `node test/seminum.js` compares WASM with native Lean and an arbitrary-precision sum-of-powers reference.  Cases cover empty and constant polynomials, zero arguments, maximum words, exact boundary results, and overflow.  The ratio tests cover successful composition, a zero denominator, and overflow in either polynomial.  CLI tests check results and invalid-input diagnostics.

The [test source](../../../../test/seminum.js) and [native reference driver](../../../../test/SeminumNative.lean) define the cases.  The [technical report](report.pdf) derives the overflow check and includes the executable source.  `tools/seminum reports` rebuilds the PDF from [its LaTeX source](report.tex).

## Annotated references

- [NIST DLMF, §1.11(i), equations 1.11.1–1.11.4](https://dlmf.nist.gov/1.11.i): gives Horner's recurrence and its polynomial-evaluation identity.  This implementation adds an integer overflow check and an optional result.
