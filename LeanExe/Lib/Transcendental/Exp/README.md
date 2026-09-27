# Bounded exponential: degree-six Taylor evaluation

`expTaylor6` approximates `exp(x)` for binary64 inputs in `[-1, 0]`.  It evaluates the degree-six Taylor polynomial with six multiplications and six additions, rounding after each operation.

[LeanExe](../../../../README.md) compiles the Lean function and its callers to WebAssembly (WASM).  The [command-line examples](../../../../libraries/README.md#setup-and-commands) run that WASM in Wasmtime.

## Verification status

Lean checks the source types.  Passing execution tests establish bit-for-bit agreement between WASM and native Lean on the tested inputs.  They also check domain rejection and compare accepted results with JavaScript's `Math.exp`.  The absolute-error target against the real exponential is `1/4000`.

A separate Lean theorem, [`Project.ExpSmall.Spec.expSmall_real_error`](../../../../proofs/talos/lean/Project/ExpSmall/Spec.lean), proves termination and a finite positive result within `1/4000` of the real exponential for every finite binary64 input in `[-1, 0]`.  Its subject is the WASM model `Project.ExpSmall.module`.  This component uses that development's coefficient words, evaluation order, and domain.  Formal verification of this library function and its compiled clients, including their connection to that theorem, remains deferred.

## Use

The [setup guide](../../../../libraries/README.md#setup-and-commands) lists prerequisites.  From the repository root, these commands build and execute the WASM examples:

```sh
tools/seminum exp-taylor6 -0.5
# 0.6065321180555556
tools/seminum decay 0.5
# 0.6065321180555556
tools/seminum exp-taylor6-bits bfe0000000000000
# 3fe368b60b60b60c
```

`exp-taylor6` and `decay` accept decimal numbers, converted by the host to binary64.  `exp-taylor6-bits` accepts sixteen hexadecimal digits and prints the result bits.  The decay client approximates the remaining fraction `exp(-t)` for dimensionless time `t` in `[0, 1]`.  Inputs outside the admitted interval exit with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.Transcendental.Exp.Basic

def LeanExe.Examples.expHalf : Option UInt64 :=
  LeanExe.Lib.Transcendental.expTaylor6 0xbfe0000000000000
```

The API is `expTaylor6 (bits : UInt64) : Option UInt64`, with binary64 input and output bits.  Both signed zeros return the exact bits of one.  Positive nonzero values, values below minus one, infinities, and NaNs return `none`.  Negative subnormal inputs are admitted.  The [source](Basic.lean) also exposes `expTaylor6Polynomial`, the unguarded polynomial evaluator.  Its caller supplies any required domain checks.

## Tests and report

From the repository root, `node test/seminum.js` compares WASM result bits with native Lean at 33 equally spaced points in `[-1, 0]`, both signed zeros, subnormals, adjacent boundary words, infinities, and NaNs.  Accepted results are finite and positive on these cases.  Their largest sampled absolute difference from `Math.exp` is about `0.00017611438411335723`, at minus one, within the `1/4000` target.  The decay client has corresponding comparisons on `[0, 1]`.  CLI tests check decimal and hexadecimal output and rejected input.

The [test source](../../../../test/seminum.js) and [native reference driver](../../../../test/SeminumNative.lean) define the cases.  The [technical report](report.pdf) explains the polynomial, coefficient representation, domain check, and prior theorem.  It includes the executable source.  `tools/seminum reports` rebuilds the PDF from [its LaTeX source](report.tex).

## Annotated references

- [NIST DLMF, §4.2(iii), equation 4.2.19](https://dlmf.nist.gov/4.2.E19): defines the exponential by its power series.  Truncation after degree six supplies the polynomial used here.
- [Existing small-exponential development](../../../../data/numerical/README.md#small-exponential): records the model, execution theorems, domain, rounding analysis, and `1/4000` bound used to choose this implementation.  Its [model source](../../../../proofs/talos/lean/Project/ExpSmall/Model.lean) gives the coefficient words and evaluation order.
- [LeanExe binary64 primitives](../../../Float64.lean): define the raw-bit arithmetic used by the component.  The compiler implements these calls as WASM floating-point operations.
