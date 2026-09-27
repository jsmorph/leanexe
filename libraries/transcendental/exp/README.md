# Bounded exponential: degree-six Taylor evaluation

This implementation approximates `exp(x)` for binary64 inputs in `[-1, 0]`.  It evaluates the degree-six Taylor polynomial with six separately rounded multiplications and additions.  It belongs to the transcendental library.

## Use

The [setup guide](../../README.md#setup-and-commands) lists prerequisites.  These commands compile the imported component and execute it in Wasmtime:

```sh
tools/seminum exp -0.5
# 0.6065321180555556
tools/seminum decay 0.5
# 0.6065321180555556
tools/seminum exp-bits bfe0000000000000
# 3fe368b60b60b60c
```

`exp` and `decay` accept decimal numbers, converted by the host to binary64.  `exp-bits` accepts sixteen hexadecimal digits and prints the result bits.  The decay client approximates the remaining fraction `exp(-t)` for dimensionless time `t` in `[0, 1]`.  Inputs outside the admitted interval exit with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.Transcendental.Exp

def LeanExe.Examples.expHalf : Option UInt64 :=
  LeanExe.Lib.Transcendental.expTaylor6 0xbfe0000000000000
```

The API is `expTaylor6 (bits : UInt64) : Option UInt64`, with binary64 input and output bits.  Both signed zeros return the exact bits of one.  Positive nonzero values, values below minus one, infinities, and NaNs return `none`.  Negative subnormal inputs are admitted.  The [source](../../../LeanExe/Lib/Transcendental/Exp.lean) also exposes `expTaylor6Polynomial`, the unguarded polynomial evaluator.  Its caller supplies any required domain checks.

## Approximation and tests

The target absolute error is `1/4000` against the real exponential of the decoded input.  The coefficient words, evaluation order, and domain follow the existing [small-exponential model](../../../proofs/talos/lean/Project/ExpSmall/Model.lean).  The [existing execution theorem](../../../proofs/talos/lean/Project/ExpSmall/Spec.lean) establishes that bound for its named model.  A proof connecting this library component and its compiled clients to that theorem is deferred.

`node test/seminum.js` compares WASM result bits with native Lean on interval samples, signed zeros, subnormals, adjacent boundary values, infinities, and NaNs.  It compares accepted outputs with the host exponential and checks the target error on those samples.  The maximum sampled absolute error in the recorded run is about `0.00017611438411335723`, at minus one.  The decay client receives the same boundary and rejection tests.

The [technical report](report.pdf) explains the polynomial, coefficient representation, domain check, and prior analysis.  It includes the executable source.  Rebuild it with `tools/seminum reports`.

## Annotated references

- [NIST DLMF, §4.2(iii), equation 4.2.19](https://dlmf.nist.gov/4.2.E19): defines the exponential by its power series.  Truncation after degree six supplies the polynomial used here.
- [Existing small-exponential development](../../../data/numerical/README.md#small-exponential): records the source-model and execution results, domain, rounding analysis, and `1/4000` bound that motivate this implementation.
- [LeanExe binary64 primitives](../../../LeanExe/Float64.lean): define the raw-bit arithmetic used by the component.  The compiler implements these calls as WASM floating-point operations.
