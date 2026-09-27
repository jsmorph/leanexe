# Binary64 exponential

`LeanExe.Lib.Transcendental.exp` computes the exponential across the binary64 input range.  It ports Arm's 128-entry, degree-five algorithm to Lean, using separate binary64 multiplications and additions.  LeanExe compiles the function and its callers to WebAssembly (WASM).

## Verification status

The verification target is the emitted WASM: termination, memory behavior, and numerical accuracy under stated assumptions.  A proof establishing those properties remains outstanding.  Lean checks the source types, and execution tests supply development evidence.  The accuracy target is an error below one ulp with round-to-nearest, ties-to-even arithmetic.  The tests compare WASM with the Lean port, Lean's `Float.exp`, JavaScript's `Math.exp`, and a high-precision decimal reference.

On the 49,821-input development corpus, WASM and the Lean port agree bit for bit.  The largest measured errors are 0.504059 ulp for this implementation, 0.503354 ulp for Lean's `Float.exp`, and 0.871814 ulp for JavaScript's `Math.exp`.  The respective counts of differences from the reference's rounded result are 49, 36, and 4,153.  These measurements used Linux AArch64 and Node.js 24.13.0.  Throughput and latency have yet to be measured.

Arm reports a worst-case error of 0.511 ulp for the selected configuration without fused multiply-add.  That published analysis motivates the algorithm choice.  Establishing a universal error bound for the emitted WASM requires a proof of its computation.

## API and computation

```lean
import LeanExe.Lib.Transcendental.ExpArm.Basic

-- Input and output are IEEE 754 binary64 words.
#eval LeanExe.Lib.Transcendental.exp 0x3FF0000000000000
```

The API takes and returns `UInt64` bit patterns, matching LeanExe's binary64 arithmetic interface.  Both signed zeros return one.  Positive infinity returns positive infinity, and negative infinity returns positive zero.  NaNs return the canonical quiet NaN `0x7FF8000000000000`.  Finite results can overflow to positive infinity or underflow through subnormal values to positive zero.  The API specifies result values with round-to-nearest arithmetic.  It has no error-number or floating-point exception-flag interface.

The implementation reduces `x` to `k·log(2)/128 + r`.  A split logarithm keeps the reduction error small.  A table supplies the scale and its correction, and a degree-five polynomial approximates the exponential of the small remainder.  Reconstruction handles large positive exponents and rounds small results before scaling them into the subnormal range.

[The implementation](Basic.lean) records the operation order and coefficients as binary64 words.  [The lookup table](Table.lean) contains 128 pairs of words.  LeanExe stores this table in a WASM data segment, and indexed reads allocate no heap objects.  The [technical report](report.pdf) explains the reduction and reconstruction.

## Commands and client

The commands run from the repository root after following the [setup guide](../../../../DEVELOPING.md).

```sh
tools/seminum exp 1
tools/seminum exp -745
tools/seminum exp-bits 7ff0000000000000
tools/seminum sigmoid -10
node test/exp.js
```

`exp` accepts a finite decimal input and prints the binary64 result in decimal.  `exp-bits` accepts all sixteen-digit hexadecimal input words and prints the result word.  `sigmoid` computes `1 / (1 + exp(-x))`, using `exp(-abs(x))` so that large negative inputs retain their small positive results without an overflowing intermediate exponential.  The client is in [the example module](../../../Examples/Seminum.lean).

The introductory [degree-six Taylor component](../Exp/README.md) remains available through `tools/seminum exp-taylor6` and `exp-taylor6-bits` on `[-1, 0]`.  The `decay` command continues to demonstrate that component.

## Tests and references

[The test driver](../../../../test/exp.js) checks bit-for-bit agreement between WASM and the Lean port.  [The native driver](../../../../test/ExpNative.lean) also evaluates Lean's `Float.exp`, which the pinned Lean toolchain implements through the C function `exp`.  [The decimal reference](../../../../test/exp-reference.py) starts at 100 significant digits and increases precision until neighboring decimal bounds round to the same binary64 value.  It measures error in units of binary64 spacing at the exact result's binade, with spacing `2^-1074` for subnormal results.

The corpus includes signed zeros, infinities, quiet and signaling NaNs, random bit patterns, inputs across the finite output range, and neighbors of reduction, overflow, and underflow boundaries.  The driver writes its accuracy measurements to `build/seminum/exp-accuracy.json`.  Separate tests cover the sigmoid client, command-line output, and allocation counts.

| Reference | Use |
|-----------|-----|
| [Arm, exponential source](https://github.com/ARM-software/optimized-routines/blob/master/math/exp.c) | Range reduction, evaluation order, and overflow and subnormal reconstruction.  This port selects the round-to-nearest path without fused operations. |
| [Arm, exponential data](https://github.com/ARM-software/optimized-routines/blob/master/math/exp_data.c) | The 128-entry table, split logarithm, polynomial coefficients, and published error analysis. |
| [Lean, floating-point API](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Init/Data/Float/Float.lean) | The `Float.exp` declaration names the external C function used in the comparison. |
| [Python, `Decimal.exp`](https://docs.python.org/3/library/decimal.html#decimal.Decimal.exp) | Correct rounding at the requested decimal precision and exact conversion of binary floating-point inputs. |

The Arm-derived implementation and table retain their copyright notices and use the [MIT license](LICENSE).
