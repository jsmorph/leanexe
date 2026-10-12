# The software fused multiply-add

[The implementation](Fma.lean) exports `fma a b c`, the fused multiply-add of IEEE 754-2019 [1]: the exact `a · b + c` rounded once to the nearest double, ties to even, computed from the operands' bit patterns with 64-bit word arithmetic.  WebAssembly has no scalar fused multiply-add instruction, its relaxed SIMD multiply-add returns the unfused result in the deterministic profile [2], and CORE-MATH's correctly rounded `tgamma`, `lgamma`, and `erfc` call one [4, 5, 6, 7], so the repository's ports of `tgamma` and `lgamma` call this function, and the planned port of CORE-MATH's `erfc` will.  The decision of 2026-10-10 calls for a software fused multiply-add "proved correct once", and the review that proposed it states the theorem as the nearest-even rounding of the exact `a · b + c`.  `transcendentals` compiles the function with the Verified compiler and checks it natively against an exact reference at 763,816 operand triples, and it contains no theorem about its result.  [The plan](../../transcendentals.md#state-of-each-track) assigns that proof to track `expm1`, which has not started it.

## Specification

For finite `a`, `b`, and `c`, `fma a b c` is the nearest-even rounding of the real number `a · b + c`, with positive or negative infinity at and beyond the overflow threshold `2^1024 - 2^970` of clause 4.3.1 [1].  Every triple of doubles is in the domain.  Clause 5.4.1 defines the operation: it "computes (x × y) + z as if with unbounded range and precision, rounding only once to the destination format" [1].  Clause 6.3 fixes the sign of a zero result, and clause 7.2 the invalid cases.  `F64SignedRounding.WithinSteps 0` of [the signed rounding module](../../LeanExe/ProofKit/F64SignedRounding.lean) would express the finite case except for the sign of a zero, since `position` places both zeros at 0, so a theorem for this function needs a statement of its own, which the repository does not yet have.  The plan states the task as a proof that the function is correct for all inputs against IEEE 754's fusedMultiplyAdd with roundTiesToEven.

| Inputs | Result | Rule of IEEE 754-2019 [1] |
|---|---|---|
| a NaN among `a`, `b`, `c` | the first NaN of `a`, `b`, and `c`, with the quiet bit set | 6.2.3: a propagated NaN should keep an input's payload, without fixing which input's; 7.2 (a): a signaling NaN gives a quiet NaN |
| `0 · ∞` or `∞ · 0`, no NaN operand | the default NaN `0x7FF8000000000000` | 7.2 (c) |
| an infinite product and an infinite `c` of the opposite sign | the default NaN | 7.2 (d) |
| an infinite product otherwise | the infinity with the product's sign | 6.1 |
| a finite product and an infinite `c` | `c` | 6.1 |
| a zero product and a zero `c` | `-0` if both are negative zeros, else `+0` | 6.3: the sign rules of a sum |
| a nonzero product and a nonzero `c` whose exact sum is zero | `+0` | 6.3, rounding to nearest |
| a nonzero exact result that rounds to zero | the zero with the exact result's sign | 6.3 |
| an exact result at or beyond the overflow threshold | the infinity with its sign | 4.3.1 |

IEEE 754 leaves the NaN of an invalid operation and the choice of a propagated payload to the implementation, and the port's choices are those of the table.  The function raises no flags, since the dialect has none.  For `0 · ∞ + c` with a quiet NaN `c`, clause 7.2 (c) leaves the invalid flag to the implementation, and the port returns `c`, quieted, as it does for every NaN operand.

## Algorithm

The operation needs the exact sum of a 106-bit product and a 53-bit addend at an arbitrary distance in exponent, rounded once.  The port keeps both in 128-bit integers held as pairs of words, and it uses a sticky bit to bound the width it needs.  The port follows no published algorithm.  [The module's docstring](Fma.lean) and [the journal's section on the port](../../devnotes.md#2026-10-11-a-software-fused-multiply-add-core-maths-gamma-functions-and-fdlibms-bessel-functions) describe the method, which [the review of the options for stages 7 and 8](../../devnotes.md#2026-10-10-review-of-the-options-for-stages-7-and-8) proposed: decode the operands, multiply the significands, align the addend with a sticky bit, add or subtract, normalize, and round to nearest even.

| Step | Computation | Reason |
|---|---|---|
| Special operands | NaN, infinity, and zero operands return at once, by the table of the specification. | The integer path then has nonzero finite operands. |
| Significands | A finite operand with biased exponent `e` and significand `m` (with the hidden bit when `e > 0`) has the value `m · 2^(max e 1 - 1075)`. | Subnormal operands need no separate path. |
| Product | `mul128` multiplies the 32-bit halves: the middle sum `a0 · b1 + a1 · b0` is below `2^54` and fits a word, and the carry of the low word is detected by comparison. | The exact 106-bit product of two significands below `2^53`. |
| Normalization | The product and `c`'s significand are shifted left so that each has its highest set bit at bit 125 of its pair, and `w`, the exponent of bit 0 plus 2400, records each scale. | Bits 0 to 19 are then clear in both, and the offset 2400 keeps the exponents unsigned. |
| Alignment | The operand of smaller magnitude is shifted right by the difference of the scales, and the bits it loses are ORed into bit 0 (`sticky128`). | A shift of 20 or less loses no bit, so the sum is exact.  A longer shift leaves the sum's highest bit at 124 or above, so at least 72 bits lie below the rounding position, and the sticky bit, which makes the sum odd, marks the sum inexact without changing the rounding. |
| Sum | The pairs are added when the signs agree and subtracted, larger minus smaller, when they differ.  An exact zero gives `+0`. | Rounding to nearest gives `+0` for an exact zero sum of nonzero operands. |
| Rounding | `roundPack` finds the highest bit `m`, keeps 53 bits from it for a normal result, with `w + m ≥ 1378`, or the bits from the one of weight `2^-1074` for a subnormal result, and rounds to nearest even from the next bit and the bits below it. | The result is `(e - 1) · 2^52 + q` with `e = 1` for a subnormal result, so a carry of the rounding moves into the exponent field, and a field of 2047 or more gives infinity. |

The sticky bit makes the shifted operand the rounding to odd of its exact value at bit 0.  Boldo and Melquiond showed that rounding intermediate values to odd, instead of to nearest, yields correctly rounded results at the end, and they used it to emulate a fused multiply-add with floating-point operations [3].  The port's argument is the direct one of its docstring, about bit positions, and the port does not implement their algorithm.

## Implementation

[The implementation](Fma.lean) is the repository's own and has no external source, so it carries no third-party notice.  It uses word operations only, in the Verified dialect, and `verified_compile compiled := [msb64, msb128, mul128, shl128, shr128, lowBits128, sticky128, bit128, lt128, add128, sub128, roundPack, fmaBits, fma]` compiles it.  `fma a b c` is `Float.ofBits (fmaBits a.toBits b.toBits c.toBits)`, so the arithmetic is on words, and only the conversions touch floats.  The module calls no other module.

| Constant | Meaning |
|---|---|
| `0xFFFFFFFFFFFFF` | the fraction field |
| `0x10000000000000` | the hidden bit, `2^52` |
| `0x8000000000000` | the quiet bit of a NaN |
| `0x7FF0000000000000`, `0x7FF8000000000000` | positive infinity and the default NaN |
| 125 | the position of the highest bit after normalization |
| 2400, 250, 1325 | the offset of `w`, and its values for the product, `ea + eb + 250 - shift`, and for `c`, `ec + 1325 - shift` |
| 1378, 1326 | `w + m ≥ 1378` for a normal result, and bit `1326 - w` of weight `2^-1074` |

`Tgamma.lean` and `Lgamma.lean` call `Fma.fma` for each `__builtin_fma` of CORE-MATH's sources at commit `ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8` [5, 6], as [the journal section on the ports](../../devnotes.md#2026-10-11-a-software-fused-multiply-add-core-maths-gamma-functions-and-fdlibms-bessel-functions) records.  `tgamma.c` has 15 such calls and `Tgamma.lean` 15 calls of `Fma.fma`, and `lgamma.c` has 14, of which `Lgamma.lean` makes 12 and takes the 2 of `muldd` and `mulddd` from `Tgamma`'s helpers.  `Lgamma.lean` also writes `__builtin_clzll` as `63 - Fma.msb64`.  WebAssembly 3.0 has a relaxed multiply-add in its SIMD instructions, which may return the fused or the unfused result, and in the deterministic profile it returns the unfused one [2], so it cannot replace this function.  A call costs about 150 word operations, by the review's estimate, against one instruction on hardware with a fused multiply-add.

## Theorems

No theorem states the result of `Fma.fma` or `Fma.fmaBits`.  `verified_compile` generates the compiler's theorems for the module, `Fma.compiled` with its `denote_eq`, `implements`, `initial`, and `bytes` results, which state that the decoded module computes the Lean functions, and [the Verified compiler's documentation](../README.md) describes them.  The root `Verified` import reaches `Fma` through `Tgamma`, so `lake build Verified` builds these generated theorems, as the integration build `opus-merge-tan-1.log` in `build/transcendentals` on the build host did.  The journal records no axiom report for them, and `tests/verified/run.sh` neither writes the module of `Fma` nor checks a file theorem for it.

| Item | State |
|---|---|
| A theorem that `fmaBits` returns the nearest-even rounding of the exact `a · b + c`, with the special cases | Assigned to track `expm1` and not started.  The review names ProofKit's rounding of scaled rationals, `F64RoundRational` and `F64RoundScaled`, as the rounding half of that proof. |
| A byte theorem and a file theorem | Planned in neither the journal nor the plan.  The function serves as a helper of the gamma modules. |
| The theorems of `tgamma` and `lgamma` | Open.  They would use the fused multiply-add theorem at every call. |

## Proof

No proof module exists for the fused multiply-add in `transcendentals` or on a branch.  The plan's section ["Resuming the work"](../../transcendentals.md#resuming-the-work) assigns the proof to track `expm1`, and it assigns the mathematical facts of the gamma functions to track `erf`.  The review proposed one theorem that covers every use: that `fma` returns the nearest-even rounding of the exact `a · b + c`.  The exactness argument of the algorithm, the bound on the shift that loses no bit and the 72 bits below the rounding position otherwise, is stated in the docstring and has no Lean counterpart yet.

## Tests

[The accuracy check](FmaAccuracy.lean) compares `Fma.fma` with `Reference.toFloat` of the exact integer value of `a · b + c`, with IEEE 754's special values and signs of zero, and it requires the same bits, or a quiet NaN where the reference is NaN.  Its operands are every triple of 24 special values, the zeros, the infinities, a quiet and a signaling NaN, the smallest and largest subnormals, the smallest normal, the largest double, 1, 2, 3, and 1/2 with both signs, and six kinds of hashed operands.  The kinds are operands over all exponents, products near 1 with `c` the negated rounded product and the four doubles next to it, products of 26-bit significands with `c` their negation, results near the smallest normal, results that overflow, and ties at half a unit in the last place of the product and the doubles next to them.

The run `ports-FmaAccuracy-3.log`, in `build/transcendentals` on the build host, checked 763,816 triples and found every result equal to the reference, quiet NaNs included, and 204,780 of them differ from the separately rounded product and sum.  Before the Lean version, a Python model of the word algorithm agreed with an exact rational reference and with the C library's `fma` at 309,261 triples.  `tests/verified/run.sh` does not run the check, a gap that the plan records under "Corrections found by the documentation review".

In Lean's model of `Float` every NaN is the canonical one, and [the design notes](../../docs/design.md#floating-point) record that native Lean's `toBits` on aarch64 returns the canonical bits for a NaN with a payload.  On such a machine the signaling NaN of the special values reaches `fmaBits` as the canonical quiet NaN, so the check tests the propagation of a payload only for that NaN.  The check's acceptance of any quiet NaN where the reference is NaN therefore does not distinguish the payload rules of the specification.

## Limits

Nothing about the result of `fma` is proved, so every use in `tgamma` and `lgamma` rests on the native check.  The payload rule of the specification holds for `fmaBits` on words, and it cannot be observed through `fma`: the `Float` arguments have the canonical NaN only, and `Float.ofBits` compiles to a reinterpretation followed by an addition of `-0.0`, which gives the canonical NaN in Talos, as [the review of the exponential theorem](../../devnotes.md#2026-10-10-review-of-the-exponential-theorem) records.  A theorem about the compiled module would also share the trusted base of the other modules: Talos's semantics, the decoder, and `binary_file%` for a file theorem.

## References

1. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clauses 4.3.1 (overflow), 5.4.1 (fusedMultiplyAdd), 6.1 and 6.2.3 (infinities and NaN propagation), 6.3 (the sign of zero results, fusedMultiplyAdd included), and 7.2 (invalid operations, items (a), (c), and (d)).
2. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0: [Instructions](https://webassembly.github.io/spec/core/syntax/instructions.html), whose scalar float instructions include no fused multiply-add, [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html), where the relaxed multiply-add returns the unfused or the fused result and "In the deterministic profile, the unfused behaviour is used", and appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).
3. S. Boldo and G. Melquiond, "Emulation of a FMA and Correctly Rounded Sums: Proved Algorithms Using Rounding to Odd", *IEEE Transactions on Computers* 57(4):462–471, 2008, [doi:10.1109/TC.2007.70819](https://doi.org/10.1109/TC.2007.70819).  Crossref confirms the bibliographic data, and the text was read in the authors' version, [HAL inria-00080427](https://inria.hal.science/inria-00080427), whose abstract states that rounding intermediate values to odd yields correctly rounded results at the end and presents an algorithm that emulates the fused multiply-and-add.
4. The CORE-MATH project, [project page](https://core-math.gitlabpages.inria.fr/), which lists `erfc`, `tgamma`, and `lgamma` among the functions available under the MIT license.
5. CORE-MATH, [`src/binary64/tgamma/tgamma.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/tgamma/tgamma.c), commit `ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8`, Copyright (c) 2024 Alexei Sibidanov, MIT license: 15 calls of `__builtin_fma`.
6. CORE-MATH, [`src/binary64/lgamma/lgamma.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/lgamma/lgamma.c), same commit, Copyright (c) 2025 Alexei Sibidanov, MIT license: 14 calls of `__builtin_fma` and 2 of `__builtin_clzll`.
7. CORE-MATH, [`src/binary64/erfc/erfc.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/erfc/erfc.c), same commit, Copyright (c) 2022-2026 Alexei Sibidanov, Paul Zimmermann, Tom Hubrecht, and Claude-Pierre Jeannerod, MIT license: 53 calls of `__builtin_fma`.
