# The software fused multiply-add

[The implementation](Fma.lean) exports `fma a b c`, the fused multiply-add of IEEE 754-2019 [1]: the exact `a · b + c` rounded once to the nearest double, ties to even, computed from the operands' bit patterns with 64-bit word arithmetic.  WebAssembly has no scalar fused multiply-add instruction, its relaxed SIMD multiply-add returns the unfused result in the deterministic profile [2], and CORE-MATH's correctly rounded `tgamma`, `lgamma`, and `erfc` call one [4, 5, 6, 7], so the repository's ports of `tgamma` and `lgamma` call this function, and the planned port of CORE-MATH's `erfc` will.  The decision of 2026-10-10 calls for a software fused multiply-add "proved correct once", and the review that proposed it states the theorem as the nearest-even rounding of the exact `a · b + c`.  Track `expm1` proves, on branch `w/expm1` at commit `72655383` and not yet merged into `transcendentals`, that `(fma a b c).toBits` is IEEE 754's fusedMultiplyAdd with roundTiesToEven for every triple of operands, with the canonical NaN for every NaN result (`FmaTheorem.fma_toBits`), and the corollary `FmaSpecTheorem.fma_nearest` in the form that the proofs of `erfc`, `tgamma`, and `lgamma` use.  `transcendentals` compiles the function with the Verified compiler and checks it natively against an exact reference at 763,816 operand triples.

## Specification

For finite `a`, `b`, and `c`, `fma a b c` is the nearest-even rounding of the real number `a · b + c`, with positive or negative infinity at and beyond the overflow threshold `2^1024 - 2^970` of clause 4.3.1 [1].  Every triple of doubles is in the domain.  Clause 5.4.1 defines the operation: it "computes (x × y) + z as if with unbounded range and precision, rounding only once to the destination format" [1].  Clause 6.3 fixes the sign of a zero result, and clause 7.2 the invalid cases.  `F64SignedRounding.WithinSteps 0` of [the signed rounding module](../../LeanExe/ProofKit/F64SignedRounding.lean) would express the finite case except for the sign of a zero, since `position` places both zeros at 0, so the theorem states the operation with a reference of its own, `fmaReference` of [the theorem module](FmaTheorem.lean), defined on words in the style of `Wasm.IEEE64.add` and `Wasm.IEEE64.mul`.  For finite operands it returns `F64SignedRounding.roundNearestEven` of the real `a · b + c`: the finite nonnegative word nearest to the number, the even one at a tie, positive infinity from the overflow threshold on, and the negation of the word of `-y` for a negative `y`, so that a nonzero result that rounds to zero keeps its sign.  For an exact zero sum it returns the zero of the table's sign rules, and for the NaN results of the table it returns the canonical NaN `0x7FF8000000000000`, since `Float.toBits` returns the canonical NaN for every NaN.  The plan states the task as a proof that the function is correct for all inputs against IEEE 754's fusedMultiplyAdd with roundTiesToEven.

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

The theorems are on branch `w/expm1` of track `expm1`, commit `72655383`, and not yet in `transcendentals`.  [The journal section](../../devnotes.md#2026-10-12-the-software-fused-multiply-add-theorem-track-expm1-minideb2) records their logs, and the build `expm1-fma-all-3.log` in `build/transcendentals` on minideb2 checks the whole chain, 3,555 jobs, with 66 axiom reports in the new modules that name only `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | Module | Statement in words |
|---|---|---|
| `fma_toBits` | [`FmaTheorem`](FmaTheorem.lean) | For all `a b c : Float`, `(Fma.fma a b c).toBits = fmaReference a.toBits b.toBits c.toBits`: IEEE 754's fusedMultiplyAdd with roundTiesToEven, signed zeros, subnormal results, overflow, and every NaN and infinity case, with the canonical NaN. |
| `fmaBits_spec` | [`FmaTheorem`](FmaTheorem.lean) | For all words, `fmaBits a b c` with a NaN result replaced by the canonical NaN is `fmaReference a b c`. |
| `fma_nearest` | [`FmaSpecTheorem`](FmaSpecTheorem.lean) | `FmaSpec.FmaNearest`: for finite operands with `|a · b + c| ≤ 2^1023` the result is finite and no finite double lies closer to `a · b + c`. |
| `fmaBits_nan_a`, `fmaBits_nan_b`, `fmaBits_nan_c` | [`FmaSpecial`](FmaSpecial.lean) | For a NaN operand, `fmaBits` returns the first NaN of `a`, `b`, and `c` with bit 51 set. |

`verified_compile` generates the compiler's theorems for the module, `Fma.compiled` with its `denote_eq`, `implements`, `initial`, and `bytes` results, which state that the decoded module computes the Lean functions, and [the Verified compiler's documentation](../README.md) describes them.  The root `Verified` import reaches `Fma` through `Tgamma`, so `lake build Verified` builds these generated theorems, as the integration build `opus-merge-tan-1.log` in `build/transcendentals` on minideb1 did.  No byte theorem or file theorem is planned for `Fma`, which serves as a helper of the gamma and `erfc` modules, and `tests/verified/run.sh` neither writes its module nor checks a file theorem for it.  The theorems of `tgamma`, `lgamma`, and `erfc` are open, and they can use `fma_nearest` at every call.

## Proof

The theorem is an equality of words, so the proof has no error budget.  It counts in units of `2^-2400`, in which every product and sum of doubles is an integer.  The doubles of biased exponent `E`, with `E = 1` for the subnormals, are spaced `2^(E + 1325)` units apart, and `FmaGrid.RoundsTo Y E Q` states that `Y` lies in binade `E` and that `Q` is the integer nearest to `Y / 2^(E + 1325)`, the even one at a tie.  `FmaNearestEven.positive_reference` proves that the nearest-even reference of `Y · 2^-2400` is the word `(E - 1) · 2^52 + Q`, or positive infinity when that word or `E` reaches the exponent field 2047, which is the packing of `roundPack`: every double at or above the start of the binade is a multiple of the spacing, every double below it lies at least half a spacing below the start, and away from a tie every other double lies farther, which gives the even choice.

`FmaRoundPack.roundPack_spec` proves that `roundPack s w h l` packs the `E` and `Q` of `N · 2^w`, for `N = h · 2^64 + l`, in seven cases: a normal result rounded at bit `m - 52`, exact at `m = 52`, or shifted left, and a subnormal result rounded at the bit of weight `2^-1074`, zero when that bit lies above bit 127, exact, or shifted left.  The aligned sum `Z` of the normalized product and addend is exact when the sticky shift loses no set bit, and otherwise it is odd, at least `2^124`, and within one unit of the exact sum at its scale (`FmaAlign`).  `FmaGrid.roundsTo_transfer` then carries the rounding from `Z` to the exact sum: the spacing is at least four units of `Z`, so every bound in `RoundsTo` is a multiple of two units, and an odd multiple of the unit and a number within one unit of it lie on the same side of every such bound.  This is the docstring's argument about the 72 bits below the rounding position, in the weaker form that the proof needs.

| Module | Content |
|---|---|
| [`FmaWords`](FmaWords.lean) | natural-number specifications of the word routines `msb64`, `msb128`, `mul128`, `shl128`, `shr128`, `lowBits128`, `sticky128`, `bit128`, `lt128`, `add128`, and `sub128` |
| [`FmaGrid`](FmaGrid.lean) | `spacing`, `RoundsTo`, `packWord`, the grid of doubles in units of `2^-2400`, and `roundsTo_transfer` |
| [`FmaNearestEven`](FmaNearestEven.lean) | `positive_reference`, `pack_negative`, and `signed_reference`, the nearest-even reference of a signed number in units |
| [`FmaRound`](FmaRound.lean), [`FmaRoundPack`](FmaRoundPack.lean) | the plan, significand, and packing of `roundPack`, the rounding of a right shift (`round_right`), and `roundPack_spec` |
| [`FmaDecode`](FmaDecode.lean) | the fields, sign bits, and zero and NaN tests of an operand, and its value in units |
| [`FmaAlign`](FmaAlign.lean) | the sticky shift and the sum and difference of the aligned addends |
| [`FmaParts`](FmaParts.lean) | `fmaBits_eq`, which names the parts of `fmaBits`, and the normalized product and addend |
| [`FmaCombine`](FmaCombine.lean) | `tail_spec` and `combine_spec`: the rounded sum is the signed reference of the exact sum, or `+0` for an exact zero |
| [`FmaGeneral`](FmaGeneral.lean) | `general_product` and `general_sum`, `fmaBits` on finite operands with nonzero factors |
| [`FmaSpecial`](FmaSpecial.lean) | the NaN, infinity, and zero-product branches, `reference_self`, and `reference_not_nan` |
| [`FmaTheorem`](FmaTheorem.lean), [`FmaSpecTheorem`](FmaSpecTheorem.lean) | `fmaReference`, `fmaBits_spec`, `fma_toBits`, and `fma_nearest` |

The proof uses the ProofKit modules `F64SignedRounding`, `F64PositiveRounding`, `F64NearestEven`, and `F64NearestNonnegative` for the reference, `F64RoundNearest` for the grid of a word's magnitude (`magnitude_dvd`, `magnitude_below`), `F64PositiveOrder`, `F64Exact`, and `F64Magnitude` for the order and values of words, and `F64Bits.toBits_ofBits` for the canonical NaN of `Float.toBits`.  Its word facts are proved by natural-number arithmetic, and `decide +kernel` checks only closed facts about literal words, such as the 64 sign and zero combinations of the infinite products.  The failed approaches, a single rounding module that timed out and a proof of `fmaBits_eq` by `rfl` that exceeded 4,000,000 heartbeats, are in the journal section.

## Tests

`fma_toBits` covers every triple of operands, so the native check below tests the native compilation of the Lean function and the Python model rather than the arithmetic.  [The accuracy check](FmaAccuracy.lean) compares `Fma.fma` with `Reference.toFloat` of the exact integer value of `a · b + c`, with IEEE 754's special values and signs of zero, and it requires the same bits, or a quiet NaN where the reference is NaN.  Its operands are every triple of 24 special values, the zeros, the infinities, a quiet and a signaling NaN, the smallest and largest subnormals, the smallest normal, the largest double, 1, 2, 3, and 1/2 with both signs, and six kinds of hashed operands.  The kinds are operands over all exponents, products near 1 with `c` the negated rounded product and the four doubles next to it, products of 26-bit significands with `c` their negation, results near the smallest normal, results that overflow, and ties at half a unit in the last place of the product and the doubles next to them.

The run `ports-FmaAccuracy-3.log`, in `/home/somebody/src/lt-ports/build/transcendentals` on minideb2, checked 763,816 triples and found every result equal to the reference, quiet NaNs included, and 204,780 of them differ from the separately rounded product and sum.  Before the Lean version, a Python model of the word algorithm agreed with an exact rational reference and with the C library's `fma` at 309,261 triples.  `tests/verified/run.sh` does not run the check, a gap that the plan records under "Corrections found by the documentation review".

In Lean's model of `Float` every NaN is the canonical one, and [the design notes](../../docs/design.md#floating-point) record that native Lean's `toBits` on aarch64 returns the canonical bits for a NaN with a payload.  On such a machine the signaling NaN of the special values reaches `fmaBits` as the canonical quiet NaN, so the check tests the propagation of a payload only for that NaN.  The check's acceptance of any quiet NaN where the reference is NaN therefore does not distinguish the payload rules of the specification.

## Limits

`fma_toBits` is a theorem about the Lean function, and it trusts Lean's kernel and the model of `Float` through `Float.toBits` and `Float.ofBits`.  The payload rule of the specification holds for `fmaBits` on words, and it cannot be observed through `fma`: the `Float` arguments have the canonical NaN only, and `Float.ofBits` compiles to a reinterpretation followed by an addition of `-0.0`, which gives the canonical NaN in Talos, as [the review of the exponential theorem](../../devnotes.md#2026-10-10-review-of-the-exponential-theorem) records.  The compiled module computes the same function by the compiler's generated theorems, and a byte or file theorem for it would share the trusted base of the other modules: Talos's semantics, the decoder, and `binary_file%`.  Until the proof is merged, the uses in `tgamma` and `lgamma` on `transcendentals` rest on the native check, and the `erfc` proof takes `FmaSpec.FmaNearest` as a hypothesis.

## References

1. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clauses 4.3.1 (overflow), 5.4.1 (fusedMultiplyAdd), 6.1 and 6.2.3 (infinities and NaN propagation), 6.3 (the sign of zero results, fusedMultiplyAdd included), and 7.2 (invalid operations, items (a), (c), and (d)).
2. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0: [Instructions](https://webassembly.github.io/spec/core/syntax/instructions.html), whose scalar float instructions include no fused multiply-add, [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html), where the relaxed multiply-add returns the unfused or the fused result and "In the deterministic profile, the unfused behaviour is used", and appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).
3. S. Boldo and G. Melquiond, "Emulation of a FMA and Correctly Rounded Sums: Proved Algorithms Using Rounding to Odd", *IEEE Transactions on Computers* 57(4):462–471, 2008, [doi:10.1109/TC.2007.70819](https://doi.org/10.1109/TC.2007.70819).  Crossref confirms the bibliographic data, and the text was read in the authors' version, [HAL inria-00080427](https://inria.hal.science/inria-00080427), whose abstract states that rounding intermediate values to odd yields correctly rounded results at the end and presents an algorithm that emulates the fused multiply-and-add.
4. The CORE-MATH project, [project page](https://core-math.gitlabpages.inria.fr/), which lists `erfc`, `tgamma`, and `lgamma` among the functions available under the MIT license.
5. CORE-MATH, [`src/binary64/tgamma/tgamma.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/tgamma/tgamma.c), commit `ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8`, Copyright (c) 2024 Alexei Sibidanov, MIT license: 15 calls of `__builtin_fma`.
6. CORE-MATH, [`src/binary64/lgamma/lgamma.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/lgamma/lgamma.c), same commit, Copyright (c) 2025 Alexei Sibidanov, MIT license: 14 calls of `__builtin_fma` and 2 of `__builtin_clzll`.
7. CORE-MATH, [`src/binary64/erfc/erfc.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/erfc/erfc.c), same commit, Copyright (c) 2022-2026 Alexei Sibidanov, Paul Zimmermann, Tom Hubrecht, and Claude-Pierre Jeannerod, MIT license: 53 calls of `__builtin_fma`.
