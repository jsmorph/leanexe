import Verified.Examples.AsinhTheoremSmallCases
import Verified.Examples.AsinhTheoremLarge
import Verified.Examples.AsinhTheoremTiny
import Verified.Examples.AtanhTheorem

/-!
**`asinh` within two steps** and its exceptional inputs.  Below `2 ^ -28` the result is `x`
(`AsinhTheoremTiny`); above it the code computes `asinhW |x|` and takes the sign of `x`, with the
branches of `AsinhTheoremSmallCases` up to `2 (1 + 2 ^ -20)`, `AsinhTheoremMid` up to
`2 ^ 28 (1 + 2 ^ -20)`, and `AsinhTheoremLarge` above.  `±0` give `±0`, `±∞` give `±∞`, and NaN
gives the canonical NaN through `x + x`.
-/

namespace Verified.Examples.AsinhTheorem
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AsinhTheoremBranches

set_option exponentiation.threshold 4096

theorem ix_gt_iff (x : Float) (H : UInt64) (hH : H.toNat + 1 < 2 ^ 64) :
    ixOf x > H ↔ ¬ ixOf x < UInt64.ofNat (H.toNat + 1) := by
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
  omega

theorem ix_big (x : Float) : ixOf x > 0x41b00000 ↔ 268435712 ≤ |value x.toBits| := by
  rw [ix_gt_iff x 0x41b00000 (by decide)]
  have h := AtanTheorem.ix_lt x 0x41b00001 (by norm_num) 268435712 (by decide +kernel)
  push_cast at h
  exact (not_congr h).trans not_lt

theorem ix_mid (x : Float) : ixOf x > 0x40000000 ↔ 1048577 / 524288 ≤ |value x.toBits| := by
  rw [ix_gt_iff x 0x40000000 (by decide)]
  have h := AtanTheorem.ix_lt x 0x40000001 (by norm_num) (1048577 / 524288) (by decide +kernel)
  push_cast at h
  exact (not_congr h).trans not_lt

theorem ix_28 (x : Float) : ixOf x < 0x3e300000 ↔ |value x.toBits| < 1 / 2 ^ 28 := by
  have h := AtanTheorem.ix_lt x 0x3e300000 (by norm_num) (1 / 2 ^ 28) (by decide +kernel)
  push_cast at h
  exact h

theorem asinh_nonfinite_eq (x : Float) (h : ixOf x ≥ 0x7ff00000) : Asinh.asinh x = x + x := by
  unfold ixOf at h
  simp only [Asinh.asinh, Asinh.asinhWith, h, ite_true]

/-- **`asinh` within two steps.**  For every finite `x`, `Asinh.asinh x` lies within two
representable steps of the nearest-even rounding of `arsinh x`. -/
theorem asinh_within_two (x : Float) (hx : Finite x.toBits) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh (value x.toBits)) (Asinh.asinh x).toBits := by
  have h0 : ¬ ixOf x ≥ 0x7ff00000 := by
    have := F64UpperWord.finite_high x.toBits hx
    rw [ge_iff_le, UInt64.le_iff_toNat_le, not_le]
    exact this
  by_cases c1 : ixOf x < 0x3e300000
  · have hs := (ix_28 x).mp c1
    rw [asinh_tiny_eq x c1 (AtanTheorem.huge_gt x hx
      (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 28 < 1)]))]
    have h := AsinhTheoremTiny.asinh_tiny x hx hs
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  have h28 : 1 / 2 ^ 28 ≤ |value x.toBits| := not_lt.mp (fun h => c1 ((ix_28 x).mpr h))
  have hx0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at h28
    linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 28)]
  rw [asinh_main_eq x h0 c1]
  refine AsinhTheoremLarge.signed_two x (asinhW x) Real.arsinh Real.arsinh_neg ?_ hx0
  unfold asinhW
  by_cases c2 : ixOf x > 0x41b00000
  · rw [if_pos c2]
    exact AsinhTheoremLarge.asinh_large_w x hx
      (by linarith [(ix_big x).mp c2, (by norm_num : (2 : ℝ) ^ 28 ≤ 268435712)])
  rw [if_neg c2]
  have hbig : |value x.toBits| < 268435712 := not_le.mp (fun h => c2 ((ix_big x).mpr h))
  by_cases c3 : ixOf x > 0x40000000
  · rw [if_pos c3]
    exact AsinhTheoremMid.asinh_mid_w x hx
      (by linarith [(ix_mid x).mp c3, (by norm_num : (2 : ℝ) ≤ 1048577 / 524288)])
      (by linarith [(by norm_num : (268435712 : ℝ) ≤ 2 ^ 29)])
  rw [if_neg c3]
  have hmid : |value x.toBits| < 1048577 / 524288 := not_le.mp (fun h => c3 ((ix_mid x).mpr h))
  exact AsinhTheoremSmallCases.asinh_small x hx h28
    (by linarith [(by norm_num : (1048577 : ℝ) / 524288 ≤ 1000001 / 500000)])

theorem asinh_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Asinh.asinh x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hix : ixOf x ≥ 0x7ff00000 := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le]
    unfold ixOf
    rw [F64UpperWord.high_toNat]
    have hw := x.toBits.toNat_lt
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h
    simp only [UInt64.reduceToNat]
    omega
  rw [asinh_nonfinite_eq x hix, F64Bits.toBits_add]
  simp only [Wasm.IEEE64.add, h, Bool.true_or, ite_true]

theorem asinh_inf (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Asinh.asinh x).toBits = 0x7FF0000000000000 := by
  rw [asinh_nonfinite_eq x (by unfold ixOf; rw [h]; decide), F64Bits.toBits_add, h]
  decide +kernel

theorem asinh_neg_inf (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Asinh.asinh x).toBits = 0xFFF0000000000000 := by
  rw [asinh_nonfinite_eq x (by unfold ixOf; rw [h]; decide), F64Bits.toBits_add, h]
  decide +kernel

theorem asinh_zero (x : Float) (h : x.toBits = 0) : (Asinh.asinh x).toBits = 0 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  rw [asinh_tiny_eq x (by unfold ixOf; rw [h]; decide)
    (AtanTheorem.huge_gt x hx (by rw [h, F64Magnitude.value_zero, abs_zero]; norm_num)), h]

theorem asinh_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (Asinh.asinh x).toBits = 0x8000000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by
    rw [h, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x8000000000000000 = 0 by
      decide +kernel]
    norm_num
  rw [asinh_tiny_eq x (by unfold ixOf; rw [h]; decide)
    (AtanTheorem.huge_gt x hx (by rw [hv, abs_zero]; norm_num)), h]

#print axioms asinh_within_two
#print axioms asinh_nan
#print axioms asinh_inf
#print axioms asinh_neg_inf
#print axioms asinh_zero
#print axioms asinh_neg_zero

end Verified.Examples.AsinhTheorem
