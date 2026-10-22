import Library.Numerics.Float64.Log2.Log2CoreStep
import Library.Numerics.Float64.Log2.Log2Branches
import Library.Numerics.Float64.Log.LogMain

/-!
`Log2.log2` on positive normal arguments outside the path near 1, and on positive subnormal
arguments: the result lies within one representable step of the nearest-even reference of
`log x / log 2`.  These arguments take `Log2.log2Core`, normal ones with their own bits and
subnormal ones scaled by `2 ^ 52`, so `Log2CoreStep.core2_within` applies.  The proofs follow
`LogMain`.
-/

namespace Library.Numerics.Float64.Log2.Log2Main
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem bound2_values :
    value (0x3FEEA4AF00000000 : UInt64) = 2008239 / 2097152 ∧
      value (0x3FF0B55900000000 : UInt64) = 1095001 / 1048576 := by
  have h1 : PolyBound.ratOfWord 0x3FEEA4AF00000000 = 2008239 / 2097152 := by decide +kernel
  have h2 : PolyBound.ratOfWord 0x3FF0B55900000000 = 1095001 / 1048576 := by decide +kernel
  rw [← PolyBound.ratOfWord_cast, ← PolyBound.ratOfWord_cast, h1, h2]
  norm_num

/-- `Log2.log2` on a positive normal argument outside the path near 1. -/
theorem log2_normal_within (x : Float) (hf : Finite x.toBits)
    (hs : Wasm.IEEE64.sign x.toBits = false) (he : 1 ≤ Wasm.IEEE64.exponent x.toBits)
    (hnear : x.toBits.toNat < 4606800540372828160 ∨ 4607381812656734208 ≤ x.toBits.toNat) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits) / Real.log 2)
      (Log2.log2 x).toBits := by
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hN : x.toBits.toNat = Wasm.IEEE64.exponent x.toBits * 4503599627370496 +
      Wasm.IEEE64.fraction x.toBits := by
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow] at he hfin ⊢
    simp only [Nat.reducePow] at hlt
    omega
  have hfrac : Wasm.IEEE64.fraction x.toBits < 4503599627370496 := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hlo : 4503599627370496 ≤ x.toBits.toNat := by omega
  have hhi : x.toBits.toNat < 9218868437227405312 := by
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    simp only [Nat.reducePow] at hlt
    omega
  rw [Log2.log2, Log2Branches.normal_selected _ _ x hlo hhi hnear, Library.Numerics.Float64.Log.LogMain.normal_form _ hs he]
  have hv := Library.Numerics.Float64.Log.LogMain.normal_form _ hs he
  obtain ⟨hb1, hb2⟩ := bound2_values
  apply Log2CoreStep.core2_within x.toBits (Wasm.IEEE64.exponent x.toBits)
    (Wasm.IEEE64.fraction x.toBits) (by omega) (by omega) hfrac
  · have : x.toBits.toNat < 18446744073709551616 := by omega
    rw [hN]
    push_cast
    omega
  · rw [← hv]
    rcases hnear with h | h
    · left
      have := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3FEEA4AF00000000 : UInt64)) (by decide) h
      rw [hb1] at this
      exact this.le
    · right
      have := (F64PositiveOrder.value_le_iff (left := (0x3FF0B55900000000 : UInt64))
        (right := x.toBits) (by decide) hlt).mpr h
      rw [hb2] at this
      exact this

/-- `Log2.log2` on a positive subnormal argument, which the code scales by `2 ^ 52` into the main
path. -/
theorem log2_subnormal_within (x : Float) (hlo : 0 < x.toBits.toNat)
    (hhi : x.toBits.toNat < 4503599627370496) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits) / Real.log 2)
      (Log2.log2 x).toBits := by
  rw [Log2.log2, Log2Branches.subnormal_selected _ _ x hlo hhi]
  have hcn : Wasm.IEEE64.isNaN 0x4330000000000000 = false := by decide
  have hw : (x * Float.ofBits 0x4330000000000000).toBits =
      Wasm.IEEE64.mul x.toBits 0x4330000000000000 := by
    rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits, hcn]
    rfl
  rw [hw]
  have hxe : Wasm.IEEE64.exponent x.toBits = 0 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hxfr : Wasm.IEEE64.fraction x.toBits = x.toBits.toNat := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hxe]
    decide
  have hxs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    omega
  have hxm : Wasm.IEEE64.scaledMagnitude x.toBits = x.toBits.toNat * 2 ^ 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hxe, hxfr, beq_self_eq_true, ↓reduceIte]
    ring
  have hcf : Finite (0x4330000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have hcm : Wasm.IEEE64.scaledMagnitude (0x4330000000000000 : UInt64) = 1 * 2 ^ 1126 := by
    decide +kernel
  have hcs : Wasm.IEEE64.sign (0x4330000000000000 : UInt64) = false := by decide
  have hcv : value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
    have h : PolyBound.ratOfWord 0x4330000000000000 = 2 ^ 52 := by decide +kernel
    rw [← PolyBound.ratOfWord_cast, h]
    norm_num
  obtain ⟨hwf, hwv, hwm, hws⟩ := F64ExactProduct.mul_exact_scaled x.toBits _ hxf hcf
    x.toBits.toNat 1 0 1126 hxm hcm (by omega) (by norm_num) (by norm_num)
  rw [hxs, hcs, hcv] at *
  simp only [bne_self_eq_false] at hws
  generalize hwdef : Wasm.IEEE64.mul x.toBits 0x4330000000000000 = w at hwf hwv hwm hws ⊢
  obtain ⟨e, he⟩ : ∃ e, Wasm.IEEE64.exponent w = e := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, Wasm.IEEE64.fraction w = f := ⟨_, rfl⟩
  have hflt : f < 4503599627370496 := by
    rw [← hf]
    simp only [Wasm.IEEE64.fraction]
    omega
  have hwlt : w.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hws
    exact hws
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    have hsm : Wasm.IEEE64.scaledMagnitude w = f := by
      simp only [Wasm.IEEE64.scaledMagnitude, he, hf, he0, beq_self_eq_true, ↓reduceIte]
    rw [hsm] at hwm
    have : 4503599627370496 ≤ x.toBits.toNat * 1 * 2 ^ (0 + 1126 - 1074) := by
      simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, mul_one]
      omega
    omega
  have hsm : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + f) * 2 ^ (e - 1) := by
    have hne : (e == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf, hne, Bool.false_eq_true, ↓reduceIte]
  have he52 : e ≤ 52 := by
    rw [hsm] at hwm
    simp only [Nat.reduceAdd, Nat.reduceSub, mul_one] at hwm
    have h1 : 2 ^ 52 * 2 ^ (e - 1) ≤ (2 ^ 52 + f) * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : x.toBits.toNat * 2 ^ 52 < 2 ^ 52 * 2 ^ 52 :=
      Nat.mul_lt_mul_of_pos_right (by simp only [Nat.reducePow]; omega) (by positivity)
    have h3 : 2 ^ (e - 1) < 2 ^ 52 := by
      have : 2 ^ 52 * 2 ^ (e - 1) < 2 ^ 52 * 2 ^ 52 := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have hwN : w.toNat = e * 4503599627370496 + f := by
    rw [← he, ← hf]
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow]
    simp only [Nat.reducePow] at hwlt
    omega
  have hwv' := Library.Numerics.Float64.Log.LogMain.normal_form w hws (by rw [he]; exact he1)
  rw [he, hf] at hwv'
  have hxv : value x.toBits = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ (((e : Int) - 52) - 1075) := by
    have h52 : (2 : ℝ) ^ (((e : Int) - 52) - 1075) * 2 ^ 52 = (2 : ℝ) ^ ((e : Int) - 1075) := by
      rw [← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    have h2 : value x.toBits * 2 ^ 52 = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ ((e : Int) - 1075) := by
      rw [← hwv, hwv']
    rw [← h52, ← mul_assoc] at h2
    exact mul_right_cancel₀ (by positivity) h2
  rw [hxv]
  have hsh : ((52 : UInt64) <<< 52).toNat = 52 * 4503599627370496 := by decide
  apply Log2CoreStep.core2_within (w - (52 : UInt64) <<< 52) ((e : Int) - 52) f (by omega) (by omega) hflt
  · rw [UInt64.toNat_sub, hsh, hwN]
    have : e * 4503599627370496 + f < 18446744073709551616 := by omega
    push_cast
    omega
  · left
    rw [← hxv]
    have h1 : value x.toBits < value (0x0010000000000000 : UInt64) :=
      F64PositiveOrder.value_strict (by decide) (by
        show x.toBits.toNat < 4503599627370496
        exact hhi)
    have h2 : PolyBound.ratOfWord 0x0010000000000000 = 1 / 2 ^ 1022 := by decide +kernel
    have h3 : value (0x0010000000000000 : UInt64) = 1 / 2 ^ 1022 := by
      rw [← PolyBound.ratOfWord_cast, h2]
      norm_num
    rw [h3] at h1
    have : (1 : ℝ) / 2 ^ 1022 ≤ 2008239 / 2097152 := by norm_num
    linarith

#print axioms bound2_values
#print axioms log2_normal_within
#print axioms log2_subnormal_within

end Library.Numerics.Float64.Log2.Log2Main
