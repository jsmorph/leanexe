import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64SignedRounding
import LeanExe.ProofKit.F64Sign

/-!
A finite word whose value lies within `11/8` units of roundoff of a real number, relative to the
number, lies within one representable step of the number's nearest-even reference.  A computed
result is the rounding of an exact sum, which contributes one unit of roundoff, so the bound
leaves `3/8` of a unit for the error of that sum.  The proof places the word in its binade and
applies `F64FullStep.one_step_binades` to the binade of the number or the one below it.
-/

namespace LeanExe.ProofKit.F64RelativeStep
open CodeLib.IEEE64 F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

/-- The power of two at the start of binade `e`, in natural powers. -/
theorem zpow_eq (e : Nat) (he : 1 ≤ e) :
    (2 : ℝ) ^ ((e : Int) - 1023) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) (e - 1), ← zpow_natCast (2 : ℝ) 1022,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

/-- The value of the word at the start of binade `e`. -/
theorem boundary_pow (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2048) :
    value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [← zpow_eq e he1]
  exact F64NearestBinade.boundary_power e ((e : Int) - 1023) he1 he2 (by ring)

/-- A finite word within `11/8` units of roundoff of a positive number `y`, relative to `y`, lies
within one step of the nonnegative nearest-even reference of `y`. -/
theorem one_step_relative (y : ℝ) (c : UInt64) (hcf : Finite c)
    (hy : 1 / (2 : ℝ) ^ 1000 ≤ y)
    (hc : |value c - y| ≤ 11 / 8 * unitRoundoff64 * y) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  norm_num [unitRoundoff64] at hcl hcu
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hy' : (1 : ℝ) / 2 ^ 1000 ≤ y := hy
  norm_num at hy'
  have hcy : y / 2 ≤ value c := by linarith
  have hnorm := normal_of_value c (by norm_num; linarith)
  set a := Wasm.IEEE64.exponent c with ha
  have hfin : a ≠ 2047 := by
    have h := hcf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    exact h
  have hlt : a < 2048 := Nat.mod_lt _ (by norm_num)
  have ha22 : 22 ≤ a := by
    refine exponent_ge_of_value c 22 (by norm_num) ?_
    norm_num
    linarith
  set P : ℝ := (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 with hP
  have hPpos : 0 < P := by positivity
  have hcP : P ≤ value c := by
    rw [hP, ← zpow_eq a hnorm.1]
    exact value_ge_of_exponent c a ((a : Int) - 1023) hnorm.1 hlt (by ring) hnorm.2 le_rfl
  have hpow1 : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
    rw [show a = (a - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hc2P : value c < 2 * P := by
    have h := magnitude_lt c (a + 1) (((a + 1 : Nat) : Int) - 1023) (by omega) (by ring)
      (by omega)
    rw [zpow_eq (a + 1) (by omega), Nat.add_sub_cancel, hpow1] at h
    rw [hP]
    have h2 : 2 * (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 = 2 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022) := by
      ring
    rw [h2] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hc63 : c.toNat < 2 ^ 63 := by
    have h := hnorm.2
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at h
    exact h
  have hbA : value (UInt64.ofNat (a * 2 ^ 52)) = P := boundary_pow a hnorm.1 hlt
  have hbB1 : value (UInt64.ofNat ((a + 1) * 2 ^ 52)) = 2 * P := by
    rw [boundary_pow (a + 1) (by omega) (by omega), Nat.add_sub_cancel, hpow1, hP]
    ring
  rcases le_or_gt P y with hPy | hyP
  · -- `y` in the binade of `c` or above it.
    have hspace : (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074 = P / (2 : ℝ) ^ 52 := by
      rw [hP]
      field_simp
    have he : |value c - y| < 3 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) / 2 := by
      rw [hspace, abs_lt]
      constructor <;> linarith
    rcases Nat.lt_or_ge (a + 2) 2047 with hb | hb
    · have hbB : value (UInt64.ofNat ((a + 2) * 2 ^ 52)) = 4 * P := by
        rw [boundary_pow (a + 2) (by omega) (by omega), hP,
          show a + 2 - 1 = (a - 1) + 2 by omega, pow_add]
        ring
      exact F64FullStep.one_step_binades y c a (a + 2) (by omega) (by omega)
        (by rw [hbA]; exact hPy) (fun _ => by rw [hbB]; linarith) hc63 (by rw [hbA]; exact hcP)
        (by rw [hbB]; linarith) he
    · have hbB : value (UInt64.ofNat (2047 * 2 ^ 52)) = (2 : ℝ) ^ 1024 := by
        rw [boundary_pow 2047 (by norm_num) (by norm_num)]
        norm_num
      have hP1 : 2 * P ≤ (2 : ℝ) ^ 1024 := by
        have h1 : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ 2046 := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [hpow1] at h1
        rw [hP, mul_div_assoc', div_le_iff₀ (by positivity)]
        calc 2 * (2 : ℝ) ^ (a - 1) ≤ 2 ^ 2046 := h1
          _ = 2 ^ 1024 * 2 ^ 1022 := by norm_num
      exact F64FullStep.one_step_binades y c a 2047 (by omega) le_rfl
        (by rw [hbA]; exact hPy) (fun h => absurd h (lt_irrefl _)) hc63
        (by rw [hbA]; exact hcP) (by rw [hbB]; linarith) he
  · -- `y` in the binade below that of `c`.
    have hspace : (2 : ℝ) ^ (a - 1 - 1) / (2 : ℝ) ^ 1074 = P / (2 : ℝ) ^ 53 := by
      rw [hP]
      have h2 : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ (a - 1 - 1) := by
        rw [show a - 1 = (a - 1 - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [h2]
      field_simp
    have he : |value c - y| < 3 * ((2 : ℝ) ^ (a - 1 - 1) / (2 : ℝ) ^ 1074) / 2 := by
      rw [hspace, abs_lt]
      constructor <;> linarith
    have hbA' : value (UInt64.ofNat ((a - 1) * 2 ^ 52)) = P / 2 := by
      rw [boundary_pow (a - 1) (by omega) (by omega), hP]
      have h2 : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ (a - 1 - 1) := by
        rw [show a - 1 = (a - 1 - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [h2]
      ring
    exact F64FullStep.one_step_binades y c (a - 1) (a + 1) (by omega) (by omega)
      (by rw [hbA']; linarith) (fun _ => by rw [hbB1]; linarith) hc63
      (by rw [hbA']; linarith) (by rw [hbB1]; linarith) he

theorem negate_negate (w : UInt64) : Wasm.IEEE64.negate (Wasm.IEEE64.negate w) = w := by
  obtain ⟨he, hf, hs⟩ := F64Sign.fields_negate w
  have hw := w.toNat_lt
  conv_lhs => rw [Wasm.IEEE64.negate]
  rw [he, hf, hs, Bool.not_not]
  apply UInt64.toNat_inj.mp
  simp only [Wasm.IEEE64.encodeFinite, Wasm.IEEE64.sign, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, UInt64.toNat_ofNat']
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

/-- A finite word within `11/8` units of roundoff of `y`, relative to `|y|`, lies within one
step of the signed nearest-even reference of `y`. -/
theorem within_one_relative (y : ℝ) (c : UInt64) (hcf : Finite c)
    (hy : 1 / (2 : ℝ) ^ 1000 ≤ |y|)
    (hc : |value c - y| ≤ 11 / 8 * unitRoundoff64 * |y|) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hu : (0 : ℝ) < unitRoundoff64 := by norm_num [unitRoundoff64]
  rcases lt_or_ge y 0 with hneg | hpos
  · rw [abs_of_neg hneg] at hy hc
    have hcl := (abs_le.mp hc).2
    norm_num [unitRoundoff64] at hcl
    have hcn : value c < 0 := by
      have : (0 : ℝ) < 1 / 2 ^ 1000 := by positivity
      linarith
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude c := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h | h
      · exfalso
        have hz : value c = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h]
          split <;> simp
        linarith
      · exact h
    have hs : Wasm.IEEE64.sign c = true := (sign_value c hmag).mpr hcn
    obtain ⟨hnf, hnv⟩ := negate_value c hcf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate c) = false := by
      have h := (F64Sign.fields_negate c).2.2
      rw [hs] at h
      exact h
    have hstep := one_step_relative (-y) (Wasm.IEEE64.negate c) hnf hy (by
      rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]
      exact hc)
    have h := F64SignedRounding.within_of_neg 1 y hneg (Wasm.IEEE64.negate c)
      (lt_limit_of_finite _ hnf hns).le hstep.1 hstep.2
    rwa [negate_negate] at h
  · have hy0 : 0 < y := by
      rw [abs_of_nonneg hpos] at hy
      exact lt_of_lt_of_le (by positivity) hy
    rw [abs_of_pos hy0] at hy hc
    have hcl := (abs_le.mp hc).1
    norm_num [unitRoundoff64] at hcl
    have hcp : 0 < value c := by linarith
    have hs : Wasm.IEEE64.sign c = false := by
      have hmag : 0 < Wasm.IEEE64.scaledMagnitude c := by
        rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h | h
        · exfalso
          have hz : value c = 0 := by
            simp only [value, Wasm.IEEE64.scaledValue, h]
            split <;> simp
          linarith
        · exact h
      cases h : Wasm.IEEE64.sign c
      · rfl
      · exact absurd ((sign_value c hmag).mp h) (not_lt.mpr hcp.le)
    have hstep := one_step_relative y c hcf hy hc
    exact F64SignedRounding.within_of_nonneg 1 y hy0.le c (lt_limit_of_finite c hcf hs).le
      hstep.1 hstep.2

#print axioms zpow_eq
#print axioms boundary_pow
#print axioms one_step_relative
#print axioms negate_negate
#print axioms within_one_relative

end LeanExe.ProofKit.F64RelativeStep
