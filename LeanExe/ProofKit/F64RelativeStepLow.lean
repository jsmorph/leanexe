import LeanExe.ProofKit.F64RelativeStepWide

/-!
`F64RelativeStepWide.within_one_wide` extended below `2 ^ -1000`: a finite word within `47/32`
units of roundoff of `y`, relative to the larger of `|y|` and `2 ^ -1021`, lies within one step of
the nearest-even reference of `y` when `2 ^ -1073 ≤ |y|`.  From `2 ^ -1021` on the proof is that
of `within_one_wide`.  Below `2 ^ -1021` the error is less than one and a half spacings of the
subnormal binade, and `F64FullStep.one_step_binades` applies to binades 0 to 3.
-/

namespace LeanExe.ProofKit.F64RelativeStepLow

open CodeLib.IEEE64 F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

/-- A word with a positive value has sign 0. -/
theorem pos_word (c : UInt64) (h : 0 < value c) :
    Wasm.IEEE64.sign c = false ∧ c.toNat < 2 ^ 63 := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude c := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h' | h'
    · exfalso
      have hz : value c = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h']
        split <;> simp
      linarith
    · exact h'
  have hs : Wasm.IEEE64.sign c = false := by
    cases hc : Wasm.IEEE64.sign c
    · rfl
    · exact absurd ((sign_value c hmag).mp hc) (not_lt.mpr h.le)
  refine ⟨hs, ?_⟩
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
  exact hs

/-- `F64RelativeStepWide.one_step_wide` from `2 ^ -1021` on. -/
theorem one_step_mid (y : ℝ) (c : UInt64) (hcf : Finite c)
    (hy : 1 / (2 : ℝ) ^ 1021 ≤ y)
    (hc : |value c - y| ≤ 47 / 32 * unitRoundoff64 * y) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  norm_num [unitRoundoff64] at hcl hcu
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hy' : (1 : ℝ) / 2 ^ 1021 ≤ y := hy
  norm_num at hy'
  have hcy : y / 2 ≤ value c := by linarith
  have hnorm := normal_of_value c (by norm_num; linarith)
  set a := Wasm.IEEE64.exponent c with ha
  have hfin : a ≠ 2047 := by
    have h := hcf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    exact h
  have hlt : a < 2048 := Nat.mod_lt _ (by norm_num)
  set P : ℝ := (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 with hP
  have hPpos : 0 < P := by positivity
  have hcP : P ≤ value c := by
    rw [hP, ← F64RelativeStep.zpow_eq a hnorm.1]
    exact value_ge_of_exponent c a ((a : Int) - 1023) hnorm.1 hlt (by ring) hnorm.2 le_rfl
  have hpow1 : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
    rw [show a = (a - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hc2P : value c < 2 * P := by
    have h := magnitude_lt c (a + 1) (((a + 1 : Nat) : Int) - 1023) (by omega) (by ring)
      (by omega)
    rw [F64RelativeStep.zpow_eq (a + 1) (by omega), Nat.add_sub_cancel, hpow1] at h
    rw [hP]
    have h2 : 2 * (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 =
        2 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022) := by
      ring
    rw [h2] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hc63 : c.toNat < 2 ^ 63 := by
    have h := hnorm.2
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at h
    exact h
  have hbA : value (UInt64.ofNat (a * 2 ^ 52)) = P := F64RelativeStep.boundary_pow a hnorm.1 hlt
  have hbB1 : value (UInt64.ofNat ((a + 1) * 2 ^ 52)) = 2 * P := by
    rw [F64RelativeStep.boundary_pow (a + 1) (by omega) (by omega), Nat.add_sub_cancel, hpow1, hP]
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
        rw [F64RelativeStep.boundary_pow (a + 2) (by omega) (by omega), hP,
          show a + 2 - 1 = (a - 1) + 2 by omega, pow_add]
        ring
      exact F64FullStep.one_step_binades y c a (a + 2) (by omega) (by omega)
        (by rw [hbA]; exact hPy) (fun _ => by rw [hbB]; linarith) hc63 (by rw [hbA]; exact hcP)
        (by rw [hbB]; linarith) he
    · have hbB : value (UInt64.ofNat (2047 * 2 ^ 52)) = (2 : ℝ) ^ 1024 := by
        rw [F64RelativeStep.boundary_pow 2047 (by norm_num) (by norm_num)]
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
  · -- `y` in the binade below that of `c`, which is binade 3 or above.
    have ha3 : 3 ≤ a := by
      by_contra h
      have h2 : (2 : ℝ) ^ (a - 1) ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : P ≤ 2 ^ 1 / (2 : ℝ) ^ 1022 := div_le_div_of_nonneg_right h2 (by positivity)
      have h4 : (2 : ℝ) ^ 1 / 2 ^ 1022 = 1 / 2 ^ 1021 := by norm_num
      linarith
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
      rw [F64RelativeStep.boundary_pow (a - 1) (by omega) (by omega), hP]
      have h2 : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ (a - 1 - 1) := by
        rw [show a - 1 = (a - 1 - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [h2]
      ring
    exact F64FullStep.one_step_binades y c (a - 1) (a + 1) (by omega) (by omega)
      (by rw [hbA']; linarith) (fun _ => by rw [hbB1]; linarith) hc63
      (by rw [hbA']; linarith) (by rw [hbB1]; linarith) he

/-- Below `2 ^ -1021`: an error under one and a half spacings of the subnormal binade. -/
theorem one_step_sub (y : ℝ) (c : UInt64) (hc63 : c.toNat < 2 ^ 63) (hy0 : 0 ≤ y)
    (hy : y < 1 / 2 ^ 1021) (hc : |value c - y| < 3 / 2 * (1 / 2 ^ 1074)) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hs : Wasm.IEEE64.sign c = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    exact hc63
  have hc0 : 0 ≤ value c := by
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Int.cast_natCast]
    positivity
  have hb3 : value (UInt64.ofNat (3 * 2 ^ 52)) = 1 / 2 ^ 1020 := by
    rw [F64RelativeStep.boundary_pow 3 (by norm_num) (by norm_num)]
    norm_num
  have hca := abs_lt.mp hc
  have e1 : (1 : ℝ) / 2 ^ 1021 + 3 / 2 * (1 / 2 ^ 1074) ≤ 1 / 2 ^ 1020 := by norm_num
  exact F64FullStep.one_step_binades y c 0 3 (by norm_num) (by norm_num)
    (by rw [value_zero_boundary]; exact hy0) (fun _ => by rw [hb3]; linarith) hc63
    (by rw [value_zero_boundary]; exact hc0) (by rw [hb3]; linarith)
    (by rw [show (0 : ℕ) - 1 = 0 from rfl, pow_zero]; linarith)

/-- The two ranges for a positive number. -/
theorem one_step_low (y : ℝ) (c : UInt64) (hcf : Finite c) (hy0 : 1 / 2 ^ 1073 ≤ y)
    (hc : |value c - y| ≤ 47 / 32 * unitRoundoff64 * max y (1 / 2 ^ 1021)) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  rcases le_or_gt (1 / 2 ^ 1021) y with h | h
  · rw [max_eq_left h] at hc
    exact one_step_mid y c hcf h hc
  · rw [max_eq_right h.le, show unitRoundoff64 = 1 / 2 ^ 53 from rfl] at hc
    have hca := abs_le.mp hc
    have e1 : (47 : ℝ) / 32 * (1 / 2 ^ 53) * (1 / 2 ^ 1021) < 1 / 2 ^ 1073 := by norm_num
    have e2 : (47 : ℝ) / 32 * (1 / 2 ^ 53) * (1 / 2 ^ 1021) < 3 / 2 * (1 / 2 ^ 1074) := by
      norm_num
    obtain ⟨-, hc63⟩ := pos_word c (by linarith)
    exact one_step_sub y c hc63 (by linarith) h (by rw [abs_lt]; constructor <;> linarith)

/-- A finite word within `47/32` units of roundoff of `y`, relative to the larger of `|y|` and
`2 ^ -1021`, lies within one step of the signed nearest-even reference of `y`. -/
theorem within_low (y : ℝ) (c : UInt64) (hcf : Finite c) (hy0 : 1 / 2 ^ 1073 ≤ |y|)
    (hc : |value c - y| ≤ 47 / 32 * unitRoundoff64 * max |y| (1 / 2 ^ 1021)) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hm : 47 / 32 * unitRoundoff64 * max |y| (1 / 2 ^ 1021) < |y| := by
    rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl]
    rcases le_total |y| (1 / 2 ^ 1021) with h | h
    · rw [max_eq_right h]
      have : (47 : ℝ) / 32 * (1 / 2 ^ 53) * (1 / 2 ^ 1021) < 1 / 2 ^ 1073 := by norm_num
      linarith
    · rw [max_eq_left h]
      have : (0 : ℝ) < 1 / 2 ^ 1073 := by positivity
      linarith
  rcases lt_or_ge y 0 with hneg | hpos
  · rw [abs_of_neg hneg] at hy0 hc hm
    have hcl := (abs_le.mp hc).2
    obtain ⟨hnf, hnv⟩ := negate_value c hcf
    obtain ⟨hns, -⟩ := pos_word (Wasm.IEEE64.negate c) (by rw [hnv]; linarith)
    have hstep := one_step_low (-y) (Wasm.IEEE64.negate c) hnf hy0 (by
      rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]
      exact hc)
    have h := F64SignedRounding.within_of_neg 1 y hneg (Wasm.IEEE64.negate c)
      (lt_limit_of_finite _ hnf hns).le hstep.1 hstep.2
    rwa [F64RelativeStep.negate_negate] at h
  · rw [abs_of_nonneg hpos] at hy0 hc hm
    have hcl := (abs_le.mp hc).1
    obtain ⟨hs, -⟩ := pos_word c (by linarith)
    have hstep := one_step_low y c hcf hy0 hc
    exact F64SignedRounding.within_of_nonneg 1 y hpos c (lt_limit_of_finite c hcf hs).le
      hstep.1 hstep.2

#print axioms one_step_mid
#print axioms one_step_sub
#print axioms within_low

end LeanExe.ProofKit.F64RelativeStepLow
