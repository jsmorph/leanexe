import Verified.Examples.SinpiTinyWords

/-!
The head and tail of `x 2 ^ 53` in `Sinpi.piTiny`, for a finite word `x` below 1 in magnitude:
`A = x 2 ^ 53` and the head `H` are exact, the tail `L = A - H` is exact, `|H| ≤ |A|`, and
`|L| ≤ |A| / 2 ^ 20 + 2 ^ -989`, the second term for subnormal `x`.  The head has at most 21
significant bits, so that its product with `pi_hi` is exact.
-/

namespace Verified.Examples.SinpiTinySplit

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanBigWords SinpiProduct SinpiTinyWords

set_option exponentiation.threshold 1200

/-- The tail bound: `m mod 2 ^ 32` against `m`, for a normal `m` or the subnormal scale. -/
theorem tail_le (m k : Nat) (h : k = 0 ∨ 2 ^ 52 ≤ m) :
    ((m % 2 ^ 32 : ℕ) : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) ≤
      (m : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) / 2 ^ 20 + 1 / 2 ^ 989 := by
  have hP : (0 : ℝ) < 2 ^ (k + 53) / 2 ^ 1074 := by positivity
  have hd : ((m % 2 ^ 32 : ℕ) : ℝ) < 2 ^ 32 := by exact_mod_cast Nat.mod_lt m (by positivity)
  have h0 : (0 : ℝ) ≤ (m : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) / 2 ^ 20 := by positivity
  rcases h with hk | hm
  · subst hk
    have e : (2 : ℝ) ^ 32 * (2 ^ (0 + 53) / 2 ^ 1074) = 1 / 2 ^ 989 := by norm_num
    have := mul_le_mul_of_nonneg_right hd.le hP.le
    linarith
  · have hm' : (2 : ℝ) ^ 52 ≤ m := by exact_mod_cast hm
    have h1 : ((m % 2 ^ 32 : ℕ) : ℝ) * 2 ^ 20 ≤ m := by
      have : (2 : ℝ) ^ 32 * 2 ^ 20 = 2 ^ 52 := by norm_num
      nlinarith
    have h2 : ((m % 2 ^ 32 : ℕ) : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) * 2 ^ 20 ≤
        (m : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hP.le]
    have h3 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 20)).mpr h2
    have h4 : (0 : ℝ) ≤ 1 / 2 ^ 989 := by positivity
    linarith

/-- The difference of two words of one sign with magnitudes `m 2 ^ j` and its truncation. -/
theorem tail_grid (A H : UInt64) (sg : Bool) (m j : Nat) (hAs : Wasm.IEEE64.sign A = sg)
    (hHs : Wasm.IEEE64.sign H = sg) (hAm : Wasm.IEEE64.scaledMagnitude A = m * 2 ^ j)
    (hHm : Wasm.IEEE64.scaledMagnitude H = m / 2 ^ 32 * 2 ^ 32 * 2 ^ j) :
    ∃ z : Int, Wasm.IEEE64.scaledValue A - Wasm.IEEE64.scaledValue H = z * 2 ^ j ∧
      z.natAbs = m % 2 ^ 32 := by
  have hsplit : m / 2 ^ 32 * 2 ^ 32 * 2 ^ j + m % 2 ^ 32 * 2 ^ j = m * 2 ^ j := by
    rw [← add_mul, show m / 2 ^ 32 * 2 ^ 32 + m % 2 ^ 32 = m by omega]
  unfold Wasm.IEEE64.scaledValue
  dsimp only
  rw [hAs, hHs, hAm, hHm, ← hsplit]
  cases sg
  · refine ⟨((m % 2 ^ 32 : ℕ) : ℤ), ?_, Int.natAbs_natCast _⟩
    simp only [Bool.false_eq_true, ite_false]
    push_cast
    ring
  · refine ⟨-((m % 2 ^ 32 : ℕ) : ℤ), ?_, by rw [Int.natAbs_neg, Int.natAbs_natCast]⟩
    simp only [ite_true]
    push_cast
    ring

theorem split_spec (b : UInt64) (hbf : Finite b) (hb1 : |value b| < 1) :
    Finite (Wasm.IEEE64.mul b P53) ∧ Finite (Wasm.IEEE64.mul (b &&& mask) P53) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul b P53) (Wasm.IEEE64.mul (b &&& mask) P53)) ∧
      value (Wasm.IEEE64.mul b P53) = value b * 2 ^ 53 ∧
      value (Wasm.IEEE64.sub (Wasm.IEEE64.mul b P53) (Wasm.IEEE64.mul (b &&& mask) P53)) =
        value (Wasm.IEEE64.mul b P53) - value (Wasm.IEEE64.mul (b &&& mask) P53) ∧
      |value (Wasm.IEEE64.mul (b &&& mask) P53)| ≤ |value (Wasm.IEEE64.mul b P53)| ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul b P53) (Wasm.IEEE64.mul (b &&& mask) P53))| ≤
        |value (Wasm.IEEE64.mul b P53)| / 2 ^ 20 + 1 / 2 ^ 989 ∧
      ∃ q : Nat, q < 2 ^ 21 ∧ Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul (b &&& mask) P53) =
        q * 2 ^ (Wasm.IEEE64.exponent b - 1 + 85) := by
  obtain ⟨m, hm53, hmb, hmt, hnorm⟩ := trunc_mag b
  have he := exp_small b hb1
  have htf := trunc_finite b hbf
  obtain ⟨-, hts, -⟩ := trunc_fields b
  obtain ⟨hAf, hAv, hAm, hAs⟩ := mul_up b hbf m (Wasm.IEEE64.exponent b - 1) hmb hm53 (by omega)
  obtain ⟨hHf, hHv, hHm, hHs⟩ := mul_up (b &&& mask) htf (m / 2 ^ 32 * 2 ^ 32)
    (Wasm.IEEE64.exponent b - 1) hmt (by omega) (by omega)
  rw [hts] at hHs
  set k := Wasm.IEEE64.exponent b - 1 with hk
  set A := Wasm.IEEE64.mul b P53 with hA
  set H := Wasm.IEEE64.mul (b &&& mask) P53 with hH
  obtain ⟨z, hdiff, hza⟩ := tail_grid A H _ m (k + 53) hAs hHs hAm hHm
  obtain ⟨hLf, hLs⟩ := F64GridExact.sub_grid_exact A H hAf hHf z (k + 53) hdiff
    (by rw [hza]; omega) (by omega)
  have hLv : value (Wasm.IEEE64.sub A H) = value A - value H := by
    simp only [TrigSmall.value_of_scaled]
    rw [hLs, Int.cast_sub, sub_div]
  have hP : (0 : ℝ) < 2 ^ (k + 53) / 2 ^ 1074 := by positivity
  have hAa : |value A| = (m : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) := by
    rw [TrigNearest.abs_value, hAm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc]
  have hHa : |value H| = ((m / 2 ^ 32 * 2 ^ 32 : ℕ) : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) := by
    rw [TrigNearest.abs_value, hHm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc]
  have hLa : |value (Wasm.IEEE64.sub A H)| =
      ((m % 2 ^ 32 : ℕ) : ℝ) * (2 ^ (k + 53) / 2 ^ 1074) := by
    rw [TrigSmall.value_of_scaled, hLs, hdiff, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 53)), ← Int.cast_abs, Int.abs_eq_natAbs,
      hza, Int.cast_natCast, mul_div_assoc]
  refine ⟨hAf, hHf, hLf, hAv, hLv, ?_, ?_, ⟨m / 2 ^ 32, by omega, ?_⟩⟩
  · rw [hHa, hAa]
    have : ((m / 2 ^ 32 * 2 ^ 32 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_mul_le_self m _
    exact mul_le_mul_of_nonneg_right this hP.le
  · rw [hLa, hAa]
    refine tail_le m k ?_
    by_cases h0 : Wasm.IEEE64.exponent b = 0
    · left; omega
    · right; exact hnorm h0
  · rw [hHm]
    ring

#print axioms tail_le
#print axioms tail_grid
#print axioms split_spec

end Verified.Examples.SinpiTinySplit
