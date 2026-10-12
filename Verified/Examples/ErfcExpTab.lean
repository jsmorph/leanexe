import Verified.Examples.Erfc
import LeanExe.ProofKit.PolyBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Verified.Examples.ErfcCast

/-!
The tables `T1` and `T2` of `exp_1` in `Erfc`: entry `i` of `T1`, the words `2 i` and `2 i + 1` of
`Erfc.expTable`, holds `2^(i/64)`, and entry `i` of `T2`, the words `128 + 2 i` and `129 + 2 i`,
holds `2^(i/4096)`, as double-doubles.  For an entry `t = a/2^120` the kernel checks
`(a (2^95 - 1))^n ≤ 2^(i + 215 n) ≤ (a (2^95 + 1))^n` in natural numbers (`tabOK`), and since
`x ↦ x^n` is increasing on the positive reals, `tab_sound` concludes that `t` lies within
`2^-95 t` of `exp (i log 2 / n)`.
-/

namespace Verified.Examples.ErfcExpTab

open LeanExe.ProofKit PolyBound Real

/-- Entry `i` of the double-double table at word `base`, as a rational. -/
def tabV (base i : ℕ) : ℚ :=
  ratOfWord Erfc.expTable[base + 2 * i]! + ratOfWord Erfc.expTable[base + 2 * i + 1]!

/-- The kernel's check of an entry approximating `2^(i/n)`. -/
def tabOK (base n i : ℕ) : Bool :=
  (tabV base i * 2 ^ 120).den == 1 && decide (0 < (tabV base i * 2 ^ 120).num) &&
    decide (((tabV base i * 2 ^ 120).num.toNat * (2 ^ 95 - 1)) ^ n ≤ 2 ^ (i + n * 215)) &&
    decide (2 ^ (i + n * 215) ≤ ((tabV base i * 2 ^ 120).num.toNat * (2 ^ 95 + 1)) ^ n)

theorem tab1_ok : ∀ i < 64, tabOK 0 64 i = true := by decide +kernel

theorem tab2_ok_a : ∀ i < 16, tabOK 128 4096 i = true := by decide +kernel
theorem tab2_ok_b : ∀ i < 16, tabOK 128 4096 (i + 16) = true := by decide +kernel
theorem tab2_ok_c : ∀ i < 16, tabOK 128 4096 (i + 32) = true := by decide +kernel
theorem tab2_ok_d : ∀ i < 16, tabOK 128 4096 (i + 48) = true := by decide +kernel

theorem tab2_ok (i : ℕ) (hi : i < 64) : tabOK 128 4096 i = true := by
  rcases (show i < 16 ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ 48 ≤ i by omega) with
    h | h | h | h
  · exact tab2_ok_a i h
  · have := tab2_ok_b (i - 16) (by omega); rwa [show i - 16 + 16 = i by omega] at this
  · have := tab2_ok_c (i - 32) (by omega); rwa [show i - 32 + 32 = i by omega] at this
  · have := tab2_ok_d (i - 48) (by omega); rwa [show i - 48 + 48 = i by omega] at this

/-- An entry that passes the check lies within `2^-95` of `2^(i/n)` relative to itself. -/
theorem tab_sound (base n i : ℕ) (hn : 1 ≤ n) (h : tabOK base n i = true) :
    |(tabV base i : ℝ) - exp (i * log 2 / n)| ≤ 1 / 2 ^ 95 * tabV base i := by
  simp only [tabOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hden, hpos⟩, hlo⟩, hhi⟩ := h
  set N := tabV base i * 2 ^ 120 with hN
  set a := N.num.toNat with ha
  have hNa : (N : ℝ) = (a : ℝ) := by
    have h1 : (N : ℚ) = (N.num : ℚ) := by
      rw [← Rat.num_div_den N, hden]; simp
    have h2 : ((N.num : ℤ) : ℝ) = (a : ℝ) := by
      rw [ha]; qc (Int.toNat_of_nonneg hpos.le).symm
    rw [show (N : ℝ) = ((N : ℚ) : ℝ) from rfl, h1]; push_cast; exact h2
  have ht : (tabV base i : ℝ) = a / 2 ^ 120 := by
    rw [← hNa, hN]; push_cast; field_simp
  have hn0 : n ≠ 0 := by omega
  set r := exp (i * log 2 / n) with hr
  have hr0 : 0 < r := exp_pos _
  have hrn : r ^ n = 2 ^ i := by
    rw [hr, ← exp_nat_mul, show (n : ℝ) * (i * log 2 / n) = i * log 2 by field_simp,
      ← log_rpow (by norm_num : (0 : ℝ) < 2), exp_log (by positivity), rpow_natCast]
  have hloR : ((a : ℝ) * (2 ^ 95 - 1) / 2 ^ 215) ^ n ≤ r ^ n := by
    rw [hrn, div_pow]
    have hc : ((a * (2 ^ 95 - 1) : ℕ) : ℝ) = (a : ℝ) * (2 ^ 95 - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by norm_num), Nat.cast_pow]; norm_num
    have := (Nat.cast_le (α := ℝ)).mpr hlo
    rw [Nat.cast_pow, Nat.cast_pow, hc, Nat.cast_ofNat] at this
    rw [div_le_iff₀ (by positivity), ← pow_mul, ← pow_add, mul_comm 215 n]
    exact this
  have hhiR : r ^ n ≤ ((a : ℝ) * (2 ^ 95 + 1) / 2 ^ 215) ^ n := by
    rw [hrn, div_pow]
    have hc : ((a * (2 ^ 95 + 1) : ℕ) : ℝ) = (a : ℝ) * (2 ^ 95 + 1) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]; norm_num
    have := (Nat.cast_le (α := ℝ)).mpr hhi
    rw [Nat.cast_pow, Nat.cast_pow, hc, Nat.cast_ofNat] at this
    rw [le_div_iff₀ (by positivity), ← pow_mul, ← pow_add, mul_comm 215 n]
    exact this
  have k1 : (a : ℝ) * (2 ^ 95 - 1) / 2 ^ 215 ≤ r :=
    (pow_le_pow_iff_left₀ (by positivity) hr0.le hn0).mp hloR
  have k2 : r ≤ (a : ℝ) * (2 ^ 95 + 1) / 2 ^ 215 :=
    (pow_le_pow_iff_left₀ hr0.le (by positivity) hn0).mp hhiR
  rw [ht, abs_le]
  have e1 : (a : ℝ) * (2 ^ 95 - 1) / 2 ^ 215 = a / 2 ^ 120 - 1 / 2 ^ 95 * (a / 2 ^ 120) := by
    field_simp
  have e2 : (a : ℝ) * (2 ^ 95 + 1) / 2 ^ 215 = a / 2 ^ 120 + 1 / 2 ^ 95 * (a / 2 ^ 120) := by
    field_simp
  constructor <;> linarith

#print axioms tab1_ok
#print axioms tab2_ok
#print axioms tab_sound

end Verified.Examples.ErfcExpTab
