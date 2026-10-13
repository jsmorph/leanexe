import Verified.Examples.TgammaAccShift
import LeanExe.ProofKit.F64Admissibility
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64NearestScale

/-!
The loop of `Tgamma.accurate` for `x < j`, which multiplies the factors `x, x + 1, …` and divides
the product by `2 ^ 500` whenever its high part exceeds `2 ^ 518`.  `prod_small` bounds the product
of the factors below 1 in magnitude: of the factors `x + i`, only the two next to the integer part
of `-x` lie below 1, and their product is at least `2 ^ -55` when `x` lies at least `2 ^ -54` from
every integer.  `scale_down` shows that the division of the high part by `2 ^ 500` is exact.
-/

namespace Verified.Examples.TgammaAccUp
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccShift

set_option exponentiation.threshold 4096

/-- The factor `min 1 |v + n|`. -/
noncomputable def g (v : ℝ) (n : ℤ) : ℝ := min 1 |v + n|

/-- **The factors below 1.**  For `v` at least `2 ^ -54` from every integer, the product of
`min 1 |v + i|` over `i ≤ m` is at least `2 ^ -55`. -/
theorem prod_small (v : ℝ) (hv : ∀ n : ℤ, 1 / 2 ^ 54 ≤ |v + n|) (m : ℕ) :
    1 / 2 ^ 55 ≤ ∏ i ∈ Finset.range (m + 1), g v i := by
  set a : ℤ := ⌊-v⌋ with ha
  have hfl := Int.floor_le (-v)
  have hlt := Int.lt_floor_add_one (-v)
  rw [← ha] at hfl hlt
  have hg1 : ∀ n : ℤ, g v n ≤ 1 := fun n => min_le_left _ _
  have hg0 : ∀ n : ℤ, 0 ≤ g v n := fun n => le_min zero_le_one (abs_nonneg _)
  have hone : ∀ n : ℤ, n ≠ a → n ≠ a + 1 → g v n = 1 := by
    intro n h1 h2
    apply min_eq_left
    rcases lt_or_gt_of_ne h1 with h | h
    · have : (n : ℝ) ≤ a - 1 := by exact_mod_cast (show n ≤ a - 1 by omega)
      rw [abs_of_neg (by linarith)]; linarith
    · have : (a : ℝ) + 2 ≤ n := by exact_mod_cast (show a + 2 ≤ n by omega)
      rw [abs_of_pos (by linarith)]; linarith
  -- the product after `m` factors
  have key : ∀ m : ℕ, (if a ≤ m then g v a else 1) * (if a + 1 ≤ m then g v (a + 1) else 1) ≤
      ∏ i ∈ Finset.range (m + 1), g v i := by
    intro m
    induction m with
    | zero =>
      simp only [zero_add, Finset.prod_range_one, Nat.cast_zero]
      by_cases ha0 : a = 0
      · rw [if_pos (by omega), if_neg (by omega), mul_one, ha0]
      · by_cases ha1 : a = -1
        · rw [if_pos (by omega), if_pos (by omega)]
          have : g v (a + 1) = g v 0 := by rw [ha1]; norm_num
          rw [this]
          nlinarith [hg1 a, hg0 a, hg0 0]
        · have h0 : g v 0 = 1 := hone 0 (by omega) (by omega)
          rw [h0]
          split_ifs <;> nlinarith [hg1 a, hg1 (a + 1), hg0 a, hg0 (a + 1)]
    | succ m ih =>
      rw [Finset.prod_range_succ]
      have hP0 : 0 ≤ ∏ i ∈ Finset.range (m + 1), g v i :=
        Finset.prod_nonneg (fun i _ => hg0 i)
      have hcast : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      by_cases h0 : (m : ℤ) + 1 = a
      · rw [if_neg (by omega), if_neg (by omega), one_mul] at ih
        rw [if_pos (by omega), if_neg (by omega), mul_one, ← h0]
        nlinarith [hg0 ((m : ℤ) + 1)]
      · by_cases h1 : (m : ℤ) + 1 = a + 1
        · rw [if_pos (by omega), if_neg (by omega), mul_one] at ih
          rw [if_pos (by omega), if_pos (by omega), h1]
          exact mul_le_mul_of_nonneg_right ih (hg0 _)
        · rw [hone _ h0 h1, mul_one]
          have e1 : (a ≤ (m : ℤ) + 1) ↔ (a ≤ (m : ℤ)) := by omega
          have e2 : (a + 1 ≤ (m : ℤ) + 1) ↔ (a + 1 ≤ (m : ℤ)) := by omega
          simp only [e1, e2]
          exact ih
  -- the two special factors
  have ht0 : 0 < v + a + 1 := by linarith
  have ht1 : v + a + 1 ≤ 1 := by linarith
  have hga : g v a = -(v + a) := by
    have h := hv a
    have hn : v + a ≤ 0 := by linarith
    rw [g, abs_of_nonpos hn]
    exact min_eq_right (by linarith)
  have hgb : g v (a + 1) = v + a + 1 := by
    rw [g]; push_cast
    rw [abs_of_pos (by linarith), min_eq_right (by linarith)]
    ring
  have hA := hv a
  have hB := hv (a + 1)
  push_cast at hB
  rw [abs_of_pos (by linarith)] at hB
  rw [abs_of_nonpos (by linarith)] at hA
  have hprod : 1 / 2 ^ 55 ≤ g v a * g v (a + 1) := by
    rw [hga, hgb]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ v + a + 1 - 1 / 2 ^ 54)
      (by linarith : (0 : ℝ) ≤ -(v + a) - 1 / 2 ^ 54)]
  refine le_trans hprod (le_trans ?_ (key m))
  split_ifs <;> nlinarith [hg1 a, hg1 (a + 1), hg0 a, hg0 (a + 1)]

/-- **Division of the high part by `2 ^ 500`** is exact above `2 ^ 518`. -/
theorem scale_down (w : Float) (hw : Finite w.toBits) (hlo : 2 ^ 518 < |value w.toBits|) :
    Finite (w * Float.ofBits 0x20B0000000000000).toBits ∧
      value (w * Float.ofBits 0x20B0000000000000).toBits = value w.toBits / 2 ^ 500 := by
  have hcw : Wasm.IEEE64.isFinite 0x20B0000000000000 = true := by decide
  have hc : (Float.ofBits 0x20B0000000000000).toBits = Wasm.IEEE64.encodeFinite false 523 0 := by
    rw [TgammaWords.ofBits_bits _ hcw]; decide
  have hcf := TgammaWords.ofBits_finite _ hcw
  have he : 1541 ≤ Wasm.IEEE64.exponent w.toBits := by
    by_contra hn
    have := F64Magnitude.magnitude_lt w.toBits 1541 518 (by norm_num) (by norm_num) (by omega)
    rw [show ((2 : ℝ) ^ (518 : ℤ)) = 2 ^ 518 by norm_num] at this
    linarith
  have hb := F64Admissibility.finite_exponent_bound w.toBits hw
  rw [F64Bits.toBits_mul, F64NearestScale.mul_comm_finite _ _ hw hcf, hc]
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite 523 w.toBits (by norm_num) (by norm_num) hw
    (by omega) (by omega) (by omega)
  refine ⟨hf, ?_⟩
  rw [hv]
  norm_num
  ring

#print axioms prod_small
#print axioms scale_down

end Verified.Examples.TgammaAccUp
