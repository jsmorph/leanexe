import LeanExe.ProofKit.F64GridExact

/-!
Every real `S` with `|S| ≤ 2 ^ 1000` has a finite double within `|S|/2^53 + 2^-1075`
(`exists_near`): with `n = S 2 ^ 1074` in scaled units and `g` the least shift with
`|n| < 2 ^ (53 + g)`, the integer `K` nearest to `n/2^g` has at most 53 bits, and `K 2 ^ g` is a
word.  So a word that no finite word beats in distance to `S`, such as the result of a correctly
rounded operation, lies within that bound (`nearest_bound`).
-/

namespace LeanExe.ProofKit.F64NearReal
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem exists_near (S : ℝ) (hS : |S| ≤ 2 ^ 1000) :
    ∃ v : UInt64, Finite v ∧ |value v - S| ≤ |S| / 2 ^ 53 + 1 / 2 ^ 1075 := by
  classical
  set n := S * 2 ^ 1074 with hn
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hna : |n| = |S| * 2 ^ 1074 := by rw [hn, abs_mul, abs_of_pos hp]
  have hex : ∃ g : ℕ, |n| < 2 ^ (53 + g) := ⟨2022, by
    rw [hna]
    calc |S| * 2 ^ 1074 ≤ 2 ^ 1000 * 2 ^ 1074 := mul_le_mul_of_nonneg_right hS hp.le
      _ < 2 ^ (53 + 2022) := by norm_num⟩
  set g := Nat.find hex with hgdef
  have hg : |n| < 2 ^ (53 + g) := Nat.find_spec hex
  have hgle : g ≤ 2022 := Nat.find_min' hex (by
    rw [hna]
    calc |S| * 2 ^ 1074 ≤ 2 ^ 1000 * 2 ^ 1074 := mul_le_mul_of_nonneg_right hS hp.le
      _ < 2 ^ (53 + 2022) := by norm_num)
  have hpg : (0 : ℝ) < 2 ^ g := by positivity
  set K : ℤ := round (n / 2 ^ g) with hK
  have hKd : |n / 2 ^ g - K| ≤ 1 / 2 := abs_sub_round _
  have hq : |n / 2 ^ g| < 2 ^ 53 := by
    rw [abs_div, abs_of_pos hpg, div_lt_iff₀ hpg, ← pow_add]
    exact hg
  have hKb : K.natAbs ≤ 2 ^ 53 := by
    have h1 : |(K : ℝ)| < 2 ^ 53 + 1 := by
      have := abs_sub_abs_le_abs_sub (K : ℝ) (n / 2 ^ g)
      rw [abs_sub_comm] at this
      linarith
    have h2 : |K| < 2 ^ 53 + 1 := by exact_mod_cast h1
    rw [Int.abs_eq_natAbs] at h2
    omega
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact K g hKb (by omega)
  refine ⟨_, hf, ?_⟩
  have hval : value (Wasm.IEEE64.roundScaledMagnitude (decide (K < 0)) (K.natAbs * 2 ^ g)) =
      K * 2 ^ g / 2 ^ 1074 := by
    rw [value, hv]
    push_cast
    ring
  rw [hval]
  have hdiff : (K : ℝ) * 2 ^ g / 2 ^ 1074 - S = 2 ^ g / 2 ^ 1074 * ((K : ℝ) - n / 2 ^ g) := by
    rw [hn]
    field_simp
  rw [hdiff, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  calc 2 ^ g / 2 ^ 1074 * |n / 2 ^ g - K| ≤ 2 ^ g / 2 ^ 1074 * (1 / 2) :=
        mul_le_mul_of_nonneg_left hKd (by positivity)
    _ ≤ |S| / 2 ^ 53 + 1 / 2 ^ 1075 := by
      rcases Nat.eq_zero_or_pos g with h0 | hpos
      · rw [h0]
        have : (0 : ℝ) ≤ |S| / 2 ^ 53 := by positivity
        norm_num
        linarith
      · have hm := Nat.find_min hex (show g - 1 < g by omega)
        push Not at hm
        rw [show 53 + (g - 1) = 52 + g by omega, hna] at hm
        have h2 : (2 : ℝ) ^ (52 + g) = 2 ^ 52 * 2 ^ g := pow_add _ _ _
        rw [h2] at hm
        have : (2 : ℝ) ^ g / 2 ^ 1074 * (1 / 2) ≤ |S| / 2 ^ 53 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h3 : (2 : ℝ) ^ 53 = 2 ^ 52 * 2 := by norm_num
          nlinarith
        have : (0 : ℝ) ≤ 1 / 2 ^ 1075 := by positivity
        linarith

theorem nearest_bound (c : UInt64) (S : ℝ) (hS : |S| ≤ 2 ^ 1000)
    (hc : ∀ v : UInt64, Finite v → |value c - S| ≤ |value v - S|) :
    |value c - S| ≤ |S| / 2 ^ 53 + 1 / 2 ^ 1075 := by
  obtain ⟨v, hv, h⟩ := exists_near S hS
  exact (hc v hv).trans h

#print axioms exists_near
#print axioms nearest_bound

end LeanExe.ProofKit.F64NearReal
