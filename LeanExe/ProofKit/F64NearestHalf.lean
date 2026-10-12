import LeanExe.ProofKit.F64NearestRelative
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Magnitude

/-!
A nearest word lies within half a spacing of its target.  `nearest_half` states it on the grid of
`2 ^ g` scaled units for a target below `2 ^ (53 + g)` units: the grid point nearest the target
is a word, and the nearest word is at least as close.  `nearest_relative` gives the relative
form `abs(c - s) ≤ u s` for a normal target.
-/

namespace LeanExe.ProofKit.F64NearestHalf
open CodeLib.IEEE64 F64NearestNonnegative

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem nearest_half (s : ℝ) (c : UInt64) (hc : Nearest s c) (hs0 : 0 ≤ s) (g : Nat)
    (hg : g ≤ 2043) (hs : s < (2 : ℝ) ^ (53 + g) / 2 ^ 1074) :
    |value c - s| ≤ (2 : ℝ) ^ g / 2 / 2 ^ 1074 := by
  set δ : ℝ := (2 : ℝ) ^ g / 2 ^ 1074 with hδ
  have hδ0 : 0 < δ := by positivity
  have hq0 : 0 ≤ s / δ + 1 / 2 := by positivity
  set n := ⌊s / δ + 1 / 2⌋₊ with hn
  have hn1 : (n : ℝ) ≤ s / δ + 1 / 2 := Nat.floor_le hq0
  have hn2 : s / δ + 1 / 2 < n + 1 := Nat.lt_floor_add_one _
  have hsd : s / δ < 2 ^ 53 := by
    rw [div_lt_iff₀ hδ0, hδ]
    calc s < (2 : ℝ) ^ (53 + g) / 2 ^ 1074 := hs
      _ = 2 ^ 53 * (2 ^ g / 2 ^ 1074) := by rw [pow_add]; ring
  have hn53 : n ≤ 2 ^ 53 := by
    have : (n : ℝ) < 2 ^ 53 + 1 := by linarith
    have : n < 2 ^ 53 + 1 := by exact_mod_cast this
    omega
  have hnd : |(n : ℝ) * δ - s| ≤ δ / 2 := by
    have h1 : (n : ℝ) * δ - s = δ * ((n : ℝ) - s / δ) := by field_simp
    rw [h1, abs_mul, abs_of_pos hδ0]
    have : |(n : ℝ) - s / δ| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc δ * |(n : ℝ) - s / δ| ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left this hδ0.le
      _ = δ / 2 := by ring
  obtain ⟨hvf, hvs⟩ := F64GridExact.signed_grid_packing_exact (n : Int) g
    (by rw [Int.natAbs_natCast]; exact hn53) hg
  set v := Wasm.IEEE64.roundScaledMagnitude ((n : Int) < 0) ((n : Int).natAbs * 2 ^ g)
  have hvv : value v = (n : ℝ) * δ := by
    rw [value, hvs, hδ]; push_cast; ring
  have hvsign : Wasm.IEEE64.sign v = false := by
    by_cases hn0 : n = 0
    · have : v = 0 := by
        simp only [v, hn0, Nat.cast_zero, lt_self_iff_false, decide_false, Int.natAbs_zero,
          zero_mul]
        decide
      rw [this]; decide
    · have hpos : 0 < value v := by
        rw [hvv]
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        positivity
      have hm : 0 < Wasm.IEEE64.scaledMagnitude v := by
        rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude v) with h | h
        · exfalso
          have hz : Wasm.IEEE64.scaledValue v = 0 := by
            have := natAbs_scaledValue v
            rw [h] at this
            exact Int.natAbs_eq_zero.mp this
          rw [value, hz] at hpos
          simp at hpos
        · exact h
      cases hsg : Wasm.IEEE64.sign v
      · rfl
      · have := (F64Magnitude.sign_value v hm).mp hsg
        linarith
  have hvl := F64Magnitude.lt_limit_of_finite v hvf hvsign
  calc |value c - s| ≤ |value v - s| := hc.2 v hvl
    _ = |(n : ℝ) * δ - s| := by rw [hvv]
    _ ≤ δ / 2 := hnd
    _ = (2 : ℝ) ^ g / 2 / 2 ^ 1074 := by rw [hδ]; ring

/-- A nearest word of a normal target `s` lies within `u s` of it. -/
theorem nearest_relative (s : ℝ) (c : UInt64) (hc : Nearest s c) (hs : 1 / 2 ^ 1022 ≤ s)
    (hs' : s < 2 ^ 1022) : |value c - s| ≤ u * s := by
  obtain ⟨e, he1, he2, hlo, hhi⟩ := F64NearestRelative.binade_of s hs
    (hs'.trans (by unfold F64PositiveRounding.overflowThreshold; norm_num))
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have he3 : e ≤ 2044 := by
    by_contra h
    have h1 : (2 : ℝ) ^ (2045 + 51) ≤ 2 ^ (e + 51) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 < 2 ^ 1022 := lt_of_le_of_lt hlo hs'
    rw [div_lt_iff₀ (by positivity)] at h2
    have h3 : (2 : ℝ) ^ 1022 * 2 ^ 1074 = 2 ^ (2045 + 51) := by norm_num
    have h4 : (0 : ℝ) < 2 ^ (2045 + 51) := by positivity
    linarith
  have h := nearest_half s c hc hs0 (e - 1) (by omega)
    (by rw [show 53 + (e - 1) = e + 52 by omega]; exact hhi)
  refine h.trans ?_
  have hu : u = 1 / 2 ^ 53 := rfl
  rw [hu]
  have h2 : (2 : ℝ) ^ (e - 1) / 2 / 2 ^ 1074 = 1 / 2 ^ 53 * ((2 : ℝ) ^ (e + 51) / 2 ^ 1074) := by
    rw [show e + 51 = (e - 1) + 52 by omega, pow_add]
    ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left hlo (by positivity)

#print axioms nearest_half
#print axioms nearest_relative

end LeanExe.ProofKit.F64NearestHalf
