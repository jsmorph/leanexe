import Verified.Examples.TgammaAccDown
import Verified.Examples.TgammaCases

/-!
The reduction of `Tgamma.accurate` above `1/4`.  For `1/4 ≤ |x| ≤ 2 ^ 8`, the code's
`d = 2 (x - (⌊x⌋ + 1/2))` is exact (`d_spec`): `⌊x⌋ + 1/2` has one fractional bit, `x` is a
multiple of `2 ^ -54`, and the difference lies in `[-1/2, 1/2)`.  `accurateRange` chooses the range
`[j, j + 1]` from `⌊x⌋` (`range_spec`).
-/

namespace Verified.Examples.TgammaAccSel
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaAcc1 TgammaAccShift

set_option exponentiation.threshold 4096

theorem half_value : value (0.5 : Float).toBits = 1 / 2 := by
  rw [show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl,
    TgammaSpecial.lit_value 0x3FE0000000000000 (1 / 2) (by decide +kernel)]
  norm_num

theorem half_finite : Finite (0.5 : Float).toBits := by
  rw [show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]; unfold CodeLib.IEEE64.Finite; decide

theorem two_finite : Finite (2.0 : Float).toBits := by
  rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl]; unfold CodeLib.IEEE64.Finite; decide

/-- **The reduced argument** `d = 2 (x - ⌊x⌋) - 1`, exact. -/
theorem d_spec (x : Float) (hx : Finite x.toBits) (hq : 1 / 4 ≤ |value x.toBits|)
    (hb : |value x.toBits| ≤ 2 ^ 8) :
    Finite (2.0 * (x - (floorF x + 0.5))).toBits ∧
      value (2.0 * (x - (floorF x + 0.5))).toBits =
        2 * (value x.toBits - ⌊value x.toBits⌋) - 1 := by
  obtain ⟨hif, hiv⟩ := TgammaCases.floorF_all x hx
  set n := ⌊value x.toBits⌋ with hn
  have hn1 := Int.floor_le (value x.toBits)
  have hn2 := Int.lt_floor_add_one (value x.toBits)
  rw [← hn] at hn1 hn2
  have hnb : |(2 * n + 1 : ℤ)| ≤ 2 ^ 53 := by
    have h1 : |((2 * n + 1 : ℤ) : ℝ)| ≤ 2 ^ 53 := by
      push_cast
      rw [abs_le] at hb ⊢
      constructor <;> linarith
    rw [← Int.cast_abs] at h1
    exact_mod_cast h1
  -- `⌊x⌋ + 1/2`
  obtain ⟨hhf, hhv⟩ := grid_add (floorF x) 0.5 hif half_finite (2 * n + 1) 1
    (by rw [hiv, half_value]; push_cast; ring) hnb (by norm_num)
  rw [hiv, half_value] at hhv
  -- `x - (⌊x⌋ + 1/2)`
  obtain ⟨zx, hzx⟩ := grid_neg x.toBits 2 (by norm_num) (by norm_num; linarith)
  have hy : value x.toBits - value (floorF x + 0.5).toBits =
      ((zx - (2 * n + 1) * 2 ^ 53 : ℤ) : ℝ) / 2 ^ 54 := by
    rw [hhv, hzx]; push_cast; ring
  have hyb : |value x.toBits - value (floorF x + 0.5).toBits| ≤ 1 / 2 := by
    rw [hhv, abs_le]; constructor <;> linarith
  obtain ⟨hdf, hdv0⟩ := grid_sub x (floorF x + 0.5) hx hhf _ 54 hy
    (int_abs_le _ (small_num _ _ hy hyb)) (by norm_num)
  have hyb' : |value (x - (floorF x + 0.5)).toBits| ≤ 1 / 2 := by rw [hdv0]; exact hyb
  have hyk : value (x - (floorF x + 0.5)).toBits =
      ((zx - (2 * n + 1) * 2 ^ 53 : ℤ) : ℝ) / 2 ^ 54 := by
    rw [hdv0]; exact hy
  have hdv := hdv0
  rw [hhv] at hdv
  set y := x - (floorF x + 0.5) with hydef
  -- `2.0 * y`
  have h2 : (2.0 : Float).toBits = Wasm.IEEE64.encodeFinite false 1024 0 := by
    rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl]; decide +kernel
  by_cases hy0 : value y.toBits = 0
  · obtain ⟨hpf, hpv⟩ := grid_mul 2.0 y two_finite hdf 2 0 0 54
      (by rw [show (2.0 : Float).toBits = 0x4000000000000000 from rfl,
        TgammaSpecial.lit_value 0x4000000000000000 2 (by decide +kernel)]; norm_num)
      (by rw [hy0]; simp) (by norm_num) (by norm_num)
    refine ⟨hpf, ?_⟩
    rw [hpv, hy0, mul_zero]
    rw [hdv] at hy0
    linarith
  · have hyl : 1 / 2 ^ 1022 < |value y.toBits| := by
      obtain ⟨k, hk⟩ : ∃ k : ℤ, value y.toBits = k / 2 ^ 54 := ⟨_, hyk⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hy0 hk
      have : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      rw [hk, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54), lt_div_iff₀ (by positivity)]
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1022 * 2 ^ 54 < 1)]
    have he1 : 1 ≤ Wasm.IEEE64.exponent y.toBits := by
      by_contra hc
      have := F64Magnitude.magnitude_lt y.toBits 1 (-1022) (by norm_num) (by norm_num) (by omega)
      rw [show ((2 : ℝ) ^ (-1022 : ℤ)) = 1 / 2 ^ 1022 by norm_num] at this
      linarith
    have he2 : Wasm.IEEE64.exponent y.toBits ≤ 1022 := by
      by_contra hc
      have := F64Magnitude.magnitude_ge y.toBits 1023 0 (by norm_num) (by norm_num) (by norm_num)
        (by omega)
      rw [zpow_zero] at this
      linarith
    rw [F64Bits.toBits_mul, h2]
    obtain ⟨hpf, hpv⟩ := F64PowerScale.mul_power_finite 1024 y.toBits (by norm_num) (by norm_num)
      hdf he1 (by omega) (by omega)
    refine ⟨hpf, ?_⟩
    rw [hpv, hdv]
    norm_num
    ring

/-- A comparison of a finite `ix` with a literal threshold. -/
theorem gt_lit (ix c : Float) (hif : Finite ix.toBits) (w : UInt64) (q : ℚ) (hcw : c.toBits = w)
    (hfin : Wasm.IEEE64.isFinite w = true) (hq : PolyBound.ratOfWord w = q) :
    ix > c ↔ (q : ℝ) < value ix.toBits := by
  have hcf : Finite c.toBits := by rw [hcw]; exact hfin
  rw [GT.gt, F64UpperWord.float_lt_iff _ _ hcf hif, hcw, TgammaSpecial.lit_value w q hq]

/-- **The range of `⌊x⌋`**: `accurateRange` returns a row of `accRanges` with `j = 4` up to 7 and
`j ≤ ⌊x⌋ ≤ j + 31` from 8 on. -/
theorem range_spec (ix : Float) (hif : Finite ix.toBits) (n : ℤ) (hiv : value ix.toBits = n)
    (hn : n ≤ 171) :
    ∃ oh imax ol jmax jN eoff : ℕ, (oh, imax, ol, jmax, jN, eoff) ∈ TgammaApprox.accRanges ∧
      ∃ jF : Float, accurateRange ix = (UInt64.ofNat oh, UInt64.ofNat imax, UInt64.ofNat ol,
        UInt64.ofNat jmax, jF, UInt64.ofNat eoff) ∧ Finite jF.toBits ∧ value jF.toBits = jN ∧
      ((n ≤ 7 ∧ jN = 4) ∨ (8 ≤ n ∧ (jN : ℤ) ≤ n ∧ n ≤ jN + 31)) := by
  have lit : ∀ (f : Float) (w : UInt64) (q : ℕ), f.toBits = w → Wasm.IEEE64.isFinite w = true →
      PolyBound.ratOfWord w = q → Finite f.toBits ∧ value f.toBits = q := by
    intro f w q hw hfin hq
    refine ⟨by rw [hw]; exact hfin, ?_⟩
    rw [hw, TgammaSpecial.lit_value w q hq]; simp
  have hn' : (n : ℝ) ≤ 171 := by exact_mod_cast hn
  unfold accurateRange
  by_cases h1 : ix > 159.0
  · rw [ite_eq_left h1]
    have : (159 : ℝ) < n := by
      have := (gt_lit ix 159.0 hif 0x4063E00000000000 159 rfl (by decide) (by decide +kernel)).mp h1
      push_cast at this; rw [hiv] at this; exact this
    have hl : 159 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 160.0 0x4064000000000000 160 rfl (by decide) (by decide +kernel)
    exact ⟨64, 14, 78, 34, 160, 942, by decide, 160.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h1]
  have g1 : n ≤ 159 := by
    have := mt (gt_lit ix 159.0 hif 0x4063E00000000000 159
      rfl (by decide) (by decide +kernel)).mpr h1
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 159 := not_lt.mp this
    exact_mod_cast this
  by_cases h2 : ix > 127.0
  · rw [ite_eq_left h2]
    have : (127 : ℝ) < n := by
      have := (gt_lit ix 127.0 hif 0x405FC00000000000 127 rfl (by decide) (by decide +kernel)).mp h2
      push_cast at this; rw [hiv] at this; exact this
    have hl : 127 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 128.0 0x4060000000000000 128 rfl (by decide) (by decide +kernel)
    exact ⟨146, 14, 160, 33, 128, 713, by decide, 128.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h2]
  have g2 : n ≤ 127 := by
    have := mt (gt_lit ix 127.0 hif 0x405FC00000000000 127
      rfl (by decide) (by decide +kernel)).mpr h2
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 127 := not_lt.mp this
    exact_mod_cast this
  by_cases h3 : ix > 95.0
  · rw [ite_eq_left h3]
    have : (95 : ℝ) < n := by
      have := (gt_lit ix 95.0 hif 0x4057C00000000000 95 rfl (by decide) (by decide +kernel)).mp h3
      push_cast at this; rw [hiv] at this; exact this
    have hl : 95 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 96.0 0x4058000000000000 96 rfl (by decide) (by decide +kernel)
    exact ⟨226, 13, 239, 32, 96, 495, by decide, 96.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h3]
  have g3 : n ≤ 95 := by
    have := mt (gt_lit ix 95.0 hif 0x4057C00000000000 95 rfl (by decide) (by decide +kernel)).mpr h3
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 95 := not_lt.mp this
    exact_mod_cast this
  by_cases h4 : ix > 63.0
  · rw [ite_eq_left h4]
    have : (63 : ℝ) < n := by
      have := (gt_lit ix 63.0 hif 0x404F800000000000 63 rfl (by decide) (by decide +kernel)).mp h4
      push_cast at this; rw [hiv] at this; exact this
    have hl : 63 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 64.0 0x4050000000000000 64 rfl (by decide) (by decide +kernel)
    exact ⟨303, 13, 316, 32, 64, 293, by decide, 64.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h4]
  have g4 : n ≤ 63 := by
    have := mt (gt_lit ix 63.0 hif 0x404F800000000000 63 rfl (by decide) (by decide +kernel)).mpr h4
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 63 := not_lt.mp this
    exact_mod_cast this
  by_cases h5 : ix > 31.0
  · rw [ite_eq_left h5]
    have : (31 : ℝ) < n := by
      have := (gt_lit ix 31.0 hif 0x403F000000000000 31 rfl (by decide) (by decide +kernel)).mp h5
      push_cast at this; rw [hiv] at this; exact this
    have hl : 31 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 32.0 0x4040000000000000 32 rfl (by decide) (by decide +kernel)
    exact ⟨380, 12, 392, 30, 32, 115, by decide, 32.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h5]
  have g5 : n ≤ 31 := by
    have := mt (gt_lit ix 31.0 hif 0x403F000000000000 31 rfl (by decide) (by decide +kernel)).mpr h5
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 31 := not_lt.mp this
    exact_mod_cast this
  by_cases h6 : ix > 25.0
  · rw [ite_eq_left h6]
    have : (25 : ℝ) < n := by
      have := (gt_lit ix 25.0 hif 0x4039000000000000 25 rfl (by decide) (by decide +kernel)).mp h6
      push_cast at this; rw [hiv] at this; exact this
    have hl : 25 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 26.0 0x403A000000000000 26 rfl (by decide) (by decide +kernel)
    exact ⟨452, 12, 464, 29, 26, 86, by decide, 26.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h6]
  have g6 : n ≤ 25 := by
    have := mt (gt_lit ix 25.0 hif 0x4039000000000000 25 rfl (by decide) (by decide +kernel)).mpr h6
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 25 := not_lt.mp this
    exact_mod_cast this
  by_cases h7 : ix > 15.0
  · rw [ite_eq_left h7]
    have : (15 : ℝ) < n := by
      have := (gt_lit ix 15.0 hif 0x402E000000000000 15 rfl (by decide) (by decide +kernel)).mp h7
      push_cast at this; rw [hiv] at this; exact this
    have hl : 15 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 16.0 0x4030000000000000 16 rfl (by decide) (by decide +kernel)
    exact ⟨522, 11, 533, 29, 16, 42, by decide, 16.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h7]
  have g7 : n ≤ 15 := by
    have := mt (gt_lit ix 15.0 hif 0x402E000000000000 15 rfl (by decide) (by decide +kernel)).mpr h7
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 15 := not_lt.mp this
    exact_mod_cast this
  by_cases h8 : ix > 7.0
  · rw [ite_eq_left h8]
    have : (7 : ℝ) < n := by
      have := (gt_lit ix 7.0 hif 0x401C000000000000 7 rfl (by decide) (by decide +kernel)).mp h8
      push_cast at this; rw [hiv] at this; exact this
    have hl : 7 < n := by exact_mod_cast this
    obtain ⟨hjf, hjv⟩ := lit 8.0 0x4020000000000000 8 rfl (by decide) (by decide +kernel)
    exact ⟨591, 10, 601, 28, 8, 14, by decide, 8.0, rfl, hjf, hjv,
      Or.inr ⟨by omega, by push_cast; omega, by push_cast; omega⟩⟩
  rw [ite_eq_right h8]
  have g8 : n ≤ 7 := by
    have := mt (gt_lit ix 7.0 hif 0x401C000000000000 7 rfl (by decide) (by decide +kernel)).mpr h8
    push_cast at this; rw [hiv] at this
    have : (n : ℝ) ≤ 7 := not_lt.mp this
    exact_mod_cast this
  obtain ⟨hjf, hjv⟩ := lit 4.0 0x4010000000000000 4 rfl (by decide) (by decide +kernel)
  exact ⟨657, 9, 666, 26, 4, 3, by decide, 4.0, rfl, hjf, hjv, Or.inl ⟨by omega, rfl⟩⟩

#print axioms range_spec

#print axioms d_spec

end Verified.Examples.TgammaAccSel
