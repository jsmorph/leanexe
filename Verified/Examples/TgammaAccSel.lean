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

#print axioms d_spec

end Verified.Examples.TgammaAccSel
