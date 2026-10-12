import LeanExe.ProofKit.F64NearestSteps
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64Magnitude

/-!
Halving keeps the nearest property.  If `c` is a nearest word of `s` with
`2 ^ -1020 ≤ s ≤ 2 ^ 1022`, the product of `c` and the word of `1/2` is exact and is a nearest word
of `s/2` (`nearest_halve`).  A word `v` between `2 ^ -1022` and `2 ^ 1023` doubles exactly, and
`c` is at least as close to `s` as `2 v`.  A smaller `v` lies farther from `s/2` than half the
distance from `s` to `2 ^ -1021`, and a larger one farther than half the distance to `2 ^ 1023`.
-/

namespace LeanExe.ProofKit.F64NearestHalve
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestSteps

set_option exponentiation.threshold 4096

theorem finite_of_lt (v : UInt64) (hv : v.toNat < limit) : Finite v := by
  have hb : v.toNat < 2047 * 2 ^ 52 := hv
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne]
  omega

theorem boundary_word (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2046) :
    (UInt64.ofNat (e * 2 ^ 52)).toNat < limit ∧
      value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ (e + 51) / 2 ^ 1074 := by
  have h := boundary_lt_limit e he'
  have hl : e * 2 ^ 52 < limit := lt_of_le_of_lt (Nat.le_add_right _ _) h
  exact ⟨by rw [word_toNat _ hl]; exact hl, F64PositiveSpacing.boundary_value e he (by omega)⟩

/-- Doubling a word between `2 ^ -1022` and `2 ^ 1023` is exact. -/
theorem double_word (v : UInt64) (hvf : Finite v) (hlo : 1 / 2 ^ 1022 < value v)
    (hhi : value v < 2 ^ 1023) :
    (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1024 0) v).toNat < limit ∧
      value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1024 0) v) = 2 * value v := by
  obtain ⟨he1, hs⟩ := F64Magnitude.normal_of_value v hlo
  have he2 : Wasm.IEEE64.exponent v ≤ 2045 := by
    by_contra h
    have hv := F64Magnitude.value_ge_of_exponent v 2046 1023 (by norm_num) (by norm_num)
      (by norm_num) hs (by omega)
    norm_num at hv
    linarith
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite 1024 v (by norm_num) (by norm_num) hvf he1
    (by omega) (by omega)
  have hv' : value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1024 0) v) = 2 * value v := by
    rw [hv]
    norm_num
  refine ⟨positive_finite_encoding _ hf ?_, hv'⟩
  rw [hv']
  have : (0 : ℝ) < 1 / 2 ^ 1022 := by positivity
  linarith

theorem nearest_halve (s : ℝ) (c : UInt64) (hc : Nearest s c) (hs : 1 / 2 ^ 1020 ≤ s)
    (hs' : s ≤ 2 ^ 1022) :
    Finite (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1022 0) c) ∧
      value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1022 0) c) = value c / 2 ∧
      Nearest (s / 2) (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1022 0) c) := by
  obtain ⟨hcf, hcs⟩ := nearest_finite s c hc
  obtain ⟨hl2, hv2⟩ := boundary_word 2 (by norm_num) (by norm_num)
  have h53 : (2 : ℝ) ^ (2 + 51) / 2 ^ 1074 = 1 / 2 ^ 1021 := by norm_num
  rw [h53] at hv2
  have hs2 : 1 / (2 : ℝ) ^ 1021 ≤ s := le_trans (by norm_num) hs
  have hc2 := nearest_ge s c _ hc hl2 (by rw [hv2]; exact hs2)
  have hcv : 1 / (2 : ℝ) ^ 1021 ≤ value c := by
    rw [← hv2]
    exact (value_le_iff (hl2.trans limit_lt) (hc.1.trans limit_lt)).mpr hc2
  have he := F64Magnitude.exponent_ge_of_value c 2 (by norm_num) (by
    rw [show ((2 : Nat) : Int) - 1023 = -1021 by norm_num, zpow_neg, zpow_ofNat, ← one_div]
    exact hcv)
  have hlt : Wasm.IEEE64.exponent c < 2048 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite 1022 c (by norm_num) (by norm_num) hcf
    (by omega) (by omega) (by omega)
  have hv' : value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1022 0) c) = value c / 2 := by
    rw [hv, show ((1022 : Nat) : Int) - 1023 = -1 by norm_num, zpow_neg_one]
    ring
  have hpos : 0 < value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1022 0) c) := by
    rw [hv']
    have : (0 : ℝ) < 1 / 2 ^ 1021 := by positivity
    linarith
  refine ⟨hf, hv', positive_finite_encoding _ hf hpos, fun v hvl => ?_⟩
  rw [hv']
  have hhalf : |value c / 2 - s / 2| = |value c - s| / 2 := by
    rw [← sub_div, abs_div, abs_two]
  rw [hhalf]
  rcases le_or_gt (value v) (1 / 2 ^ 1022) with h1 | h1
  · have hb := hc.2 _ hl2
    have : (1 : ℝ) / 2 ^ 1022 = 1 / 2 ^ 1021 / 2 := by norm_num
    rw [hv2, abs_of_nonpos (show 1 / (2 : ℝ) ^ 1021 - s ≤ 0 by linarith)] at hb
    rw [abs_of_nonpos (show value v - s / 2 ≤ 0 by linarith)]
    linarith
  rcases lt_or_ge (value v) (2 ^ 1023) with h2 | h2
  · obtain ⟨hdl, hdv⟩ := double_word v (finite_of_lt v hvl) h1 h2
    have hb := hc.2 _ hdl
    rw [hdv] at hb
    have : |2 * value v - s| = 2 * |value v - s / 2| := by
      rw [show 2 * value v - s = 2 * (value v - s / 2) by ring, abs_mul, abs_two]
    linarith
  · obtain ⟨hlt2, hvt⟩ := boundary_word 2046 (by norm_num) (by norm_num)
    have h97 : (2 : ℝ) ^ (2046 + 51) / 2 ^ 1074 = 2 ^ 1023 := by norm_num
    rw [h97] at hvt
    have hb := hc.2 _ hlt2
    have h22 : s ≤ (2 : ℝ) ^ 1023 := hs'.trans (by norm_num)
    rw [hvt, abs_of_nonneg (show 0 ≤ (2 : ℝ) ^ 1023 - s by linarith)] at hb
    rw [abs_of_nonneg (show 0 ≤ value v - s / 2 by linarith)]
    have : (2 : ℝ) ^ 1023 = 2 * 2 ^ 1022 := by norm_num
    linarith

#print axioms double_word
#print axioms nearest_halve

end LeanExe.ProofKit.F64NearestHalve
