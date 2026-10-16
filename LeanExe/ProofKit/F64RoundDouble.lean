import LeanExe.ProofKit.F64RoundNearest

/-!
Doubling keeps a word nearest.  If `c` is a nearest word of `S` and `d` has the value `2 c`, then
`d` is a nearest word of `2 S`: every word `v` above `2 ^ -1021` in magnitude is twice the word
`v * 0.5`, which lies no closer to `S` than `c`, and the smaller and the non-finite words lie
farther from `2 S` than `d`.
-/

namespace LeanExe.ProofKit.F64RoundDouble
open CodeLib.IEEE64 F64NearestNonnegative F64RoundNearest

set_option exponentiation.threshold 4096

/-- A rounded word of a number at or above the start of binade `a` in magnitude lies at or above
that start in magnitude. -/
theorem rounded_abs_ge (c : UInt64) (S : ℝ) (hc : Rounded c S) (a : ℕ) (ha : a < 2047)
    (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ |S|) :
    value (UInt64.ofNat (a * 2 ^ 52)) ≤ |value c| := by
  obtain ⟨hcf, -, -, hnear⟩ := hc
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hcl : (Wasm.IEEE64.abs c).toNat < limit := by
    rw [F64UpperWord.abs_toNat, hlim]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    have := c.toNat_lt
    omega
  have hN : Nearest |S| (Wasm.IEEE64.abs c) := by
    refine ⟨hcl, fun v hv => ?_⟩
    have h1 := hnear v
    rw [F64UpperWord.value_abs]
    rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [hlim] at hv; omega))] at h1
    exact h1
  have hab := nearest_above |S| _ hN a ha hS
  have hBt : (UInt64.ofNat (a * 2 ^ 52)).toNat = a * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  rw [← F64UpperWord.value_abs]
  exact (F64PositiveOrder.value_le_iff (by rw [hBt]; omega) (by rw [hlim] at hcl; omega)).mpr
    (by rw [hBt]; exact hab)

/-- A non-finite word has magnitude at least `2 ^ 1023`. -/
theorem nonfinite_ge (v : UInt64) (hv : ¬ Finite v) : (2 : ℝ) ^ 1023 ≤ |value v| := by
  have hB := F64PositiveSpacing.boundary_value 2046 (by norm_num) (by norm_num)
  have hBt : (UInt64.ofNat (2046 * 2 ^ 52)).toNat = 2046 * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hat := F64UpperWord.abs_toNat v
  have hvn := v.toNat_lt
  have he : v.toNat % 2 ^ 63 / 2 ^ 52 = 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq, not_not] at hv
    omega
  have h := (F64PositiveOrder.value_le_iff (left := UInt64.ofNat (2046 * 2 ^ 52))
    (right := Wasm.IEEE64.abs v) (by rw [hBt]; omega) (by rw [hat]; omega)).mpr
    (by rw [hBt, hat]; omega)
  rw [hB, F64UpperWord.value_abs] at h
  have h2 : (2 : ℝ) ^ (2046 + 51) / 2 ^ 1074 = 2 ^ 1023 := by norm_num
  rw [h2] at h
  exact h

/-- Doubling a nearest word gives a nearest word of the doubled number. -/
theorem rounded_double (c : UInt64) (S : ℝ) (hc : Rounded c S) (hS : 1 / 2 ^ 1000 ≤ |S|)
    (hS2 : |S| < 2 ^ 1000) (d : UInt64) (hdf : Finite d) (hd : value d = 2 * value c) :
    Rounded d (2 * S) := by
  have hnear := hc.2.2.2
  have hB2 : value (UInt64.ofNat (2 * 2 ^ 52)) = 1 / 2 ^ 1021 := by
    rw [F64PositiveSpacing.boundary_value 2 (by norm_num) (by norm_num)]
    norm_num
  have hc0 : 1 / 2 ^ 1021 ≤ |value c| := by
    have := rounded_abs_ge c S hc 2 (by norm_num) (by
      rw [hB2]
      exact le_trans (by norm_num) hS)
    rwa [hB2] at this
  have hvc0 : value c ≠ 0 := by
    intro h
    rw [h, abs_zero] at hc0
    norm_num at hc0
  have hvd0 : value d ≠ 0 := by
    rw [hd]
    exact mul_ne_zero two_ne_zero hvc0
  have hmc := F64Magnitude.scaledMagnitude_pos c hvc0
  have hmd := F64Magnitude.scaledMagnitude_pos d hvd0
  have hw1 : value (UInt64.ofNat (1 * 2 ^ 52)) = 1 / 2 ^ 1022 := by
    rw [F64PositiveSpacing.boundary_value 1 (by norm_num) (by norm_num)]
    norm_num
  have hcS : |(|value c| - |S|)| ≤ |S| - 1 / 2 ^ 1022 := by
    have h1 := hnear (UInt64.ofNat (1 * 2 ^ 52))
    have h2 : (1 : ℝ) / 2 ^ 1022 < 1 / 2 ^ 1000 := by norm_num
    rw [hw1, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 1022),
      abs_of_neg (by linarith : (1 : ℝ) / 2 ^ 1022 - |S| < 0)] at h1
    linarith
  refine ⟨hdf, fun h => ?_, fun h => ?_, fun v => ?_⟩
  · have hS0 : S < 0 := by linarith
    have hvc : value c < 0 := (F64Magnitude.sign_value c hmc).mp (hc.2.1 hS0)
    exact (F64Magnitude.sign_value d hmd).mpr (by rw [hd]; linarith)
  · have hS0 : 0 < S := by linarith
    have hsc := hc.2.2.1 hS0
    have hvc : 0 < value c := by
      rcases lt_or_gt_of_ne hvc0 with hn | hp
      · have := (F64Magnitude.sign_value c hmc).mpr hn
        rw [hsc] at this
        exact absurd this Bool.false_ne_true
      · exact hp
    cases hsd : Wasm.IEEE64.sign d
    · rfl
    · have := (F64Magnitude.sign_value d hmd).mp hsd
      rw [hd] at this
      linarith
  · rw [hd, abs_mul, abs_mul, abs_two, show 2 * |value c| - 2 * |S| = 2 * (|value c| - |S|) by
      ring, abs_mul, abs_two]
    by_cases hv1 : |value v| < 1 / 2 ^ 1021
    · have h3 : 2 * |S| - |value v| ≤ |(|value v| - 2 * |S|)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have h4 : (1 : ℝ) / 2 ^ 1021 = 2 * (1 / 2 ^ 1022) := by norm_num
      linarith
    have hve : 2 ≤ Wasm.IEEE64.exponent v := by
      by_contra hn
      have := F64Magnitude.magnitude_lt v 2 (-1021) (by norm_num) (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (-1021 : ℤ) = 1 / 2 ^ 1021 := by norm_num
      rw [h2] at this
      exact hv1 this
    by_cases hvf : Finite v
    · obtain ⟨-, hu⟩ := F64Exact.mul_half_exact v hvf hve
      have h1 := hnear (Wasm.IEEE64.mul 0x3FE0000000000000 v)
      rw [hu, abs_div, abs_two] at h1
      have h2 : |(|value v| - 2 * |S|)| = 2 * |(|value v| / 2 - |S|)| := by
        rw [show |value v| - 2 * |S| = 2 * (|value v| / 2 - |S|) by ring, abs_mul, abs_two]
      rw [h2]
      linarith
    · have h1 := nonfinite_ge v hvf
      have h3 : |value v| - 2 * |S| ≤ |(|value v| - 2 * |S|)| := le_abs_self _
      have h4 : |(|value c| - |S|)| ≤ |S| := by
        have := hnear 0
        rwa [F64Magnitude.value_zero, abs_zero, zero_sub, abs_neg, abs_abs] at this
      have h5 : (2 : ℝ) ^ 1000 * 4 ≤ 2 ^ 1023 := by norm_num
      linarith

#print axioms rounded_double

end LeanExe.ProofKit.F64RoundDouble
