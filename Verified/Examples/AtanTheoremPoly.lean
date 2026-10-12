import Verified.Examples.Atan
import Verified.Examples.AtanKernelPoly
import LeanExe.ProofKit.F64Approx

/-!
The polynomial part of `Atan.atan`: `t * (s1 + s2)` with `z = t * t`, `w = z * z`, and `s1`, `s2`
the even and odd halves of `aT[0] z + ... + aT[10] z ^ 11` in the order of `s_atan.c`.  For a
reduced argument `t` with `|t| ≤ s ≤ 7/16`, the computed product lies within `2.0 · 2 ^ -53 s ^ 3`
of `t · polyS t`, where `polyS t` is the same sum in exact arithmetic, and
`t - t · polyS t = t · eval atanKernel (t ^ 2)`, which `AtanKernelPoly.atan_kernel_error` compares
with `arctan t`.  Each step's bounds come from `F64Approx`, rounded up to short rationals.
-/

namespace Verified.Examples.AtanTheoremPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound

set_option exponentiation.threshold 4096

/-- `s1 + s2` of `Atan.atan` for the reduced argument `t`. -/
def atanS (t : Float) : Float :=
  let z := t * t
  let w := z * z
  let s1 := z * (Float.ofBits 0x3FD555555555550D + w * (Float.ofBits 0x3FC24924920083FF +
    w * (Float.ofBits 0x3FB745CDC54C206E + w * (Float.ofBits 0x3FB10D66A0D03D51 +
    w * (Float.ofBits 0x3FA97B4B24760DEB + w * Float.ofBits 0x3F90AD3AE322DA11)))))
  let s2 := w * (Float.ofBits 0xBFC999999998EBC4 + w * (Float.ofBits 0xBFBC71C6FE231671 +
    w * (Float.ofBits 0xBFB3B0F2AF749A6D + w * (Float.ofBits 0xBFADDE2D52DEFD9A +
    w * Float.ofBits 0xBFA2B4442C6A6C2F))))
  s1 + s2

/-- `s1 + s2` in exact arithmetic. -/
noncomputable def polyS (v : ℝ) : ℝ :=
  let z := v * v
  let w := z * z
  z * (value 0x3FD555555555550D + w * (value 0x3FC24924920083FF +
    w * (value 0x3FB745CDC54C206E + w * (value 0x3FB10D66A0D03D51 +
    w * (value 0x3FA97B4B24760DEB + w * value 0x3F90AD3AE322DA11))))) +
  w * (value 0xBFC999999998EBC4 + w * (value 0xBFBC71C6FE231671 +
    w * (value 0xBFB3B0F2AF749A6D + w * (value 0xBFADDE2D52DEFD9A +
    w * value 0xBFA2B4442C6A6C2F))))

theorem kernel_link (v : ℝ) :
    v - v * polyS v = v * eval AtanKernelPoly.atanKernel (v ^ 2) := by
  simp only [polyS, AtanKernelPoly.atanKernel, eval_cons, eval_nil, Rat.cast_neg, ratOfWord_cast]
  ring

theorem atanS_approx (t : Float) (s : ℝ) (ht : FSApprox t (value t.toBits) s 1 0)
    (hs1 : s ≤ 7 / 16) (hs0 : 1 / 2 ^ 27 ≤ s) :
    FSApprox (t * atanS t) (value t.toBits * polyS (value t.toBits)) (s * (s * s))
      (3779 / 10000) ((4999 / 2500) / 2 ^ 53) := by
  have hs : 0 < s := ht.1
  have hss : 1 / 2 ^ 54 ≤ s * s := by
    have := mul_le_mul hs0 hs0 (by positivity) hs.le
    norm_num at this ⊢
    linarith
  have hpos2 : 0 < s * s := mul_pos hs hs
  have hle2 : s * s ≤ 1 := by nlinarith
  have hss2 : s * s ≤ (7 / 16) ^ 2 := by nlinarith
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hη2 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (s * s) := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * (s * s) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    norm_num at this ⊢
    linarith
  have hη21 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (s * s * 1) := by rw [mul_one]; exact hη2
  have hη4 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (s * s * (s * s)) := by
    have h4 : 1 / 2 ^ 54 * (1 / 2 ^ 54) ≤ s * s * (s * s) := mul_le_mul hss hss (by positivity)
      hpos2.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54 * (1 / 2 ^ 54)) ≤ 1 / 2 ^ 960 * (s * s * (s * s)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    norm_num at this ⊢
    linarith
  have hη41 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (s * s * (s * s) * 1) := by
    rw [mul_one]; exact hη4
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (s * (s * s)) := by
    have h3 : 1 / 2 ^ 27 * (1 / 2 ^ 54) ≤ s * (s * s) := mul_le_mul hs0 hss (by positivity) hs.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 27 * (1 / 2 ^ 54)) ≤ 1 / 2 ^ 960 * (s * (s * s)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hk4 : s * s * (s * s) ≤ (7 / 16) ^ 4 * 1 := by
    have := mul_le_mul hss2 hss2 hpos2.le (by positivity)
    nlinarith
  have hk2 : s * s * (s * s) * 1 ≤ (7 / 16) ^ 2 * (s * s) := by
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right hss2 hpos2.le
  have hz := (fsapprox_mul ht ht (1 / 2 ^ 960) hη2 (by norm_num)).mono
    (M' := 1) (e' := (10001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hw := (fsapprox_mul hz hz (1 / 2 ^ 960) hη4 (by norm_num)).mono
    (M' := 1) (e' := (30003 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hwk := (hw.rescale 1 ((7 / 16) ^ 4) one_pos le_rfl hk4).mono
    (M' := (367 / 10000)) (e' := (11 / 100) / 2 ^ 53) (by norm_num) (by norm_num)
  have c10 := fsapprox_const 0x3F90AD3AE322DA11 (by decide +kernel) (((8143 / 500000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pa8 := (fsapprox_mul hwk c10 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (5977 / 10000000)) (e' := (3 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have qa8 := (pa8.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (5977 / 10000000)) (e' := (3 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have c8 := fsapprox_const 0x3FA97B4B24760DEB (by decide +kernel) (((49769 / 1000000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have ha8 := (fsapprox_add' c8 qa8 (by norm_num)).mono
    (M' := (63 / 1250)) (e' := (33 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have pa6 := (fsapprox_mul hwk ha8 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (19 / 10000)) (e' := (47 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qa6 := (pa6.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (19 / 10000)) (e' := (47 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c6 := fsapprox_const 0x3FB10D66A0D03D51 (by decide +kernel) (((66611 / 1000000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have ha6 := (fsapprox_add' c6 qa6 (by norm_num)).mono
    (M' := (343 / 5000)) (e' := (39 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pa4 := (fsapprox_mul hwk ha6 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (13 / 5000)) (e' := (13 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qa4 := (pa4.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (13 / 5000)) (e' := (13 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c4 := fsapprox_const 0x3FB745CDC54C206E (by decide +kernel) (((90909 / 1000000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have ha4 := (fsapprox_add' c4 qa4 (by norm_num)).mono
    (M' := (117 / 1250)) (e' := (533 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pa2 := (fsapprox_mul hwk ha4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (7 / 2000)) (e' := (177 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qa2 := (pa2.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (7 / 2000)) (e' := (177 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c2 := fsapprox_const 0x3FC24924920083FF (by decide +kernel) (((71429 / 500000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have ha2 := (fsapprox_add' c2 qa2 (by norm_num)).mono
    (M' := (183 / 1250)) (e' := (1641 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pa0 := (fsapprox_mul hwk ha2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (27 / 5000)) (e' := (11 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have qa0 := (pa0.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (27 / 5000)) (e' := (11 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have c0 := fsapprox_const 0x3FD555555555550D (by decide +kernel) (((166667 / 500000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have ha0 := (fsapprox_add' c0 qa0 (by norm_num)).mono
    (M' := (847 / 2500)) (e' := (3663 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c9 := fsapprox_const 0xBFA2B4442C6A6C2F (by decide +kernel) (((9133 / 250000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pb7 := (fsapprox_mul hwk c9 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (7 / 5000)) (e' := (27 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qb7 := (pb7.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (7 / 5000)) (e' := (27 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c7 := fsapprox_const 0xBFADDE2D52DEFD9A (by decide +kernel) (((1823 / 31250 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb7 := (fsapprox_add' c7 qb7 (by norm_num)).mono
    (M' := (299 / 5000)) (e' := (163 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pb5 := (fsapprox_mul hwk hb7 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (11 / 5000)) (e' := (7 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have qb5 := (pb5.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (11 / 5000)) (e' := (7 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0xBFB3B0F2AF749A6D (by decide +kernel) (((76919 / 1000000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb5 := (fsapprox_add' c5 qb5 (by norm_num)).mono
    (M' := (99 / 1250)) (e' := (113 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have pb3 := (fsapprox_mul hwk hb5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (3 / 1000)) (e' := (3 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have qb3 := (pb3.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (3 / 1000)) (e' := (3 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have c3 := fsapprox_const 0xBFBC71C6FE231671 (by decide +kernel) (((13889 / 125000 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 := (fsapprox_add' c3 qb3 (by norm_num)).mono
    (M' := (571 / 5000)) (e' := (323 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pb1 := (fsapprox_mul hwk hb3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (21 / 5000)) (e' := (43 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qb1 := (pb1.rescale 1 (1) one_pos le_rfl (by norm_num)).mono
    (M' := (21 / 5000)) (e' := (43 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c1 := fsapprox_const 0xBFC999999998EBC4 (by decide +kernel) (((1 / 5 : ℚ)) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 := (fsapprox_add' c1 qb1 (by norm_num)).mono
    (M' := (1021 / 5000)) (e' := (1129 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs1 := (fsapprox_mul hz ha0 (1 / 2 ^ 960) hη21 (by norm_num)).mono
    (M' := (847 / 2500)) (e' := (261 / 250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs1' := (hs1.rescale (s * s) (1) hpos2 hle2 (by rw [mul_one, one_mul])).mono
    (M' := (847 / 2500)) (e' := (261 / 250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs2 := (fsapprox_mul hw hb1 (1 / 2 ^ 960) hη41 (by norm_num)).mono
    (M' := (1021 / 5000)) (e' := (10427 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hs2' := (hs2.rescale (s * s) ((7 / 16) ^ 2) hpos2 hle2 hk2).mono
    (M' := (391 / 10000)) (e' := (499 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hS := (fsapprox_add' hs1' hs2' (by norm_num)).mono
    (M' := (3779 / 10000)) (e' := (2027 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have hP := (fsapprox_mul ht hS (1 / 2 ^ 960) hη3 (by norm_num)).mono
    (M' := (3779 / 10000)) (e' := (4999 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  exact hP.congr (by simp only [polyS])

#print axioms kernel_link
#print axioms atanS_approx

end Verified.Examples.AtanTheoremPoly
