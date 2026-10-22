import Library.Numerics.Float64.Tgamma.TgammaLogdParts
import Library.Numerics.Float64.Tgamma.TgammaExpr

/-!
The code of `Tgamma.asLogd` after the reduction, as `logTail`, and its error.  `logTail_spec`
bounds `lh + ll` against `lt + l1l + l2l + E ln2l + Z + Z² P(Z)`, where `lt` is the exact sum of
the high parts and `Z = r t - 1`, by `2^-71 + |E| 2^-85`, and the low part `ll` by
`2^-22 + |lh|/2^52`.  The roundings of the low sums are followed through `F64Approx`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaLogdTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaFloor TgammaLogdTab TgammaLogdParts
  TgammaLogdKernel

set_option exponentiation.threshold 4096

/-- `asLogd` after the reduction: `r`, `t`, the exponent `ed`, the high and low parts of the
tables' logarithms, and the kernel's coefficients. -/
def logTail (r t ed h1 h2 g1 g2 c0 c1 c2 c3 : Float) : Float × Float :=
  let o := r * t
  let dxl := Library.Numerics.Arithmetic.Fma.fma r t (-o)
  let dxh := o - 1.0
  let dx := Library.Numerics.Arithmetic.Fma.fma r t (-1.0)
  let dx2 := dx * dx
  let f := dx2 * ((c0 + dx * c1) + dx2 * (c2 + dx * c3))
  let lt := (h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000
  let lh := lt + dxh
  let ll := (lt - lh) + dxh
  let ll := ll + (((g1 + g2) + Float.ofBits 0x3DB1CF79ABC9E3B4 * ed) + dxl)
  (lh, ll + f)

theorem logTail_eq (r t ed h1 h2 g1 g2 c0 c1 c2 c3 : Float) :
    logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3 =
      (((h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000) + (r * t - 1.0),
        (((((h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000) -
          (((h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000) + (r * t - 1.0))) + (r * t - 1.0)) +
          (((g1 + g2) + Float.ofBits 0x3DB1CF79ABC9E3B4 * ed) + Library.Numerics.Arithmetic.Fma.fma r t (-(r * t)))) +
        (Library.Numerics.Arithmetic.Fma.fma r t (-1.0) * Library.Numerics.Arithmetic.Fma.fma r t (-1.0)) *
          ((c0 + Library.Numerics.Arithmetic.Fma.fma r t (-1.0) * c1) +
            (Library.Numerics.Arithmetic.Fma.fma r t (-1.0) * Library.Numerics.Arithmetic.Fma.fma r t (-1.0)) * (c2 + Library.Numerics.Arithmetic.Fma.fma r t (-1.0) * c3))) := rfl

theorem ln2l_finite : Finite (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits := by
  rw [F64Bits.toBits_ofBits]; unfold CodeLib.IEEE64.Finite; decide

theorem ln2l_value : value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits =
    ((PolyBound.ratOfWord 0x3DB1CF79ABC9E3B4 : ℚ) : ℝ) := by
  rw [F64Bits.toBits_ofBits, PolyBound.ratOfWord_cast]; rfl

theorem ln2l_bound : |value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits| ≤ 1 / 2 ^ 35 := by
  rw [ln2l_value]
  have h : PolyBound.qabs (PolyBound.ratOfWord 0x3DB1CF79ABC9E3B4) ≤ 1 / 2 ^ 35 := by decide +kernel
  have h2 := TgammaExpr.qabs_cast (PolyBound.ratOfWord 0x3DB1CF79ABC9E3B4)
  rw [← h2]
  calc ((PolyBound.qabs (PolyBound.ratOfWord 0x3DB1CF79ABC9E3B4) : ℚ) : ℝ) ≤ ((1 / 2 ^ 35 : ℚ) : ℝ) :=
        Rat.cast_le.mpr h
    _ = 1 / 2 ^ 35 := by push_cast; ring

theorem ln2h_value : value (Float.ofBits 0x3FE62E42FEF80000).toBits = 11908177887 / 2 ^ 34 := by
  rw [F64Bits.toBits_ofBits, show Wasm.IEEE64.isNaN 0x3FE62E42FEF80000 = false by decide]
  simp only [Bool.false_eq_true, ite_false]
  rw [value_eq, ln2h_sv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  rewrite [mul_assoc, ← pow_add]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **The tail of `asLogd`.** -/
theorem logTail_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (r t ed h1 h2 g1 g2 c0 c1 c2 c3 : Float)
    (E z1 z2 : ℤ) (hr : Finite r.toBits) (ht : Finite t.toBits)
    (hz : |value r.toBits * value t.toBits - 1| ≤ 1 / 2400)
    (hc0 : Finite c0.toBits) (hc1 : Finite c1.toBits) (hc2 : Finite c2.toBits)
    (hc3 : Finite c3.toBits) (hb0 : |value c0.toBits| ≤ 1 / 2) (hb1 : |value c1.toBits| ≤ 34 / 100)
    (hb2 : |value c2.toBits| ≤ 26 / 100) (hb3 : |value c3.toBits| ≤ 21 / 100)
    (hed : Finite ed.toBits) (hve : sv ed.toBits = E * 2 ^ 1074) (hE : |E| ≤ 1074)
    (hh1 : Finite h1.toBits) (hh2 : Finite h2.toBits) (hv1 : sv h1.toBits = z1 * 2 ^ 1040)
    (hv2 : sv h2.toBits = z2 * 2 ^ 1040) (hz1 : 10000 * |z1| ≤ 6932 * 2 ^ 34)
    (hz2 : 1000 * |z2| ≤ 21 * 2 ^ 34)
    (hsmall : |E| ≤ 1 → (z1 + z2 + E * 11908177887 = 0 ∨
      2 ^ 34 ≤ 1475 * |z1 + z2 + E * 11908177887|))
    (hg1 : Finite g1.toBits) (hg2 : Finite g2.toBits) (hgb1 : |value g1.toBits| ≤ 1 / 2 ^ 35)
    (hgb2 : |value g2.toBits| ≤ 1 / 2 ^ 35) :
    Finite (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).1.toBits ∧
      Finite (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).2.toBits ∧
      |value (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).1.toBits +
          value (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).2.toBits -
        ((z1 + z2 + E * 11908177887 : ℤ) / 2 ^ 34 + value g1.toBits + value g2.toBits +
          E * value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits +
          (value r.toBits * value t.toBits - 1) + (value r.toBits * value t.toBits - 1) ^ 2 *
            (value c0.toBits + (value r.toBits * value t.toBits - 1) * (value c1.toBits +
              (value r.toBits * value t.toBits - 1) * (value c2.toBits +
                (value r.toBits * value t.toBits - 1) * value c3.toBits))))| ≤
        1 / 2 ^ 71 + |(E : ℝ)| / 2 ^ 85 ∧
      |value (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).2.toBits| ≤
        1 / 2 ^ 22 + |value (logTail r t ed h1 h2 g1 g2 c0 c1 c2 c3).1.toBits| / 2 ^ 52 := by
  rw [logTail_eq]
  simp only []
  obtain ⟨ho, ho99, hdxhv, hdxh, hdxl, hff, hsum, hdxhb, hdxlb, hfe, hfb⟩ :=
    kernel_spec hF r t c0 c1 c2 c3 hr ht hc0 hc1 hc2 hc3 hz hb0 hb1 hb2 hb3
  obtain ⟨hltf, hltv⟩ := lt_exact h1 h2 ed E z1 z2 hh1 hh2 hv1 hv2 (by
    have := abs_nonneg z1; nlinarith) (by have := abs_nonneg z2; nlinarith) hed hve hE
  generalize hO : r * t = o at *
  generalize hDH : o - 1.0 = dxh at *
  generalize hDL : Library.Numerics.Arithmetic.Fma.fma r t (-o) = dxl at *
  generalize hDX : Library.Numerics.Arithmetic.Fma.fma r t (-1.0) = dx at *
  generalize hFF : (dx * dx) * ((c0 + dx * c1) + (dx * dx) * (c2 + dx * c3)) = f at *
  generalize hLT : (h1 + h2) + ed * Float.ofBits 0x3FE62E42FEF80000 = lt at *
  -- `lt`
  obtain ⟨zl, hzl⟩ : ∃ zl, zl = z1 + z2 + E * 11908177887 := ⟨_, rfl⟩
  rw [← hzl] at hltv hsmall
  have hltval : value lt.toBits = (zl : ℝ) / 2 ^ 34 := by
    rw [value_eq, hltv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity)]
    rewrite [mul_assoc, ← pow_add]
    norm_num
  have hzlb : |zl| ≤ 1024 * 2 ^ 34 := by
    have := abs_le.mp hE
    have h3 : |E * 11908177887| ≤ 12789383050638 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 11908177887)]; nlinarith
    have h4 := abs_add_le (z1 + z2) (E * 11908177887)
    have h5 := abs_add_le z1 z2
    have h6 := abs_nonneg z1
    have h7 := abs_nonneg z2
    rw [hzl]
    norm_num at hz1 hz2 ⊢
    linarith
  have hltb : |value lt.toBits| ≤ 1024 := by
    rw [hltval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 34), div_le_iff₀ (by positivity)]
    have : (|(zl : ℝ)|) ≤ 1024 * 2 ^ 34 := by exact_mod_cast hzlb
    linarith
  have hsize : value lt.toBits = 0 ∨ 1 / 1475 ≤ |value lt.toBits| := by
    rcases lt_size z1 z2 E hz1 hz2 (by rw [← hzl]; exact hsmall) with h | h
    · left; rw [hltval, hzl, h]; simp
    · right
      rw [hltval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 34),
        le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ 34 ≤ 1475 * |(zl : ℝ)| := by rw [hzl]; exact_mod_cast h
      linarith
  -- the grid of `dxh`
  have hgo := F64TwoSum.rounded_dvd o.toBits (value o.toBits)
    (F64TwoSum.rounded_self o.toBits ho) 1020 (by norm_num)
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 ≤ 99 / 100)])
  have hgd : (2 : ℤ) ^ 1010 ∣ sv dxh.toBits := by
    have h1 : sv dxh.toBits = sv o.toBits - 2 ^ 1074 := by
      apply sv_eq_of_value
      rw [hdxhv, value_eq, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_div,
        div_self (by positivity)]
    rw [h1]
    exact dvd_sub (dvd_trans (pow_dvd_pow 2 (by norm_num)) hgo) (pow_dvd_pow 2 (by norm_num))
  have hgl : (2 : ℤ) ^ 1010 ∣ sv lt.toBits := by
    rw [hltv]; exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _
  obtain ⟨hlhf, hll0f, hpair, hll0b⟩ := two_sum lt dxh hltf hdxh hgl hgd hsize hdxhb hltb
  generalize hLH : lt + dxh = lh at *
  generalize hL0 : (lt - lh) + dxh = ll0 at *
  -- the low sums
  have hlnf := ln2l_finite
  have hlnb := ln2l_bound
  have hEv : value ed.toBits = E := by
    rw [value_eq, hve, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
      div_self (by positivity), mul_one]
  have hEr : |(E : ℝ)| ≤ 1074 := by exact_mod_cast hE
  have hs1 := fapprox_add (TgammaDD.fapprox_self g1 hg1) (TgammaDD.fapprox_self g2 hg2)
    (1 / 2 ^ 34) (by
      have := abs_add_le (value g1.toBits) (value g2.toBits)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 35 + 1 / 2 ^ 35 = 1 / 2 ^ 34)]) (by norm_num)
  have hs2 := fapprox_mul (TgammaDD.fapprox_self _ hlnf) (TgammaDD.fapprox_self ed hed)
    (1 / 2 ^ 35) |(E : ℝ)| hlnb (by rw [hEv]) (|(E : ℝ)| / 2 ^ 35) (by
      rw [add_zero, add_zero]; exact le_of_eq (by ring)) (by
      have : |(E : ℝ)| / 2 ^ 35 ≤ 1074 / 2 ^ 35 := div_le_div_of_nonneg_right hEr (by positivity)
      linarith [(by norm_num : (1074 : ℝ) / 2 ^ 35 < 2 ^ 1022)])
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hs1 hs2
  rw [hEv] at hs2
  have hE88 : |(E : ℝ)| / 2 ^ 35 / 2 ^ 53 ≤ 1074 / 2 ^ 88 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg (E : ℝ)]
  have hs3 := fapprox_add hs1 hs2 (1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 76) (by
    have h1 := abs_add_le (value g1.toBits + value g2.toBits)
      (value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E)
    have h2 := abs_add_le (value g1.toBits) (value g2.toBits)
    have h3 : |value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E| ≤ |(E : ℝ)| / 2 ^ 35 := by
      rw [abs_mul, div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hlnb (abs_nonneg _)
    linarith [(by norm_num : (1 / 2 ^ 35 + 1 / 2 ^ 35 : ℝ) = 1 / 2 ^ 34),
      (by norm_num : (1 / 2 ^ 34 : ℝ) / 2 ^ 53 + 1074 / 2 ^ 88 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 76)]) (by
      have : |(E : ℝ)| / 2 ^ 35 ≤ 1074 / 2 ^ 35 := div_le_div_of_nonneg_right hEr (by positivity)
      linarith [(by norm_num : (1 / 2 ^ 34 : ℝ) + 1074 / 2 ^ 35 + 1 / 2 ^ 76 < 2 ^ 1023)])
  have hs4 := fapprox_add hs3 (TgammaDD.fapprox_self dxl hdxl)
    (1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 51) (by
      have h1 := abs_add_le (value g1.toBits + value g2.toBits +
        value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E) (value dxl.toBits)
      have h2 := abs_add_le (value g1.toBits + value g2.toBits)
        (value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E)
      have h2' := abs_add_le (value g1.toBits) (value g2.toBits)
      have h3 : |value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E| ≤ |(E : ℝ)| / 2 ^ 35 := by
        rw [abs_mul, div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hlnb (abs_nonneg _)
      have h5 : (1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 76) / 2 ^ 53 ≤ 1 / 2 ^ 77 := by
        have : |(E : ℝ)| / 2 ^ 35 ≤ 1074 / 2 ^ 35 := div_le_div_of_nonneg_right hEr (by positivity)
        rw [div_le_iff₀ (by positivity)]
        linarith [(by norm_num : (1 / 2 ^ 34 : ℝ) + 1074 / 2 ^ 35 + 1 / 2 ^ 76 ≤ 1 / 2 ^ 77 * 2 ^ 53)]
      linarith [(by norm_num : (1 / 2 ^ 35 + 1 / 2 ^ 35 : ℝ) = 1 / 2 ^ 34),
        (by norm_num : (1 / 2 ^ 34 : ℝ) / 2 ^ 53 + 1074 / 2 ^ 88 + 1 / 2 ^ 1075 + 1 / 2 ^ 77 +
          1 / 2 ^ 52 ≤ 1 / 2 ^ 51)]) (by
      have : |(E : ℝ)| / 2 ^ 35 ≤ 1074 / 2 ^ 35 := div_le_div_of_nonneg_right hEr (by positivity)
      linarith [(by norm_num : (1 / 2 ^ 34 : ℝ) + 1074 / 2 ^ 35 + 1 / 2 ^ 51 < 2 ^ 1023)])
  -- the accumulated error of the low sums
  have hs4' := hs4.mono (show _ ≤ 1 / 2 ^ 85 + |(E : ℝ)| / 2 ^ 86 by
    have : 0 ≤ |(E : ℝ)| := abs_nonneg _
    have h1 : |(E : ℝ)| / 2 ^ 35 / 2 ^ 53 = |(E : ℝ)| / 2 ^ 88 := by rw [div_div, ← pow_add]
    have h2 : (1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 76) / 2 ^ 53 =
        1 / 2 ^ 87 + |(E : ℝ)| / 2 ^ 88 + 1 / 2 ^ 129 := by
      rw [add_div, add_div, div_div, div_div, div_div, ← pow_add, ← pow_add, ← pow_add]
    have h3 : (1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 51) / 2 ^ 53 =
        1 / 2 ^ 87 + |(E : ℝ)| / 2 ^ 88 + 1 / 2 ^ 104 := by
      rw [add_div, add_div, div_div, div_div, div_div, ← pow_add, ← pow_add, ← pow_add]
    rw [h1, h2, h3]
    have h4 : |(E : ℝ)| / 2 ^ 88 * 3 ≤ |(E : ℝ)| / 2 ^ 86 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith [(by norm_num : (1 / 2 ^ 34 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 + 1 / 2 ^ 87 + 1 / 2 ^ 129 +
      0 + 1 / 2 ^ 87 + 1 / 2 ^ 104 ≤ 1 / 2 ^ 85)])
  have hE24 : |(E : ℝ)| / 2 ^ 35 ≤ 1 / 2 ^ 24 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hE86 : |(E : ℝ)| / 2 ^ 86 ≤ 1 / 2 ^ 75 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨V4, hV4⟩ : ∃ V4, V4 = value g1.toBits + value g2.toBits +
      value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E + value dxl.toBits := ⟨_, rfl⟩
  rw [← hV4] at hs4'
  have hV4b : |V4| ≤ 1 / 2 ^ 34 + |(E : ℝ)| / 2 ^ 35 + 1 / 2 ^ 52 := by
    rw [hV4]
    have h1 := abs_add_le (value g1.toBits + value g2.toBits +
      value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E) (value dxl.toBits)
    have h2 := abs_add_le (value g1.toBits + value g2.toBits)
      (value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E)
    have h2' := abs_add_le (value g1.toBits) (value g2.toBits)
    have h3 : |value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits * E| ≤ |(E : ℝ)| / 2 ^ 35 := by
      rw [abs_mul, div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hlnb (abs_nonneg _)
    linarith [(by norm_num : (1 / 2 ^ 35 + 1 / 2 ^ 35 : ℝ) = 1 / 2 ^ 34)]
  -- `lh` is below `1025`
  have hlhb : |value lh.toBits| ≤ 1025 := by
    have e : value lh.toBits = (value lt.toBits + value dxh.toBits) - value ll0.toBits := by
      linarith [hpair]
    have h1 : |value lh.toBits| ≤ |value lt.toBits| + |value dxh.toBits| + |value ll0.toBits| := by
      rw [e]
      have := abs_sub (value lt.toBits + value dxh.toBits) (value ll0.toBits)
      have := abs_add_le (value lt.toBits) (value dxh.toBits)
      linarith
    linarith [(by norm_num : (1024 : ℝ) + (1 / 2400 + 1 / 2 ^ 52) + 1 / 2 ^ 1074 ≤
      1025 * (1 - 1 / 2 ^ 52))]
  have hll0b' : |value ll0.toBits| ≤ 1 / 2 ^ 41 := by
    have : |value lh.toBits| / 2 ^ 52 ≤ 1025 / 2 ^ 52 := div_le_div_of_nonneg_right hlhb (by positivity)
    linarith [(by norm_num : (1025 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 41)]
  have hll1 := fapprox_add (TgammaDD.fapprox_self ll0 hll0f) hs4' (1 / 2 ^ 24) (by
    linarith [(by norm_num : (1 / 2 ^ 41 : ℝ) + (1 / 2 ^ 34 + 1 / 2 ^ 25 + 1 / 2 ^ 52) +
      (0 + (1 / 2 ^ 85 + 1 / 2 ^ 76)) ≤ 1 / 2 ^ 24), abs_add_le (value ll0.toBits) V4]) (by norm_num)
  have hllf := fapprox_add hll1 (TgammaDD.fapprox_self f hff) (1 / 2 ^ 22) (by
    have h1 := abs_add_le (value ll0.toBits + V4) (value f.toBits)
    have h2 := abs_add_le (value ll0.toBits) V4
    linarith [(by norm_num : (1 / 2 ^ 41 : ℝ) + (1 / 2 ^ 34 + 1 / 2 ^ 25 + 1 / 2 ^ 52) + 1 / 2 ^ 23 +
      (0 + (1 / 2 ^ 85 + 1 / 2 ^ 75) + 1 / 2 ^ 24 / 2 ^ 53 + 0) ≤ 1 / 2 ^ 22)]) (by norm_num)
  have hlle := hllf.2
  have hllff := hllf.1
  clear hs1 hs2 hs3 hs4 hs4' hll1 hllf
  refine ⟨hlhf, hllff, ?_, ?_⟩
  · rw [hltval, hzl] at hpair
    have hE85 : |(E : ℝ)| / 2 ^ 86 ≤ |(E : ℝ)| / 2 ^ 85 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)
    obtain ⟨hs1', hs2'⟩ := abs_le.mp hsum
    obtain ⟨hf1, hf2⟩ := abs_le.mp hfe
    obtain ⟨he1, he2⟩ := abs_le.mp hlle
    clear hsum hfe hlle
    generalize value r.toBits * value t.toBits - 1 = Z at *
    generalize value c0.toBits + Z * (value c1.toBits + Z * (value c2.toBits + Z * value c3.toBits)) =
      P at *
    rw [abs_le]
    have hn : (1 / 2 ^ 24 : ℝ) / 2 ^ 53 + 1 / 2 ^ 22 / 2 ^ 53 + 1 / 2 ^ 85 + 1 / 2 ^ 104 +
        1 / 2 ^ 72 ≤ 1 / 2 ^ 71 := by norm_num
    constructor <;> linarith only [hn, hpair, he1, he2, hV4, hs1', hs2', hf1, hf2, hE85]
  · have h1 := abs_sub_abs_le_abs_sub (value (ll0 + (g1 + g2 + Float.ofBits 0x3DB1CF79ABC9E3B4 * ed +
      dxl) + f).toBits) (value ll0.toBits + V4 + value f.toBits)
    have h2 := abs_add_le (value ll0.toBits + V4) (value f.toBits)
    have h3 := abs_add_le (value ll0.toBits) V4
    have hn : (1 / 2 ^ 34 : ℝ) + 1 / 2 ^ 24 + 1 / 2 ^ 52 + 1 / 2 ^ 23 + 1 / 2 ^ 100 +
        (0 + (1 / 2 ^ 85 + 1 / 2 ^ 75) + 1 / 2 ^ 24 / 2 ^ 53 + 0 + 1 / 2 ^ 22 / 2 ^ 53) ≤
        1 / 2 ^ 22 := by norm_num
    have hll0c : |value ll0.toBits| ≤ |value lh.toBits| / 2 ^ 52 + 1 / 2 ^ 100 := by
      have : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 100 := by norm_num
      linarith only [hll0b, this]
    clear hll0b
    clear hpair hsum hfe hltv hv1 hv2 hve hz1 hz2 hzlb hgo hgd hgl hsmall
    generalize value (ll0 + (g1 + g2 + Float.ofBits 0x3DB1CF79ABC9E3B4 * ed + dxl) + f).toBits = vF
      at *
    generalize value ll0.toBits = v0 at *
    generalize value f.toBits = vf at *
    generalize value lh.toBits = vh at *
    generalize |(E : ℝ)| = aE at *
    linarith only [hn, h1, h2, h3, hll0c, hV4b, hfb, hlle, hE24, hE86]

#print axioms logTail_eq
#print axioms logTail_spec

end Library.Numerics.Float64.Tgamma.TgammaLogdTail
