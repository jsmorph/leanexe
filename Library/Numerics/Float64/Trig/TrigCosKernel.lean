import Library.Numerics.Float64.Trig.TrigSinTail
import LeanExe.ProofKit.F64SignedNearestSum
import LeanExe.ProofKit.F64ValueExact
import LeanExe.ProofKit.F64ExactProduct

/-!
The rounding error of `Trig.kernelCos x y`.  For `2 ^ -70 ≤ |x| ≤ 0.78541` and
`|y| ≤ |x| / 2 ^ 52`, the result lies within `7/5 u` of `cos (x + y)`, `u = 2 ^ -53`.  The
halving of `z` and the difference `1 - w` are exact, so `((1 - w) - hz)` recovers the rounding
error of `w = 1 - hz` up to `u ^ 2`, and the rounding of `z = x * x` contributes `u x ^ 2 / 2`.
-/

namespace Library.Numerics.Float64.Trig.TrigCosKernel

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TrigKernelWords
  TrigSinTail

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

/-- Halving a word of magnitude at least `2 ^ -1000` is exact. -/
theorem half_exact (z : UInt64) (hzf : Finite z) (hz : 1 / 2 ^ 1000 ≤ |value z|)
    (hz1 : |value z| ≤ 1) :
    Finite (Wasm.IEEE64.mul half z) ∧ value (Wasm.IEEE64.mul half z) = value z / 2 := by
  have he2 : 2 ≤ Wasm.IEEE64.exponent z := by
    by_contra h
    have hb := F64SignedNearestSum.grid_bound z
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent z - 1)) / 2 ^ 1074 ≤ 1 / 2 ^ 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hfin : Wasm.IEEE64.exponent z ≠ 2047 := by
    have h := hzf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    exact h
  have hlt : Wasm.IEEE64.exponent z ≤ 1023 := by
    by_contra h
    have hl := F64SignedNearestSum.grid_lower z (by omega)
    have : (2 : ℝ) ≤ 2 ^ (52 + (Wasm.IEEE64.exponent z - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hmz : Wasm.IEEE64.scaledMagnitude z =
      (2 ^ 52 + Wasm.IEEE64.fraction z) * 2 ^ (Wasm.IEEE64.exponent z - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, show (Wasm.IEEE64.exponent z == 0) = false by
      simp; omega, Bool.false_eq_true, ite_false]
  have hf : Wasm.IEEE64.fraction z < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, fh, -⟩ := words_finite
  obtain ⟨h1, h2, -⟩ := F64ExactProduct.mul_exact_scaled half z fh hzf 1
    (2 ^ 52 + Wasm.IEEE64.fraction z) 1073 (Wasm.IEEE64.exponent z - 1)
    (by decide) hmz (by omega) (by omega) (by omega)
  refine ⟨h1, ?_⟩
  rw [h2, value_half]
  ring

/-- `1 - w` is exact for `w` from `1/2` to `1`. -/
theorem one_sub_exact (w : UInt64) (hwf : Finite w) (hw1 : 1 / 2 ≤ value w) (hw2 : value w ≤ 1) :
    Finite (Wasm.IEEE64.sub one w) ∧ value (Wasm.IEEE64.sub one w) = 1 - value w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fo⟩ := words_finite
  have h1 : (2 : ℝ) ^ (52 + 1021) / 2 ^ 1074 = 1 / 2 := by norm_num
  have h2 : (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = 1 := by norm_num
  have hda := F64ValueExact.dvd_of_value one fo 1021 (by rw [h1, value_one]; norm_num)
  have hdb := F64ValueExact.dvd_of_value w hwf 1021 (by
    rw [h1, abs_of_nonneg (by linarith)]
    exact hw1)
  obtain ⟨hf, hv⟩ := F64ValueExact.sub_exact one w fo hwf 1021 (by norm_num) hda hdb (by
    rw [h2, value_one, abs_le]
    constructor <;> linarith)
  exact ⟨hf, by rw [hv, value_one]⟩

/-- The cosine kernel with a tail, expanded. -/
theorem cos_tail_expand (a b : ℝ) (ha : |a| ≤ 78541 / 100000) (hb : |b| ≤ 1 / 2 ^ 40) :
    |Real.cos (a + b) - (eval TrigKernelPoly.cosKernel (a ^ 2) - a * b)| ≤
      1 / 2 ^ 59 + |b| * (|a| ^ 3 / 6 + |a| ^ 5 / 100) + 2 * b ^ 2 := by
  have ha1 : |a| ≤ 1 := ha.trans (by norm_num)
  have hb1 : |b| ≤ 1 := hb.trans (by norm_num)
  have h1 := TrigKernelWide.cos_kernel_error_wide a ha
  have h2 := Real.cos_bound hb1
  have h3 := Real.sin_bound hb1
  have h4 := Real.sin_bound ha1
  have hsa := Real.abs_sin_le_one a
  have hca := Real.abs_cos_le_one a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hb3 : |b| ^ 3 ≤ b ^ 2 / 2 := by
    rw [← hb2, show |b| ^ 3 = |b| * |b| ^ 2 by ring]
    have : |b| ≤ 1 / 2 := hb.trans (by norm_num)
    nlinarith [sq_nonneg |b|]
  have hb4 : |b| ^ 4 ≤ b ^ 2 := by
    rw [← hb2, show |b| ^ 4 = |b| ^ 2 * |b| ^ 2 by ring]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hb0 hb1)
  have hb5 : |b| ^ 5 ≤ b ^ 2 := by
    rw [← hb2, show |b| ^ 5 = |b| ^ 3 * |b| ^ 2 by ring]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hb0 hb1)
  have e2 : |Real.cos b - 1| ≤ b ^ 2 := by
    rw [abs_le] at h2 ⊢
    constructor <;> nlinarith [sq_nonneg b]
  have e3 : |Real.sin b - b| ≤ b ^ 2 := by
    have hb3' : |b ^ 3| ≤ b ^ 2 / 2 := by rw [abs_pow]; exact hb3
    rw [abs_le] at h3 hb3' ⊢
    constructor <;> nlinarith [sq_nonneg b]
  have e4 : |Real.sin a - a| ≤ |a| ^ 3 / 6 + |a| ^ 5 / 100 := by
    have h := abs_sub_le (Real.sin a) (a - a ^ 3 / 6) a
    rw [show a - a ^ 3 / 6 - a = -(a ^ 3 / 6) by ring, abs_neg, abs_div, abs_pow] at h
    norm_num at h
    linarith
  have key : Real.cos a * Real.cos b - Real.sin a * Real.sin b -
      (eval TrigKernelPoly.cosKernel (a ^ 2) - a * b) =
      (Real.cos a - eval TrigKernelPoly.cosKernel (a ^ 2)) + Real.cos a * (Real.cos b - 1) -
        b * (Real.sin a - a) - Real.sin a * (Real.sin b - b) := by ring
  rw [Real.cos_add, key]
  have t2 : |Real.cos a * (Real.cos b - 1)| ≤ b ^ 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hca).trans e2
  have t3 : |b * (Real.sin a - a)| ≤ |b| * (|a| ^ 3 / 6 + |a| ^ 5 / 100) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e4 hb0
  have t4 : |Real.sin a * (Real.sin b - b)| ≤ b ^ 2 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hsa).trans e3
  have h1' : |Real.cos a - eval TrigKernelPoly.cosKernel (a ^ 2)| ≤ 1 / 2 ^ 59 := h1
  rw [abs_le] at h1' t2 t3 t4 ⊢
  constructor <;> linarith

/-- The kernel polynomial of `kernelCos` in the coefficients' words. -/
theorem cosKernel_eval (a : ℝ) :
    eval TrigKernelPoly.cosKernel (a ^ 2) =
      1 - a * a / 2 + a * a * (a * a * (value wC1 + a * a * (value wC2 + a * a * value wC3)) +
        a * a * (a * a) * (a * a * (a * a)) *
          (value wC4 + a * a * (value wC5 + a * a * value wC6))) := by
  simp only [TrigKernelPoly.cosKernel, eval_cons, eval_nil, ratOfWord_cast, wC1, wC2, wC3, wC4,
    wC5, wC6]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- The accuracy of `kernelCos` on words. -/
theorem cos_spec (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y) (hX : |value x| = X)
    (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 78541 / 100000) (hy : |value y| ≤ X / 2 ^ 52) :
    Finite (cosW x y) ∧ |value (cosW x y) - Real.cos (value x + value y)| ≤ 7 / 5 * 𝐮 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  have hx : AB x (value x) 0 X := AB.const x hxf X hX.le
  have hy' : AB y (value y) 0 (X / 2 ^ 52) := AB.const y hyf _ hy
  have z := (AB.mul hx hx (by linarith) (by linarith)).mono
    (e' := 𝐮 * X ^ 2 + η) (M' := X ^ 2) (le_of_eq (by ring)) (le_of_eq (by ring))
  have zc := z.mono (e' := 𝐮 * (617 / 1000) + η) (M' := 617 / 1000)
    (by simp only [unitRoundoff64]; linarith) hXX
  have rc := cosR_AB _ _ zc
  have zr := (AB.mul zc rc (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64])).mono (e' := 𝐮 / 8)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) le_rfl
  have xy := (AB.mul hx hy' (by linarith) (by linarith)).mono (e' := 𝐮 / 2 ^ 50)
    (M' := 1 / 2 ^ 52)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by rw [show X * (X / 2 ^ 52) = X ^ 2 / 2 ^ 52 by ring]; linarith)
  have Q := (AB.sub zr xy (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])).mono
    (e' := 3 / 20 * 𝐮) (by norm_num [unitRoundoff64]) le_rfl
  -- The value of `z` and the exact halving.
  have hz2 : value x * value x = X ^ 2 := by rw [← hX, sq_abs, sq]
  obtain ⟨hzf, hze⟩ := z.1
  rw [hz2] at hze
  set zW := Wasm.IEEE64.mul x x with hzW
  have hX2lo : 1 / 2 ^ 140 ≤ X ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hX0 2
    rw [div_pow, one_pow, ← pow_mul] at this
    exact this
  have hze' := abs_le.mp hze
  have hzlo : 1 / 2 ^ 1000 ≤ |value zW| := by
    have hpos : 1 / 2 ^ 1000 ≤ value zW := by
      simp only [hu, hη] at hze'
      linarith [hze'.1]
    exact hpos.trans (le_abs_self _)
  have hzhi : |value zW| ≤ 1 := by
    rw [abs_le]
    simp only [hu, hη] at hze'
    constructor <;> linarith [hze'.1, hze'.2]
  obtain ⟨hhf, hhv⟩ := half_exact zW hzf hzlo hzhi
  set HZ := Wasm.IEEE64.mul half zW with hHZ
  have hhz : |value HZ - X ^ 2 / 2| ≤ (𝐮 * X ^ 2 + η) / 2 := by
    rw [hhv, show value zW / 2 - X ^ 2 / 2 = (value zW - X ^ 2) / 2 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hhz' := abs_le.mp hhz
  have hHZ1 : value HZ ≤ 31 / 100 := by simp only [hu, hη] at hhz'; linarith [hhz'.2]
  have hHZ0 : 0 ≤ value HZ := by
    simp only [hu, hη] at hhz'
    linarith [hhz'.1]
  -- `w = 1 - hz`, rounded, and the exact `1 - w`.
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fo⟩ := words_finite
  have hb1 : |value one - value HZ| < 2 ^ 1023 := by
    rw [value_one, abs_lt]
    constructor <;> linarith [four_lt 1023 (by norm_num)]
  obtain ⟨hwf, hwe⟩ := F64AddBounds.sub_real_relative one HZ fo hhf hb1
  set W := Wasm.IEEE64.sub one HZ with hW
  rw [value_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - value HZ)] at hwe
  have hwe' := abs_le.mp hwe
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hu1 : 𝐮 ≤ 1 / 2 ^ 53 := le_of_eq hu
  have hwu : 𝐮 * (1 - value HZ) ≤ 𝐮 := mul_le_of_le_one_right hu0 (by linarith)
  have hw1 : 1 / 2 ≤ value W := by
    have : 𝐮 ≤ 1 / 100 := by rw [hu]; norm_num
    linarith [hwe'.1]
  have hw2 : value W ≤ 1 := by
    have hn := F64SignedNearestSum.sub_nearest one HZ fo hhf hb1 one
    rw [value_one, show (1 : ℝ) - (1 - value HZ) = value HZ by ring,
      abs_of_nonneg hHZ0] at hn
    have := (abs_le.mp hn).2
    linarith
  obtain ⟨h1wf, h1wv⟩ := one_sub_exact W hwf hw1 hw2
  -- `P = (1 - w) - hz` recovers the rounding error of `w`.
  have hb2 : |value (Wasm.IEEE64.sub one W) - value HZ| < 2 ^ 1023 := by
    rw [h1wv, abs_lt]
    constructor <;> linarith [four_lt 1023 (by norm_num)]
  obtain ⟨hPf, hPe⟩ := F64AddBounds.sub_real_relative _ _ h1wf hhf hb2
  rw [h1wv] at hPe
  set P := Wasm.IEEE64.sub (Wasm.IEEE64.sub one W) HZ with hP
  have hPx : |1 - value W - value HZ| ≤ 𝐮 := by
    rw [abs_le]
    constructor <;> linarith [hwe'.1, hwe'.2]
  have hPe' : |value P - (1 - value W - value HZ)| ≤ 𝐮 * 𝐮 :=
    hPe.trans (mul_le_mul_of_nonneg_left hPx hu0)
  -- `U = P + Q` and the final sum `w + U`.
  obtain ⟨⟨hQf, hQe⟩, hQm⟩ := Q
  set QW := Wasm.IEEE64.sub (Wasm.IEEE64.mul zW (cosR zW)) (Wasm.IEEE64.mul x y) with hQW
  have hPe'' := abs_le.mp hPe'
  have hQe' := abs_le.mp hQe
  have hQm' := abs_le.mp hQm
  have hPQ : |value P + value QW| ≤ 1 / 50 := by
    rw [abs_le]
    simp only [hu] at hPe'' hQe' hPx ⊢
    have hPx' := abs_le.mp hPx
    constructor <;> linarith [hPx'.1, hPx'.2]
  have hb3 : |value P + value QW| < 2 ^ 1023 :=
    lt_of_le_of_lt hPQ (lt_trans (by norm_num) (four_lt 1023 (by norm_num)))
  obtain ⟨hUf, hUe⟩ := F64AddBounds.add_real_relative P QW hPf hQf hb3
  set U := Wasm.IEEE64.add P QW with hU
  have hUe' : |value U - (value P + value QW)| ≤ 𝐮 / 50 := by
    have := mul_le_mul_of_nonneg_left hPQ hu0
    linarith
  have hb4 : |value W + value U| < 2 ^ 1023 := by
    have := abs_le.mp hUe'
    have := abs_le.mp hPQ
    rw [abs_lt]
    constructor <;> linarith [four_lt 1023 (by norm_num)]
  obtain ⟨hcf, hce⟩ := F64AddBounds.add_real_relative W U hwf hUf hb4
  have hcW : cosW x y = Wasm.IEEE64.add W U := rfl
  refine ⟨hcW ▸ hcf, ?_⟩
  rw [hcW]
  -- `t = w + U` against `T0 = 1 - X ^ 2 / 2 + Qx`.
  set t := value W + value U with ht
  set Qx := value x * value x *
      (value x * value x * (value wC1 + value x * value x * (value wC2 + value x * value x * value wC3)) +
        value x * value x * (value x * value x) * (value x * value x * (value x * value x)) *
          (value wC4 + value x * value x * (value wC5 + value x * value x * value wC6))) -
      value x * value y with hQx
  have htT : |t - (1 - X ^ 2 / 2 + Qx)| ≤ (𝐮 * X ^ 2 + η) / 2 + 𝐮 * 𝐮 + 3 / 20 * 𝐮 + 𝐮 / 50 := by
    have hU' := abs_le.mp hUe'
    rw [abs_le]
    constructor <;> linarith [hhz'.1, hhz'.2, hPe''.1, hPe''.2, hQe'.1, hQe'.2]
  -- `T0` against `cos (x + y)`.
  have hb : |value y| ≤ 1 / 2 ^ 40 := hy.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith)
  have hexp := cos_tail_expand (value x) (value y) (by rw [hX]; exact hX1) hb
  rw [cosKernel_eval, hX] at hexp
  have hxx : value x * value x / 2 = X ^ 2 / 2 := by rw [hz2]
  have hT0 : 1 - value x * value x / 2 + value x * value x *
      (value x * value x * (value wC1 + value x * value x * (value wC2 + value x * value x * value wC3)) +
        value x * value x * (value x * value x) * (value x * value x * (value x * value x)) *
          (value wC4 + value x * value x * (value wC5 + value x * value x * value wC6))) -
      value x * value y = 1 - X ^ 2 / 2 + Qx := by rw [hxx, hQx]; ring
  rw [hT0] at hexp
  have hy2 : value y ^ 2 ≤ X ^ 2 / 2 ^ 104 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) hy 2
    rw [div_pow, ← pow_mul] at this
    exact this
  have hyX : |value y| * (X ^ 3 / 6 + X ^ 5 / 100) ≤ X / 2 ^ 52 * (X ^ 3 / 6 + X ^ 5 / 100) :=
    mul_le_mul_of_nonneg_right hy (by positivity)
  have hexp' := abs_le.mp hexp
  have htT' := abs_le.mp htT
  have hce' := abs_le.mp hce
  -- `|t| ≤ 1 - X ^ 2 / 2 + 0.0163 + (error)`.
  have htabs : |t| ≤ 1 - X ^ 2 / 2 + (617 / 1000 * (263 / 10000) + 1 / 2 ^ 52) +
      ((𝐮 * X ^ 2 + η) / 2 + 𝐮 * 𝐮 + 3 / 20 * 𝐮 + 𝐮 / 50) := by
    rw [abs_le]
    simp only [hu, hη] at htT' hQm' ⊢
    constructor <;> linarith [htT'.1, htT'.2, hQm'.1, hQm'.2]
  have hut := mul_le_mul_of_nonneg_left htabs hu0
  rw [abs_le]
  simp only [hu, hη] at hut hce' htT' hexp' hyX hy2 ⊢
  constructor <;> linarith [hce'.1, hce'.2, htT'.1, htT'.2, hexp'.1, hexp'.2]

#print axioms half_exact
#print axioms one_sub_exact
#print axioms cos_tail_expand
#print axioms cosKernel_eval
#print axioms cos_spec

end Library.Numerics.Float64.Trig.TrigCosKernel
