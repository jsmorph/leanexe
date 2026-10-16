import Verified.Examples.TanTrunc
import Verified.Examples.TanComp
import Verified.Examples.TrigApprox
import LeanExe.ProofKit.F64DivBounds

/-!
The odd path of `Tan.kernelTan` below `0x3FE59428`: the compensated reciprocal `-1/(x + r)`.
With `W = x + r` exact, the result is a nearest word to a real `τ` within `u / (2 ^ 11 |W|)` of
`-1/W`: the truncated heads make `t z` exact, and the remaining roundings act on quantities of
size `2 ^ -17`.  Each rounding step is a separate lemma with only the hypotheses it uses.
-/

namespace Verified.Examples.TanOdd

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanComp TrigKernelWords

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

/-- The compensated reciprocal on words, `smallW x y true` with `r = corrW x y`. -/
def oddW (x r : UInt64) : UInt64 :=
  let w := Wasm.IEEE64.add x r
  let z := canon (w &&& mask)
  let v := Wasm.IEEE64.sub r (Wasm.IEEE64.sub z x)
  let a := Wasm.IEEE64.div negOne w
  let t := canon (a &&& mask)
  let s := Wasm.IEEE64.add one (Wasm.IEEE64.mul t z)
  Wasm.IEEE64.add t (Wasm.IEEE64.mul a (Wasm.IEEE64.add s (Wasm.IEEE64.mul t v)))

theorem smallW_odd (x y : UInt64) : smallW x y true = oddW x (corrW x y) := by
  simp only [smallW, oddW, mask, Bool.not_true, Bool.false_eq_true, ite_false]

theorem oddW_eq (x r w z a t : UInt64) (hw : Wasm.IEEE64.add x r = w) (hz : canon (w &&& mask) = z)
    (ha : Wasm.IEEE64.div negOne w = a) (ht : canon (a &&& mask) = t) :
    oddW x r = Wasm.IEEE64.add t (Wasm.IEEE64.mul a (Wasm.IEEE64.add
      (Wasm.IEEE64.add one (Wasm.IEEE64.mul t z))
      (Wasm.IEEE64.mul t (Wasm.IEEE64.sub r (Wasm.IEEE64.sub z x))))) := by
  subst hw hz ha ht
  simp only [oddW]

theorem exp_two (v : UInt64) (h : 1 / 2 ^ 1000 ≤ |value v|) : 2 ≤ Wasm.IEEE64.exponent v := by
  by_contra hc
  have hb := F64SignedNearestSum.grid_bound v
  have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 ≤ 1 / 2 ^ 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem exp_upper (v : UInt64) (n : ℕ) (h : |value v| < 2 ^ n) :
    Wasm.IEEE64.exponent v ≤ n + 1023 := by
  by_contra hc
  have hl := F64SignedNearestSum.grid_lower v (by omega)
  have : (2 : ℝ) ^ n ≤ 2 ^ (52 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 := by
    rw [le_div_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem exp_sum (a w : UInt64) (h : 1 / 2 ≤ |value a * value w|) :
    1012 ≤ Wasm.IEEE64.exponent a + Wasm.IEEE64.exponent w := by
  by_contra hc
  have hp : |value a * value w| < 2 ^ (53 + (Wasm.IEEE64.exponent a - 1)) / 2 ^ 1074 *
      (2 ^ (53 + (Wasm.IEEE64.exponent w - 1)) / 2 ^ 1074) := by
    rw [abs_mul]
    exact mul_lt_mul'' (F64SignedNearestSum.grid_bound a) (F64SignedNearestSum.grid_bound w)
      (abs_nonneg _) (abs_nonneg _)
  have hk : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent a - 1)) *
      2 ^ (53 + (Wasm.IEEE64.exponent w - 1)) ≤ 2 ^ 1117 := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_mul_div_comm] at hp
  have h2 := div_le_div_of_nonneg_right hk (show (0 : ℝ) ≤ 2 ^ 1074 * 2 ^ 1074 by positivity)
  have h3 : (2 : ℝ) ^ 1117 / (2 ^ 1074 * 2 ^ 1074) ≤ 1 / 2 := by norm_num
  linarith

theorem value_negOne : value negOne = -1 := by
  have h : Wasm.IEEE64.scaledValue negOne = -(2 ^ 1074) := by decide +kernel
  rw [TrigSmall.value_of_scaled, h]
  push_cast
  norm_num

theorem sub_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at this

/-- `x + r` against `|x| = X`. -/
theorem sum_real (a b X : ℝ) (hX : |a| = X) (hX0 : 0 < X) (hb : |b| ≤ X / 5) :
    4 / 5 * X ≤ |a + b| ∧ |a + b| ≤ 6 / 5 * X ∧ 4 / 5 * X ^ 2 ≤ a * (a + b) := by
  have h1 := abs_sub_abs_le_abs_sub a (-b)
  rw [sub_neg_eq_add, abs_neg] at h1
  have h2 := abs_add_le a b
  have h3 : |a * b| ≤ X * (X / 5) := by
    rw [abs_mul, hX]
    exact mul_le_mul_of_nonneg_left hb hX0.le
  have h4 := (abs_le.mp h3).1
  have h5 : a ^ 2 = X ^ 2 := by rw [← sq_abs, hX]
  refine ⟨by linarith, by linarith, ?_⟩
  linarith

/-- The rounded sum `w` against `W = x + r`. -/
theorem w_real (X W wv xv : ℝ) (hX : |xv| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 6744 / 10000)
    (hWl : 4 / 5 * X ≤ |W|) (hWu : |W| ≤ 6 / 5 * X) (hxW : 4 / 5 * X ^ 2 ≤ xv * W)
    (hwe : |wv - W| ≤ 𝐮 * |W|) :
    |W| * (1 - 𝐮) ≤ |wv| ∧ |wv| ≤ |W| * (1 + 𝐮) ∧ 1 / 2 ^ 72 ≤ |wv| ∧ |wv| ≤ 1 ∧
      0 < wv * xv := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  rw [hu] at hwe ⊢
  have h1 := abs_sub_abs_le_abs_sub W wv
  rw [abs_sub_comm] at h1
  have h2 := abs_sub_abs_le_abs_sub wv W
  have hX0' : 0 < X := lt_of_lt_of_le (by positivity) hX0
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
  have h3 : |(wv - W) * xv| ≤ 1 / 2 ^ 53 * |W| * X := by
    rw [abs_mul, hX]
    exact mul_le_mul_of_nonneg_right hwe hX0'.le
  have h4 := (abs_le.mp h3).1
  have h5 : |W| * X ≤ 6 / 5 * X * X := mul_le_mul_of_nonneg_right hWu hX0'.le
  have h6 : 0 < X * X := mul_pos hX0' hX0'
  linarith

theorem w_spec (x r : UInt64) (X : ℝ) (hxf : Finite x) (hrf : Finite r) (hX : |value x| = X)
    (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 6744 / 10000) (hr : |value r| ≤ X / 5) :
    Finite (Wasm.IEEE64.add x r) ∧
      |value (Wasm.IEEE64.add x r) - (value x + value r)| ≤ 𝐮 * |value x + value r| ∧
      |value x + value r| * (1 - 𝐮) ≤ |value (Wasm.IEEE64.add x r)| ∧
      |value (Wasm.IEEE64.add x r)| ≤ |value x + value r| * (1 + 𝐮) ∧
      1 / 2 ^ 72 ≤ |value (Wasm.IEEE64.add x r)| ∧ |value (Wasm.IEEE64.add x r)| ≤ 1 ∧
      0 < value (Wasm.IEEE64.add x r) * value x ∧
      4 / 5 * X ≤ |value x + value r| ∧ |value x + value r| ≤ 6 / 5 * X := by
  obtain ⟨hWl, hWu, hxW⟩ :=
    sum_real (value x) (value r) X hX (lt_of_lt_of_le (by positivity) hX0) hr
  have h4 : (4 : ℝ) < 2 ^ 1023 := TrigApprox.four_lt 1023 (by norm_num)
  obtain ⟨hwf, hwe⟩ := F64AddBounds.add_real_relative x r hxf hrf (by linarith)
  obtain ⟨h1, h2, h3, h5, h6⟩ :=
    w_real X _ _ _ hX hX0 hX1 hWl hWu hxW hwe
  exact ⟨hwf, hwe, h1, h2, h3, h5, h6, hWl, hWu⟩

/-- Sterbenz conditions for `z - x`, with `z` the head of `w`. -/
theorem ratio_real (X W wv zv xv : ℝ) (hX : |xv| = X) (hX0 : 0 < X) (hWl : 4 / 5 * X ≤ |W|)
    (hWu : |W| ≤ 6 / 5 * X) (hwl : |W| * (1 - 𝐮) ≤ |wv|) (hwu : |wv| ≤ |W| * (1 + 𝐮))
    (hzd : |zv - wv| ≤ |wv| / 2 ^ 20) (hzb : |zv| ≤ |wv|) (hzs : 0 ≤ zv * wv)
    (hwx : 0 < wv * xv) :
    0 ≤ zv * xv ∧ |xv| ≤ 2 * |zv| ∧ |zv| ≤ 2 * |xv| := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  rw [hu] at hwl hwu
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 0 ≤ zv * wv * (wv * xv) := mul_nonneg hzs hwx.le
    have h2 : 0 < wv ^ 2 := by
      have : wv ≠ 0 := by rintro rfl; simp at hwx
      exact lt_of_le_of_ne (sq_nonneg wv) (Ne.symm (pow_ne_zero 2 this))
    have : zv * wv * (wv * xv) = wv ^ 2 * (zv * xv) := by ring
    rw [this] at h1
    exact (mul_nonneg_iff_of_pos_left h2).mp h1
  · have := abs_sub_abs_le_abs_sub wv zv
    rw [abs_sub_comm] at this
    rw [hX]
    linarith
  · rw [hX]
    linarith

theorem v_spec (x r w : UInt64) (X : ℝ) (hxf : Finite x) (hrf : Finite r) (hwf : Finite w)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 6744 / 10000)
    (hr : |value r| ≤ X / 5) (hwl : |value x + value r| * (1 - 𝐮) ≤ |value w|)
    (hwu : |value w| ≤ |value x + value r| * (1 + 𝐮))
    (hWl : 4 / 5 * X ≤ |value x + value r|) (hWu : |value x + value r| ≤ 6 / 5 * X)
    (hwx : 0 < value w * value x) (hew : 2 ≤ Wasm.IEEE64.exponent w) (hw1 : |value w| ≤ 1) :
    Finite (Wasm.IEEE64.sub r (Wasm.IEEE64.sub (w &&& mask) x)) ∧
      |value (Wasm.IEEE64.sub r (Wasm.IEEE64.sub (w &&& mask) x)) -
          (value x + value r - value (w &&& mask))| ≤
        𝐮 * |value x + value r - value (w &&& mask)| := by
  obtain ⟨hzf, -, hze, -, hzd, hzb, hzs⟩ := trunc_spec w hwf (by omega)
  have hX0' : 0 < X := lt_of_lt_of_le (by positivity) hX0
  obtain ⟨hzx, h1, h2⟩ := ratio_real X _ _ _ _ hX hX0' hWl hWu hwl hwu hzd hzb hzs hwx
  have hzex : Wasm.IEEE64.exponent (w &&& mask) ≤ 2044 := by
    rw [hze]
    have := exp_upper w 1 (by rw [pow_one]; linarith)
    omega
  obtain ⟨hdf, hdv⟩ := sterbenz _ x hzf hxf hzx h1 h2 hzex
  have hVb : |value r - value (Wasm.IEEE64.sub (w &&& mask) x)| < 2 ^ 1023 := by
    rw [hdv]
    have h5 := sub_abs (value r) (value (w &&& mask) - value x)
    have h6 := sub_abs (value (w &&& mask)) (value x)
    have h7 : |value (w &&& mask)| ≤ 2 * X := by rw [← hX]; exact h2
    have h4 : (4 : ℝ) < 2 ^ 1023 := TrigApprox.four_lt 1023 (by norm_num)
    rw [hX] at h6
    linarith
  obtain ⟨hvf, hve⟩ := F64AddBounds.sub_real_relative r _ hrf hdf hVb
  rw [hdv, show value r - (value (w &&& mask) - value x) =
    value x + value r - value (w &&& mask) by ring] at hve
  exact ⟨hvf, hve⟩

/-- The rounded reciprocal `a` of `w`. -/
theorem a_real (av wv : ℝ) (hw0 : 1 / 2 ^ 72 ≤ |wv|) (hw1 : |wv| ≤ 1)
    (hae : |av - -1 / wv| ≤ 𝐮 * |-1 / wv| + η) :
    |av * wv + 1| ≤ 𝐮 + η ∧ 1 / 2 ≤ |av| ∧ |av| ≤ 2 ^ 80 ∧ |av| * |wv| ≤ 2 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hwp : 0 < |wv| := lt_of_lt_of_le (by positivity) hw0
  have hwne : wv ≠ 0 := abs_pos.mp hwp
  have hα : |av * wv + 1| ≤ 𝐮 + η := by
    have h1 : av * wv + 1 = (av - -1 / wv) * wv := by
      rw [sub_mul, div_mul_cancel₀ _ hwne]
      ring
    rw [h1, abs_mul]
    have h2 : |-1 / wv| = 1 / |wv| := by rw [abs_div, abs_neg, abs_one]
    rw [h2] at hae
    have h3 : 0 ≤ η := by rw [hη]; positivity
    calc |av - -1 / wv| * |wv| ≤ (𝐮 * (1 / |wv|) + η) * |wv| :=
          mul_le_mul_of_nonneg_right hae hwp.le
      _ = 𝐮 + η * |wv| := by
          rw [add_mul, mul_assoc, one_div, inv_mul_cancel₀ hwp.ne', mul_one]
      _ ≤ 𝐮 + η := by
          have := mul_le_mul_of_nonneg_left hw1 h3
          linarith
  rw [hu, hη] at hα
  have h1 := abs_le.mp hα
  have h3 : |av| * |wv| ≤ |av| := mul_le_of_le_one_right (abs_nonneg _) hw1
  have h4 : |av * wv| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub (av * wv) (-1)
    rw [sub_neg_eq_add, abs_neg, abs_one] at this
    linarith
  have h5 : 1 / 2 ≤ |av * wv| := by
    rcases le_or_gt 0 (av * wv) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  rw [abs_mul] at h4 h5
  refine ⟨by rw [hu, hη]; exact hα, by linarith, ?_, h4⟩
  have : |av| * (1 / 2 ^ 72) ≤ |av| * |wv| := mul_le_mul_of_nonneg_left hw0 (abs_nonneg _)
  linarith

theorem a_spec (w : UInt64) (hwf : Finite w) (hw0 : 1 / 2 ^ 72 ≤ |value w|)
    (hw1 : |value w| ≤ 1) :
    Finite (Wasm.IEEE64.div negOne w) ∧
      |value (Wasm.IEEE64.div negOne w) * value w + 1| ≤ 𝐮 + η ∧
      1 / 2 ≤ |value (Wasm.IEEE64.div negOne w)| ∧
      |value (Wasm.IEEE64.div negOne w)| ≤ 2 ^ 80 ∧
      |value (Wasm.IEEE64.div negOne w)| * |value w| ≤ 2 := by
  have hnf : Finite negOne := by unfold CodeLib.IEEE64.Finite; decide
  have hwp : 0 < |value w| := lt_of_lt_of_le (by positivity) hw0
  have hwm : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
    intro h0
    have := F64RoundNearest.abs_value w
    rw [h0, Nat.cast_zero, zero_div] at this
    linarith
  have hab : |value negOne / value w| < 2 ^ 1022 := by
    rw [value_negOne, abs_div, abs_neg, abs_one, div_lt_iff₀ hwp]
    have : (2 : ℝ) ^ 1022 * (1 / 2 ^ 72) ≤ 2 ^ 1022 * |value w| :=
      mul_le_mul_of_nonneg_left hw0 (by positivity)
    have h2 : (1 : ℝ) < 2 ^ 1022 * (1 / 2 ^ 72) := by norm_num
    linarith
  obtain ⟨haf, hae⟩ := F64DivBounds.div_real_mixed negOne w hnf hwf hwm hab
  rw [value_negOne] at hae
  exact ⟨haf, a_real _ _ hw0 hw1 hae⟩

/-- The exact product `t z` of the two heads. -/
theorem p_spec (a w : UInt64) (haf : Finite a) (hwf : Finite w)
    (hea : 2 ≤ Wasm.IEEE64.exponent a) (hew : 2 ≤ Wasm.IEEE64.exponent w)
    (hsum : 1012 ≤ Wasm.IEEE64.exponent a + Wasm.IEEE64.exponent w)
    (hsum2 : Wasm.IEEE64.exponent a + Wasm.IEEE64.exponent w ≤ 3000) :
    Finite (Wasm.IEEE64.mul (a &&& mask) (w &&& mask)) ∧
      value (Wasm.IEEE64.mul (a &&& mask) (w &&& mask)) = value (a &&& mask) * value (w &&& mask) := by
  obtain ⟨htf, -, -, htm, -, -, -⟩ := trunc_spec a haf (by omega)
  obtain ⟨hzf, -, -, hzm, -, -, -⟩ := trunc_spec w hwf (by omega)
  have hfa : Wasm.IEEE64.fraction a < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hfw : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  obtain ⟨hpf, hpv, -, -⟩ := F64ExactProduct.mul_exact_scaled _ _ htf hzf _ _ _ _ htm hzm
    (by
      have h1 : Wasm.IEEE64.fraction a / 2 ^ 32 < 2 ^ 20 := by omega
      have h2 : Wasm.IEEE64.fraction w / 2 ^ 32 < 2 ^ 20 := by omega
      calc (2 ^ 20 + Wasm.IEEE64.fraction a / 2 ^ 32) * (2 ^ 20 + Wasm.IEEE64.fraction w / 2 ^ 32)
          < 2 ^ 21 * 2 ^ 21 := Nat.mul_lt_mul'' (by omega) (by omega)
        _ ≤ 2 ^ 53 := by norm_num)
    (by omega) (by omega)
  exact ⟨hpf, hpv⟩

/-- The roundings of `s = 1 + t z`, `q = t v`, `o = s + q`, and `m = a o`. -/
theorem tail_spec (t p vv a s q o m : UInt64) (hs : Wasm.IEEE64.add one p = s)
    (hq : Wasm.IEEE64.mul t vv = q) (ho : Wasm.IEEE64.add s q = o) (hm : Wasm.IEEE64.mul a o = m)
    (htf : Finite t) (hpf : Finite p) (hvf : Finite vv) (haf : Finite a)
    (hpb : |value p| ≤ 2) (htv : |value t * value vv| ≤ 1 / 2 ^ 17) (hab : |value a| ≤ 2 ^ 80)
    (htb : |value t| ≤ 2 ^ 80) :
    Finite m ∧ |value s - (1 + value p)| ≤ 𝐮 * |1 + value p| ∧
      |value q - value t * value vv| ≤ 𝐮 * |value t * value vv| + η ∧
      |value o - (value s + value q)| ≤ 𝐮 * |value s + value q| ∧
      |value m - value a * value o| ≤ 𝐮 * |value a * value o| + η ∧
      |value t + value m| < 2 ^ 1023 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have h4 : (4 : ℝ) < 2 ^ 1022 := TrigApprox.four_lt 1022 (by norm_num)
  have h4' : (4 : ℝ) < 2 ^ 1023 := TrigApprox.four_lt 1023 (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fo⟩ := words_finite
  obtain ⟨hsf, hse⟩ := F64AddBounds.add_real_relative one p fo hpf (by
    rw [value_one]
    have := abs_add_le 1 (value p)
    rw [abs_one] at this
    linarith)
  rw [value_one, hs] at hse
  rw [hs] at hsf
  obtain ⟨hqf, hqe⟩ := F64MulBounds.mul_real_mixed t vv htf hvf (by linarith)
  rw [hq] at hqf hqe
  have hsb : |value s| ≤ 4 := by
    have := abs_sub_abs_le_abs_sub (value s) (1 + value p)
    have h1 := abs_add_le 1 (value p)
    rw [abs_one] at h1
    have : 𝐮 * |1 + value p| ≤ 1 := by
      rw [hu]
      have := abs_nonneg (1 + value p)
      linarith
    linarith
  have hqb : |value q| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value q) (value t * value vv)
    have : 𝐮 * |value t * value vv| + η ≤ 1 / 2 := by
      rw [hu, hη]
      have := abs_nonneg (value t * value vv)
      linarith
    have : (1 : ℝ) / 2 ^ 17 ≤ 1 / 2 := by norm_num
    linarith
  obtain ⟨hof, hoe⟩ := F64AddBounds.add_real_relative s q hsf hqf (by
    have := abs_add_le (value s) (value q)
    linarith)
  rw [ho] at hof hoe
  have hob : |value o| ≤ 10 := by
    have := abs_sub_abs_le_abs_sub (value o) (value s + value q)
    have := abs_add_le (value s) (value q)
    have : 𝐮 * |value s + value q| ≤ 5 := by
      rw [hu]
      have := abs_nonneg (value s + value q)
      linarith
    linarith
  have hao : |value a * value o| ≤ 2 ^ 80 * 10 := by
    rw [abs_mul]
    exact mul_le_mul hab hob (abs_nonneg _) (by positivity)
  obtain ⟨hmf, hme⟩ := F64MulBounds.mul_real_mixed a o haf hof (by
    have : (2 : ℝ) ^ 80 * 10 < 2 ^ 1022 := by norm_num
    linarith)
  rw [hm] at hmf hme
  have hmb : |value m| ≤ 2 ^ 90 := by
    have := abs_sub_abs_le_abs_sub (value m) (value a * value o)
    rw [hu, hη] at hme
    have : 1 / 2 ^ 53 * |value a * value o| ≤ 1 / 2 ^ 53 * (2 ^ 80 * 10) :=
      mul_le_mul_of_nonneg_left hao (by positivity)
    have : (2 : ℝ) ^ 80 * 10 + (1 / 2 ^ 53 * (2 ^ 80 * 10) + 1 / 2 ^ 1075) ≤ 2 ^ 90 := by
      norm_num
    linarith
  refine ⟨hmf, hse, hqe, hoe, hme, ?_⟩
  have := abs_add_le (value t) (value m)
  have : (2 : ℝ) ^ 80 + 2 ^ 90 < 2 ^ 1023 := by norm_num
  linarith

/-- The real error of the odd path, from the rounding of each step. -/
theorem odd_real (W wv av tv zv vv sv qv ov mv : ℝ) (hw0 : 1 / 2 ^ 72 ≤ |wv|) (hw1 : |wv| ≤ 1)
    (hwe : |wv - W| ≤ 𝐮 * |W|) (hwl : |W| * (1 - 𝐮) ≤ |wv|)
    (hα : |av * wv + 1| ≤ 𝐮 + η) (htd : |tv - av| ≤ |av| / 2 ^ 20)
    (hzd : |zv - wv| ≤ |wv| / 2 ^ 20) (hve : |vv - (W - zv)| ≤ 𝐮 * |W - zv|)
    (hse : |sv - (1 + tv * zv)| ≤ 𝐮 * |1 + tv * zv|)
    (hqe : |qv - tv * vv| ≤ 𝐮 * |tv * vv| + η) (hoe : |ov - (sv + qv)| ≤ 𝐮 * |sv + qv|)
    (hme : |mv - av * ov| ≤ 𝐮 * |av * ov| + η) :
    |tv + mv + 1 / W| ≤ 𝐮 / 2 ^ 11 / |W| := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; positivity
  have hwp : 0 < |wv| := lt_of_lt_of_le (by positivity) hw0
  have hwne : wv ≠ 0 := abs_pos.mp hwp
  have hWne : W ≠ 0 := by
    rintro rfl
    rw [sub_zero, abs_zero, mul_zero] at hwe
    linarith
  have hWp : 0 < |W| := abs_pos.mpr hWne
  have hW2 : |W| ≤ 2 * |wv| := by
    have : 𝐮 * |W| ≤ 1 / 2 * |W| :=
      mul_le_mul_of_nonneg_right (by rw [hu]; norm_num) (abs_nonneg W)
    linarith
  have key := comp_real 𝐮 η (av * wv) (tv * wv) (zv / wv) (W / wv) (vv / wv) sv qv ov (wv * mv)
    hu0 (le_of_eq hu) hη0 (by rw [hu, hη]; norm_num) hα
    (by
      rw [show tv * wv - av * wv = (tv - av) * wv by ring, abs_mul, abs_mul]
      calc |tv - av| * |wv| ≤ |av| / 2 ^ 20 * |wv| :=
            mul_le_mul_of_nonneg_right htd (abs_nonneg _)
        _ = |av| * |wv| / 2 ^ 20 := by ring)
    (by
      rw [show zv / wv - 1 = (zv - wv) / wv by rw [sub_div, div_self hwne], abs_div,
        div_le_iff₀ hwp]
      linarith)
    (by
      rw [show W / wv - 1 = (W - wv) / wv by rw [sub_div, div_self hwne], abs_div,
        div_le_iff₀ hwp, abs_sub_comm]
      have : 𝐮 * |W| ≤ 𝐮 * (2 * |wv|) := mul_le_mul_of_nonneg_left hW2 hu0
      linarith)
    (by
      rw [show vv / wv - (W / wv - zv / wv) = (vv - (W - zv)) / wv by rw [sub_div, sub_div],
        show W / wv - zv / wv = (W - zv) / wv by rw [sub_div], abs_div, abs_div,
        div_le_iff₀ hwp]
      calc |vv - (W - zv)| ≤ 𝐮 * |W - zv| := hve
        _ = 𝐮 * (|W - zv| / |wv|) * |wv| := by rw [mul_assoc, div_mul_cancel₀ _ hwp.ne'])
    (by
      rw [show tv * wv * (zv / wv) = tv * zv by
        rw [mul_assoc, mul_comm wv, div_mul_cancel₀ _ hwne]]
      exact hse)
    (by
      rw [show tv * wv * (vv / wv) = tv * vv by
        rw [mul_assoc, mul_comm wv, div_mul_cancel₀ _ hwne]]
      exact hqe)
    hoe
    (by
      have h1 : |wv * mv - av * wv * ov| = |wv| * |mv - av * ov| := by
        rw [← abs_mul]
        congr 1
        ring
      have h2 : |av * wv * ov| = |wv| * |av * ov| := by
        rw [← abs_mul]
        congr 1
        ring
      rw [h1, h2]
      calc |wv| * |mv - av * ov| ≤ |wv| * (𝐮 * |av * ov| + η) :=
            mul_le_mul_of_nonneg_left hme (abs_nonneg _)
        _ = 𝐮 * (|wv| * |av * ov|) + η * |wv| := by ring
        _ ≤ 𝐮 * (|wv| * |av * ov|) + η := by
            have := mul_le_mul_of_nonneg_left hw1 hη0
            linarith)
  rw [show tv * wv + wv * mv + 1 / (W / wv) = wv * (tv + mv + 1 / W) by
    rw [one_div_div]; ring, abs_mul] at key
  rw [le_div_iff₀ hWp]
  have h1 : |tv + mv + 1 / W| * (|W| * (1 - 𝐮)) ≤ |tv + mv + 1 / W| * |wv| :=
    mul_le_mul_of_nonneg_left hwl (abs_nonneg _)
  have h1' : |tv + mv + 1 / W| * (|W| * (1 - 1 / 2 ^ 53)) ≤ |tv + mv + 1 / W| * |wv| := by
    simpa only [hu] using h1
  have key' : |wv| * |tv + mv + 1 / W| ≤ 1 / 2 ^ 53 / 2 ^ 12 + 3 * (1 / 2 ^ 1075) := by
    simpa only [hu, hη] using key
  have h2 : |tv + mv + 1 / W| * |W| ≤ 1 / 2 ^ 53 / 2 ^ 11 := by linarith
  exact h2

theorem odd_spec (x r : UInt64) (X : ℝ) (hxf : Finite x) (hrf : Finite r) (hX : |value x| = X)
    (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 6744 / 10000) (hr : |value r| ≤ X / 5) :
    Finite (oddW x r) ∧ ∃ τ : ℝ, (∀ v : UInt64, |value (oddW x r) - τ| ≤ |value v - τ|) ∧
      |τ + 1 / (value x + value r)| ≤ 𝐮 / 2 ^ 11 / |value x + value r| := by
  obtain ⟨hwf, hwe, hwl, hwu, hw0, hw1, hwx, hWl, hWu⟩ := w_spec x r X hxf hrf hX hX0 hX1 hr
  generalize hw : Wasm.IEEE64.add x r = w at *
  have hew := exp_two w (le_trans (by norm_num) hw0)
  obtain ⟨hvf, hve⟩ := v_spec x r w X hxf hrf hwf hX hX0 hX1 hr hwl hwu hWl hWu hwx hew hw1
  obtain ⟨-, hzc, -, -, hzd, hzb, -⟩ := trunc_spec w hwf (by omega)
  obtain ⟨haf, hα, hal, hab, haw⟩ := a_spec w hwf hw0 hw1
  generalize ha : Wasm.IEEE64.div negOne w = a at *
  have hea := exp_two a (le_trans (by norm_num) hal)
  obtain ⟨htf, htc, -, -, htd, htb, -⟩ := trunc_spec a haf (by omega)
  have hsum := exp_sum a w (by
    have h1 := abs_le.mp hα
    have h2 : 𝐮 + η ≤ 1 / 2 := by
      show (1 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2
      norm_num
    rcases le_or_gt 0 (value a * value w) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith)
  have hsum2 : Wasm.IEEE64.exponent a + Wasm.IEEE64.exponent w ≤ 3000 := by
    have h1 := exp_upper a 81 (lt_of_le_of_lt hab (by norm_num))
    have h2 := exp_upper w 1 (by rw [pow_one]; linarith)
    omega
  obtain ⟨hpf, hpv⟩ := p_spec a w haf hwf hea hew hsum hsum2
  generalize hz : w &&& mask = z at *
  generalize ht : a &&& mask = t at *
  generalize hvv : Wasm.IEEE64.sub r (Wasm.IEEE64.sub z x) = vv at *
  generalize hp : Wasm.IEEE64.mul t z = p at *
  have htw : |value t| * |value w| ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_right htb (abs_nonneg _)) haw
  have hWz : |value x + value r - value z| ≤ |value w| / 2 ^ 19 := by
    have h1 := abs_sub_le (value x + value r) (value w) (value z)
    rw [abs_sub_comm (value x + value r) (value w), abs_sub_comm (value w) (value z)] at h1
    have : 𝐮 * |value x + value r| ≤ |value w| / 2 ^ 20 := by
      have hu : 𝐮 = 1 / 2 ^ 53 := rfl
      rw [hu] at hwl ⊢
      linarith
    linarith
  have hvvb : |value vv| ≤ |value w| / 2 ^ 18 := by
    have := abs_sub_abs_le_abs_sub (value vv) (value x + value r - value z)
    have : 𝐮 * |value x + value r - value z| ≤ |value w| / 2 ^ 19 := by
      have hu : 𝐮 = 1 / 2 ^ 53 := rfl
      rw [hu]
      have := abs_nonneg (value w)
      linarith
    linarith
  have htv : |value t * value vv| ≤ 1 / 2 ^ 17 := by
    rw [abs_mul]
    calc |value t| * |value vv| ≤ |value t| * (|value w| / 2 ^ 18) :=
          mul_le_mul_of_nonneg_left hvvb (abs_nonneg _)
      _ = |value t| * |value w| / 2 ^ 18 := by ring
      _ ≤ 2 / 2 ^ 18 := div_le_div_of_nonneg_right htw (by norm_num)
      _ = 1 / 2 ^ 17 := by norm_num
  have hpb : |value p| ≤ 2 := by
    rw [hpv, abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hzb (abs_nonneg _)) htw
  rw [oddW_eq x r w z a t hw (by rw [hz, hzc]) ha (by rw [ht, htc]), hvv, hp]
  generalize hs : Wasm.IEEE64.add one p = s
  generalize hq : Wasm.IEEE64.mul t vv = q
  generalize ho : Wasm.IEEE64.add s q = o
  generalize hm : Wasm.IEEE64.mul a o = m
  obtain ⟨hmf, hse, hqe, hoe, hme, hcb⟩ := tail_spec t p vv a s q o m hs hq ho hm
    htf hpf hvf haf hpb htv hab (htb.trans hab)
  refine ⟨(F64AddBounds.add_real_relative t m htf hmf hcb).1, value t + value m,
    fun v => F64SignedNearestSum.add_nearest t m htf hmf hcb v, ?_⟩
  rw [hpv] at hse
  exact odd_real _ _ _ _ _ _ _ _ _ _ hw0 hw1 hwe hwl hα htd hzd hve hse hqe hoe hme

#print axioms odd_spec

end Verified.Examples.TanOdd
