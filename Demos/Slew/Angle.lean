import Demos.Slew.Valid
import Library.Numerics.Float64.Atan.AtanTwoTheorem
import Library.Numerics.Float64.Atan.AtanTwoSpecial
import LeanExe.ProofKit.F64NearestHalf
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! The output's axis and angle.  A segment reports the axis `v/s` of its relative quaternion
`rel`, or `+X` when `s` is below `axisMin`, and the angle `2 atan2 s w`.  The rotation angle of
`rel`'s real value is `2 arg (W + i S)` (`angle_eq_two_arg`), and the library's `atan2` lies
within two steps of `arg (w + i s)` (`AtanTwoTheorem.atan2_within_two`), which is within `2⁻⁴⁹`
for an argument in `[0, 2]` (`within_two_abs`).  The argument moves by at most `4 |Δs|` when the
imaginary part moves by `Δs` (`arg_sub_le`), so the output angle lies within `1e-14` of the angle
of `rel`'s real value (`angle_out`).  The computed `s` is finite, since the computed sum of
squares is not negative, and the axis lies within `5.2 u` of the axis of `rel`'s real value
when `s ≥ axisMin` (`axis_out`). -/

namespace Demos.Slew.Angle

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Decide Demos.Slew.Check Demos.Slew.Valid Demos.Slew.Arc
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx Real

set_option exponentiation.threshold 4096

/-! ### The argument -/

open Complex in
theorem angle_eq_two_arg {W S : ℝ} (hW : 0 ≤ W) (hS : 0 ≤ S) (hQ : 0 < W * W + S * S) :
    angle W S = 2 * arg ((W : ℂ) + (S : ℂ) * I) := by
  set z : ℂ := (W : ℂ) + (S : ℂ) * I
  have hre : z.re = W := by simp [z]
  have him : z.im = S := by simp [z]
  have hz : z ≠ 0 := by
    intro h
    have h1 : z.re = 0 := by rw [h]; rfl
    have h2 : z.im = 0 := by rw [h]; rfl
    rw [hre] at h1; rw [him] at h2
    rw [h1, h2] at hQ; norm_num at hQ
  have hn : ‖z‖ = √(W ^ 2 + S ^ 2) := norm_add_mul_I W S
  have hc := cos_arg hz
  rw [hre, hn] at hc
  have h0 : 0 ≤ arg z := arg_nonneg_iff.mpr (by rw [him]; exact hS)
  have h1 : arg z ≤ π / 2 := arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hW))
  unfold angle
  have hQ' : 0 < W ^ 2 + S ^ 2 := by nlinarith
  rw [show (W * W - S * S) / (W * W + S * S) = Real.cos (2 * arg z) by
    rw [Real.cos_two_mul, hc, div_pow, Real.sq_sqrt hQ'.le]
    field_simp
    ring]
  exact arccos_cos (by linarith) (by linarith [pi_pos])

open Complex in
theorem arg_range {W S : ℝ} (hW : 0 ≤ W) (hS : 0 ≤ S) :
    0 ≤ arg ((W : ℂ) + (S : ℂ) * I) ∧ arg ((W : ℂ) + (S : ℂ) * I) ≤ π / 2 :=
  ⟨arg_nonneg_iff.mpr (by simp; exact hS), arg_le_pi_div_two_iff.mpr (Or.inl (by simp; exact hW))⟩

open Complex in
/-- The argument is at most `π/2` times the sine. -/
theorem arg_le_sin {W S : ℝ} (hW : 0 ≤ W) (hS : 0 ≤ S) :
    arg ((W : ℂ) + (S : ℂ) * I) ≤ π / 2 * (S / √(W ^ 2 + S ^ 2)) := by
  obtain ⟨h0, h1⟩ := arg_range hW hS
  have hj := Real.mul_le_sin h0 h1
  have hs := sin_arg ((W : ℂ) + (S : ℂ) * I)
  rw [norm_add_mul_I] at hs
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
    add_zero] at hs
  rw [hs] at hj
  have hpi := pi_pos
  calc arg ((W : ℂ) + (S : ℂ) * I) = π / 2 * (2 / π * arg ((W : ℂ) + (S : ℂ) * I)) := by
        field_simp
    _ ≤ π / 2 * (S / √(W ^ 2 + S ^ 2)) := mul_le_mul_of_nonneg_left hj (by positivity)

open Complex in
/-- The argument of `W + i y` moves by at most `4 |Δy|` while its length stays at least `1/2`. -/
theorem arg_sub_le {W y1 y2 : ℝ} (hW : 0 ≤ W) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2)
    (hz1 : 1 / 2 ≤ √(W ^ 2 + y1 ^ 2)) (hz2 : 1 / 2 ≤ √(W ^ 2 + y2 ^ 2)) :
    |arg ((W : ℂ) + (y1 : ℂ) * I) - arg ((W : ℂ) + (y2 : ℂ) * I)| ≤ 4 * |y1 - y2| := by
  obtain ⟨a10, a11⟩ := arg_range hW h1
  obtain ⟨a20, a21⟩ := arg_range hW h2
  have ne : ∀ y : ℝ, 1 / 2 ≤ √(W ^ 2 + y ^ 2) → (W : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro y hy e
    have := congrArg (fun z : ℂ => ‖z‖) e
    simp only [norm_add_mul_I, norm_zero] at this
    linarith
  have s1 := sin_arg ((W : ℂ) + (y1 : ℂ) * I)
  have c1 := cos_arg (ne y1 hz1)
  have s2 := sin_arg ((W : ℂ) + (y2 : ℂ) * I)
  have c2 := cos_arg (ne y2 hz2)
  simp only [norm_add_mul_I, add_im, add_re, ofReal_im, ofReal_re, mul_im, mul_re, I_im, I_re,
    mul_one, mul_zero, zero_add, sub_zero, add_zero] at s1 c1 s2 c2
  generalize arg ((W : ℂ) + (y1 : ℂ) * I) = a1 at s1 c1 a10 a11 ⊢
  generalize arg ((W : ℂ) + (y2 : ℂ) * I) = a2 at s2 c2 a20 a21 ⊢
  generalize √(W ^ 2 + y1 ^ 2) = r1 at s1 c1 hz1
  generalize hr2d : √(W ^ 2 + y2 ^ 2) = r2 at s2 c2 hz2
  have hr1 : 0 < r1 := by linarith
  have hr2 : 0 < r2 := by linarith
  have hsd : Real.sin (a1 - a2) = W * (y1 - y2) / (r1 * r2) := by
    rw [Real.sin_sub, s1, c1, s2, c2]; field_simp
  have hWr1 : W ≤ r1 := by
    have e1 : Real.sin a1 ^ 2 + Real.cos a1 ^ 2 = 1 := Real.sin_sq_add_cos_sq a1
    rw [s1, c1, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)] at e1
    exact (pow_le_pow_iff_left₀ hW hr1.le two_ne_zero).mp (by nlinarith [sq_nonneg y1])
  have hsabs : |Real.sin (a1 - a2)| ≤ 2 * |y1 - y2| := by
    rw [hsd, abs_div, abs_mul, abs_of_nonneg hW, abs_of_pos (mul_pos hr1 hr2), div_le_iff₀
      (mul_pos hr1 hr2)]
    have hd := abs_nonneg (y1 - y2)
    have e1 := mul_le_mul_of_nonneg_right hWr1 hd
    have e2 := mul_nonneg (mul_nonneg hr1.le hd) (show (0 : ℝ) ≤ 2 * r2 - 1 by linarith)
    nlinarith
  have hpi := pi_pos
  have hjord : 2 / π * |a1 - a2| ≤ |Real.sin (a1 - a2)| := by
    rcases le_total 0 (a1 - a2) with h | h
    · rw [abs_of_nonneg h]
      exact (Real.mul_le_sin h (by linarith)).trans (le_abs_self _)
    · rw [abs_of_nonpos h]
      have := Real.mul_le_sin (x := a2 - a1) (by linarith) (by linarith)
      rw [show a2 - a1 = -(a1 - a2) by ring, Real.sin_neg] at this
      calc 2 / π * -(a1 - a2) ≤ -Real.sin (a1 - a2) := this
        _ ≤ |Real.sin (a1 - a2)| := neg_le_abs _
  have hpi4 : π ≤ 4 := by linarith [pi_lt_four]
  have h3 : 2 / π * |a1 - a2| ≤ 2 * |y1 - y2| := hjord.trans hsabs
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h3
  nlinarith [abs_nonneg (a1 - a2), abs_nonneg (y1 - y2)]

/-! ### Words -/

/-- A finite result whose upper neighbor bounds a positive exact value from above is not
negative. -/
theorem nonneg_of_enclosure {r : UInt64} {e : ℝ} (he : e ≤ value (F64Adjacent.nextUp r))
    (hpos : 0 < e) : 0 ≤ value r := by
  by_contra hneg
  push Not at hneg
  by_cases hs : Wasm.IEEE64.sign r = false
  · linarith [value_nonneg_of_sign hs]
  have hs' : Wasm.IEEE64.sign r = true := by simpa using hs
  have hr63 : 2 ^ 63 ≤ r.toNat := by simpa [Wasm.IEEE64.sign] using hs'
  by_cases h0 : r = 0x8000000000000000
  · rw [h0] at hneg
    have : value (0x8000000000000000 : UInt64) = 0 := by
      have : Wasm.IEEE64.scaledValue (0x8000000000000000 : UInt64) = 0 := by decide
      simp only [value, this]; norm_num
    linarith
  · have hgt : 2 ^ 63 < r.toNat := by
      rcases lt_or_eq_of_le hr63 with h | h
      · exact h
      · exfalso; apply h0; apply UInt64.toNat_inj.mp; rw [← h]; rfl
    have hn : F64Adjacent.nextUp r = r - 1 := by
      have hlt' : ¬ r < 0x8000000000000000 := by
        rw [UInt64.lt_iff_toNat_lt]; simp only [UInt64.reduceToNat]; omega
      simp [F64Adjacent.nextUp, h0, hlt']
    have hs1 : Wasm.IEEE64.sign (r - 1) = true := by
      simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
      simp; omega
    rw [hn] at he
    linarith [value_nonpos_of_sign hs1]

theorem mul_self_nonneg' {c : Float} (hc : Rounding.Fin c) (hr : Rounding.Fin (c * c)) :
    0 ≤ val (c * c) := by
  have hrb : Finite (Wasm.IEEE64.mul c.toBits c.toBits) := by
    rw [← F64Bits.toBits_mul]; exact hr
  have hv : val (c * c) = value (Wasm.IEEE64.mul c.toBits c.toBits) := by
    simp only [val, F64Bits.toBits_mul]
  rw [hv]
  by_cases h0 : value c.toBits = 0
  · have hm : Wasm.IEEE64.scaledMagnitude c.toBits = 0 := by
      have hv0 := h0
      simp only [value, Wasm.IEEE64.scaledValue] at hv0
      split at hv0 <;> simp at hv0 <;> exact_mod_cast hv0
    have h := F64MulBounds.mul_real_adaptive c.toBits c.toBits hc hc (by rw [h0]; norm_num)
    have hb : |value (Wasm.IEEE64.mul c.toBits c.toBits) - value c.toBits * value c.toBits| ≤ 0 := by
      refine h.2.trans (le_of_eq ?_)
      simp [hm]
    rw [h0, mul_zero, sub_zero] at hb
    rw [abs_nonpos_iff.mp hb]
  · have he := (F64Adjacent.mul_enclosure c.toBits c.toBits hc hc hrb).2
    exact nonneg_of_enclosure he (mul_self_pos.mpr h0)

theorem add_nonneg' {a b : Float} (ha : Rounding.Fin a) (hb : Rounding.Fin b)
    (hr : Rounding.Fin (a + b)) (h0a : 0 ≤ val a) (h0b : 0 ≤ val b) : 0 ≤ val (a + b) := by
  have hrb : Finite (Wasm.IEEE64.add a.toBits b.toBits) := by
    rw [← F64Bits.toBits_add]; exact hr
  have hv : val (a + b) = value (Wasm.IEEE64.add a.toBits b.toBits) := by
    simp only [val, F64Bits.toBits_add]
  rw [hv]
  simp only [val] at h0a h0b
  rcases lt_or_eq_of_le (add_nonneg h0a h0b) with hpos | hz
  · exact nonneg_of_enclosure (F64Adjacent.add_enclosure a.toBits b.toBits ha hb hrb).2 hpos
  · have h := F64AddBounds.add_real_relative a.toBits b.toBits ha hb (by rw [← hz]; norm_num)
    rw [← hz, abs_zero, mul_zero] at h
    have := abs_nonpos_iff.mp h.2
    linarith

/-- The computed radicand of a good relative quaternion is not negative. -/
theorem radicand_nonneg {q : Q4} (h : GoodRel q) : 0 ≤ val (radicand q) := by
  have fr := h.fin_radicand
  unfold radicand at fr ⊢
  obtain ⟨f2, fzz⟩ := fin_add fr
  obtain ⟨fxx, fyy⟩ := fin_add f2
  exact add_nonneg' f2 fzz fr (add_nonneg' fxx fyy f2 (mul_self_nonneg' h.fx fxx)
    (mul_self_nonneg' h.fy fyy)) (mul_self_nonneg' h.fz fzz)

/-- The computed length `s` of a good relative quaternion is finite, not negative, and within
`4.1 u S + 2⁻⁴⁹⁹` of `S`. -/
theorem s_facts' {q : Q4} (h : GoodRel q) :
    Rounding.Fin (sOf q) ∧ 0 ≤ val (sOf q) ∧
      |val (sOf q) - √(s2 q)| ≤ 4.1 / 2 ^ 53 * √(s2 q) + 1 / 2 ^ 499 := by
  have hr := h.radApprox
  have hS0 := s2_nonneg q
  have hSs := Real.sqrt_nonneg (s2 q)
  have hrn := radicand_nonneg h
  have hlo := hr.lower
  have hup := hr.upper
  simp only [val] at hrn
  have small : s2 q < 1 / 2 ^ 1000 → √(s2 q) ≤ 1 / 2 ^ 500 := by
    intro hs
    rw [show (1 : ℝ) / 2 ^ 500 = √((1 / 2 ^ 500) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hs ⊢; linarith)
  rcases sqrt_cases h.fin_radicand with ⟨hz, he⟩ | ⟨_, hneg⟩ | ⟨hpos, hfin, hb⟩
  · have hfs : Rounding.Fin (sOf q) := by simp only [sOf]; rw [he]; exact h.fin_radicand
    have hv : val (sOf q) = 0 := by simp only [sOf]; rw [he, hz]
    refine ⟨hfs, hv.ge, ?_⟩
    rw [hv, zero_sub, abs_neg, abs_of_nonneg hSs]
    have : s2 q < 1 / 2 ^ 1000 := by simp only [val] at hz; nlinarith
    have := small this
    have : (1 : ℝ) / 2 ^ 500 ≤ 1 / 2 ^ 499 := by norm_num
    nlinarith
  · simp only [val] at hneg; linarith
  · refine ⟨hfin, ?_, ?_⟩
    · have := (abs_le.mp hb).1
      have h0 := Real.sqrt_nonneg (val (radicand q))
      simp only [sOf]
      nlinarith
    · by_cases hbig : 1 / 2 ^ 1000 ≤ s2 q
      · obtain ⟨bx, byy, bz, _⟩ := h.components
        have hs := (s_approx q h.fx h.fy h.fz (by linarith) (by linarith) (by linarith) hbig).2
        simp only [val]
        have : (0 : ℝ) ≤ 1 / 2 ^ 499 := by norm_num
        linarith
      · push Not at hbig
        have hS := small hbig
        have hrv : val (radicand q) ≤ 1.01 / 2 ^ 1000 := by simp only [val]; nlinarith
        have hsq : √(val (radicand q)) ≤ 1.005 / 2 ^ 500 := by
          rw [show (1.005 : ℝ) / 2 ^ 500 = √((1.005 / 2 ^ 500) ^ 2) by
            rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by norm_num at hrv ⊢; linarith)
        have h1 := abs_le.mp hb
        have h0 := Real.sqrt_nonneg (val (radicand q))
        simp only [sOf]
        rw [abs_le]
        constructor <;> nlinarith

/-! ### Steps -/

theorem tn {i : Nat} (h : i < 2 ^ 64) : (UInt64.ofNat i).toNat = i :=
  UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; exact h)

theorem gap_le (b : UInt64) (hb : b.toNat ≤ 0x4000000000000002) :
    value (b + 1) - value b ≤ 1 / 2 ^ 51 := by
  rw [F64Adjacent.positive_successor_gap b (by omega)]
  have he : b.toNat / 2 ^ 52 - 1 ≤ 1023 := by omega
  calc (2 : ℝ) ^ (b.toNat / 2 ^ 52 - 1) / 2 ^ 1074 ≤ 2 ^ 1023 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) he) (by positivity)
    _ = 1 / 2 ^ 51 := by norm_num

theorem steps_le (a : Nat) : ∀ k : Nat, a + k ≤ 0x4000000000000003 →
    value (UInt64.ofNat (a + k)) - value (UInt64.ofNat a) ≤ k / 2 ^ 51 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have e : UInt64.ofNat (a + (k + 1)) = UInt64.ofNat (a + k) + 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, tn (by omega), tn (by omega)]; simp only [UInt64.reduceToNat]; omega
    have g := gap_le (UInt64.ofNat (a + k)) (by rw [tn (by omega)]; omega)
    rw [e]
    have := ih (by omega)
    push_cast
    linarith

theorem value_small_word {m : Nat} (hm : m ≤ 2) : value (UInt64.ofNat m) ≤ 2 / 2 ^ 1074 := by
  have h2 : value (UInt64.ofNat 2) = 2 / 2 ^ 1074 := by
    have : Wasm.IEEE64.scaledValue (UInt64.ofNat 2) = 2 := by decide
    simp only [value, this]; norm_num
  rw [← h2]
  exact (F64PositiveOrder.value_le_iff (by rw [tn (by omega)]; omega) (by decide)).mpr
    (by rw [tn (by omega), tn (by omega)]; exact hm)

/-- A word within two steps of the reference of `y ∈ [0, 2]` lies within `2⁻⁴⁹` of `y`. -/
theorem within_two_abs {y : ℝ} {w : UInt64} (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (h : F64SignedRounding.WithinSteps 2 y w) : |value w - y| ≤ 1 / 2 ^ 49 := by
  obtain ⟨_, hpos⟩ := h
  have hthr : y < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num; linarith
  have href : F64SignedRounding.roundNearestEven y = F64NearestEven.roundNearestEven y := by
    simp only [F64SignedRounding.roundNearestEven, hy0, ite_true,
      F64PositiveRounding.reference_finite y hthr]
  rw [href] at hpos
  have hnear := (F64NearestEven.roundNearestEven_spec y).1
  set r := F64NearestEven.roundNearestEven y
  have hre : |value r - y| ≤ 1 / 2 ^ 52 := by
    have := F64NearestHalf.nearest_half y r hnear hy0 1023 (by norm_num) (by norm_num; linarith)
    calc |value r - y| ≤ (2 : ℝ) ^ 1023 / 2 / 2 ^ 1074 := this
      _ = 1 / 2 ^ 52 := by norm_num
  have hrlim : r.toNat < 2 ^ 63 := hnear.1.trans (by decide)
  have hr2 : r.toNat ≤ 0x4000000000000000 := by
    by_contra hc
    push Not at hc
    have hv := (F64PositiveOrder.value_le_iff (left := (0x4000000000000001 : UInt64)) (by decide)
      hrlim).mpr (by simp only [UInt64.reduceToNat]; omega)
    have h21 : value (0x4000000000000001 : UInt64) = 2 + 1 / 2 ^ 51 := by
      have : Wasm.IEEE64.scaledValue 0x4000000000000001 = (2 ^ 52 + 1) * 2 ^ 1023 := by
        decide +kernel
      simp only [value, this]; push_cast; ring
    rw [h21] at hv
    have := (abs_le.mp hre).2
    norm_num at this hv
    linarith
  rw [F64SignedRounding.position_of_lt r hrlim] at hpos
  by_cases hws : Wasm.IEEE64.sign w = false
  · have hwlt : w.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hws
    rw [F64SignedRounding.position_of_lt w hwlt] at hpos
    have hd := abs_le.mp hpos
    have hwr : |value w - value r| ≤ 2 / 2 ^ 51 := by
      rcases le_total w.toNat r.toNat with hle | hle
      · have hs := steps_le w.toNat (r.toNat - w.toNat) (by omega)
        rw [show w.toNat + (r.toNat - w.toNat) = r.toNat by omega, UInt64.ofNat_toNat,
          UInt64.ofNat_toNat] at hs
        have hmono := (F64PositiveOrder.value_le_iff hwlt hrlim).mpr hle
        have hk : ((r.toNat - w.toNat : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega)
        rw [abs_le]; constructor
        · have : ((r.toNat - w.toNat : ℕ) : ℝ) / 2 ^ 51 ≤ 2 / 2 ^ 51 :=
            div_le_div_of_nonneg_right hk (by positivity)
          linarith
        · linarith
      · have hs := steps_le r.toNat (w.toNat - r.toNat) (by omega)
        rw [show r.toNat + (w.toNat - r.toNat) = w.toNat by omega, UInt64.ofNat_toNat,
          UInt64.ofNat_toNat] at hs
        have hmono := (F64PositiveOrder.value_le_iff hrlim hwlt).mpr hle
        have hk : ((w.toNat - r.toNat : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega)
        rw [abs_le]; constructor
        · linarith
        · have : ((w.toNat - r.toNat : ℕ) : ℝ) / 2 ^ 51 ≤ 2 / 2 ^ 51 :=
            div_le_div_of_nonneg_right hk (by positivity)
          linarith
    rw [abs_le] at hwr hre ⊢
    constructor <;> norm_num at hwr hre ⊢ <;> linarith [hwr.1, hwr.2, hre.1, hre.2]
  · have hws' : Wasm.IEEE64.sign w = true := by simpa using hws
    have hw63 : 2 ^ 63 ≤ w.toNat := by simpa [Wasm.IEEE64.sign] using hws'
    simp only [F64SignedRounding.position, hws', ite_true] at hpos
    have hd := abs_le.mp hpos
    have hr2' : r.toNat ≤ 2 := by omega
    have hwm : w.toNat - 2 ^ 63 ≤ 2 := by omega
    have hvr : value r ≤ 2 / 2 ^ 1074 := by
      have := value_small_word hr2'; rwa [UInt64.ofNat_toNat] at this
    have hvw : |value w| ≤ 2 / 2 ^ 1074 := by
      rw [← F64UpperWord.value_abs]
      have e : Wasm.IEEE64.abs w = UInt64.ofNat (w.toNat - 2 ^ 63) := by
        apply UInt64.toNat_inj.mp
        rw [F64UpperWord.abs_toNat, tn (by omega)]; omega
      rw [e]; exact value_small_word hwm
    have hr0 : 0 ≤ value r := value_nonneg_of_sign (F64NearestNonnegative.nearest_finite y r hnear).2
    rw [abs_le] at hvw hre ⊢
    constructor <;> norm_num at hvw hre hvr ⊢ <;> linarith [hvw.1, hvw.2, hre.1, hre.2]

/-- A word that is not a NaN and lies within 1 of a number of magnitude at most 2 is finite. -/
theorem finite_of_close {w : UInt64} {y : ℝ} (hn : w.toNat % 2 ^ 63 ≤ 0x7FF0000000000000)
    (hc : |value w - y| ≤ 1) (hy : |y| ≤ 2) : Finite w := by
  by_contra hf
  have he : w.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq, not_not] at hf
    omega
  have e : Wasm.IEEE64.abs w = 0x7FF0000000000000 := by
    apply UInt64.toNat_inj.mp
    rw [F64UpperWord.abs_toNat]; simp only [UInt64.reduceToNat]; omega
  have hv : |value w| = 2 ^ 1024 := by
    rw [← F64UpperWord.value_abs, e]
    have : Wasm.IEEE64.scaledValue 0x7FF0000000000000 = 2 ^ 2098 := by decide +kernel
    simp only [value, this]; norm_num
  have := abs_sub_abs_le_abs_sub (value w) y
  rw [hv] at this
  norm_num at this
  linarith

theorem zero_bits_of {w : UInt64} (hz : value w = 0) :
    w = 0 ∨ w = 0x8000000000000000 := by
  have hm : Wasm.IEEE64.scaledMagnitude w = 0 := by
    simp only [value, Wasm.IEEE64.scaledValue] at hz
    split at hz <;> simp at hz <;> exact_mod_cast hz
  have hef : Wasm.IEEE64.exponent w = 0 ∧ Wasm.IEEE64.fraction w = 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude] at hm
    split at hm
    · rename_i h; exact ⟨by simpa using h, hm⟩
    · exfalso
      have : 0 < (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
        positivity
      omega
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hef
  have hlt := w.toNat_lt
  rcases lt_or_ge w.toNat (2 ^ 63) with h | h
  · left; apply UInt64.toNat_inj.mp; simp only [UInt64.reduceToNat]; omega
  · right; apply UInt64.toNat_inj.mp; simp only [UInt64.reduceToNat]; omega

/-! ### The output's angle and axis -/

theorem angleOf_eq (rel : Q4) :
    angleOf rel = 2.0 * Library.Numerics.Float64.Atan.atan2 (sOf rel) rel.w := rfl

theorem norm_sum_sq_ge {W S : ℝ} (h : 1 / 4 ≤ W * W + S * S) : 1 / 2 ≤ √(W ^ 2 + S ^ 2) := by
  rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- The output angle of a segment lies within `1e-14` of the rotation angle of `rel`'s real
value. -/
theorem angle_out {rel : Q4} (h : GoodRel rel) :
    Rounding.Fin (angleOf rel) ∧ |val (angleOf rel) - angleR rel| ≤ 1e-14 := by
  obtain ⟨fs, s0, sclose⟩ := s_facts' h
  have hSS : √(s2 rel) * √(s2 rel) = s2 rel := Real.mul_self_sqrt (s2_nonneg rel)
  have hQ := abs_le.mp h.norm
  have hW0 := h.w_nonneg
  have hS0 : 0 ≤ √(s2 rel) := Real.sqrt_nonneg _
  have hQpos : 0 < val rel.w * val rel.w + √(s2 rel) * √(s2 rel) := by rw [hSS]; linarith
  have hS1 : √(s2 rel) ≤ 1.0001 := by nlinarith [mul_self_nonneg (val rel.w)]
  have hθ : angleR rel = 2 * Complex.arg ((val rel.w : ℂ) + ((√(s2 rel) : ℝ) : ℂ) * Complex.I) :=
    angle_eq_two_arg hW0 hS0 hQpos
  have hsc := abs_le.mp sclose
  have hd : |val (sOf rel) - √(s2 rel)| ≤ 5e-16 := by
    refine sclose.trans ?_
    have : (1 : ℝ) / 2 ^ 499 ≤ 1e-100 := by norm_num
    have : (4.1 : ℝ) / 2 ^ 53 * 1.0001 ≤ 4.6e-16 := by norm_num
    nlinarith
  have hd' := abs_le.mp hd
  rw [angleOf_eq]
  set A := Library.Numerics.Float64.Atan.atan2 (sOf rel) rel.w
  set V := val (sOf rel)
  have hz1 : 1 / 2 ≤ √(val rel.w ^ 2 + V ^ 2) := by
    apply norm_sum_sq_ge
    have := mul_nonneg hS0 (show 0 ≤ V - √(s2 rel) + 5e-16 by linarith [hd'.1])
    nlinarith [sq_nonneg (V - √(s2 rel))]
  have hz2 : 1 / 2 ≤ √(val rel.w ^ 2 + √(s2 rel) ^ 2) := norm_sum_sq_ge (by linarith)
  have hargV := arg_range hW0 s0
  have hpi := pi_gt_three
  have hpi4 := pi_lt_four
  have hA : Rounding.Fin A ∧
      |val A - Complex.arg ((val rel.w : ℂ) + (V : ℂ) * Complex.I)| ≤ 1 / 2 ^ 49 := by
    by_cases hz : V = 0
    · have hbits := zero_bits_of hz
      have hwpos : 0 < val rel.w := by
        have : √(s2 rel) ≤ 5e-16 := by rw [hz] at hd'; linarith [hd'.1]
        have : s2 rel ≤ 1e-30 := by nlinarith
        nlinarith
      have hws : Wasm.IEEE64.sign rel.w.toBits = false := by
        by_contra hc
        have := value_nonpos_of_sign (by simpa using hc)
        simp only [val] at hwpos; linarith
      have hat := Library.Numerics.Float64.Atan.AtanTwoSpecial.atan2_zero (sOf rel) rel.w hbits
        (not_nan_of_finite h.fw)
      rw [hws] at hat
      simp only [Bool.false_eq_true, ite_false] at hat
      have hvA : val A = 0 := by simp only [val, A, hat]; exact hz
      refine ⟨by simp only [Rounding.Fin, A, hat]; exact fs, ?_⟩
      rw [hvA, hz]
      simp [Complex.arg_ofReal_of_nonneg hW0]
    · have hpos : 0 < V := lt_of_le_of_ne s0 (Ne.symm hz)
      have hw := Library.Numerics.Float64.Atan.AtanTwoTheorem.atan2_within_two (sOf rel) rel.w fs
        h.fw hz
      have habs := within_two_abs hargV.1 (by linarith [hargV.2]) hw
      refine ⟨finite_of_close hw.1 (habs.trans (by norm_num)) ?_, habs⟩
      rw [abs_of_nonneg hargV.1]; linarith [hargV.2]
  obtain ⟨hfA, hAe⟩ := hA
  have hdarg := arg_sub_le hW0 s0 hS0 hz1 hz2
  have hAm : |val A| ≤ 3 := by
    have := abs_le.mp hAe
    rw [abs_le]; constructor <;> norm_num at this ⊢ <;> linarith [hargV.1, hargV.2, this.1, this.2]
  have hb := Bnd.mul (6.001 / 2 ^ 53) Bnd.two (Bnd.of_val hfA hAm) (by norm_num) (by norm_num)
  refine ⟨hb.1.1, ?_⟩
  have hm : |val (2.0 * A) - 2 * val A| ≤ 6.001 / 2 ^ 53 := hb.1.2
  rw [hθ]
  have h1 := abs_le.mp hm
  have h2 := abs_le.mp hAe
  have h3 := abs_le.mp hdarg
  rw [abs_le]
  constructor <;> norm_num at h1 h2 h3 hd' ⊢ <;>
    nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hd'.1, hd'.2, abs_nonneg (V - √(s2 rel))]

theorem axisMin_val : Rounding.Fin Demos.Slew.axisMin ∧ 0.9999e-150 ≤ val Demos.Slew.axisMin ∧
    val Demos.Slew.axisMin ≤ 1.0001e-150 := by
  have hb : Demos.Slew.axisMin.toBits = 0x20CA2FE76A3F9475 := rfl
  have hs : Wasm.IEEE64.scaledValue 0x20CA2FE76A3F9475 = (2 ^ 52 + 0xA2FE76A3F9475) * 2 ^ 523 := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · simp only [Rounding.Fin, hb]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, hb, value, hs]; norm_num
  · simp only [val, hb, value, hs]; norm_num

/-- When the output axis is `v/s`, the vector part of `rel` is not tiny; otherwise it is below
`2e-150`. -/
theorem axis_out {rel : Q4} (h : GoodRel rel) :
    (Demos.Slew.axisMin ≤ sOf rel → 1 / 2 ^ 1000 ≤ s2 rel) ∧
      (¬ Demos.Slew.axisMin ≤ sOf rel → √(s2 rel) ≤ 2e-150) := by
  obtain ⟨fs, s0, sclose⟩ := s_facts' h
  obtain ⟨fa, a1, a2⟩ := axisMin_val
  have hsc := abs_le.mp sclose
  have hS0 := Real.sqrt_nonneg (s2 rel)
  have hp : (1 : ℝ) / 2 ^ 499 ≤ 6.2e-151 := by norm_num
  refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
  · have hv := le_val_of_le hbig
    by_contra hc
    push Not at hc
    have hS : √(s2 rel) ≤ 1 / 2 ^ 500 := by
      rw [show (1 : ℝ) / 2 ^ 500 = √((1 / 2 ^ 500) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num at hc ⊢; linarith)
    have : (1 : ℝ) / 2 ^ 500 ≤ 3.1e-151 := by norm_num
    nlinarith
  · rw [le_iff_val fa fs, not_le] at hsmall
    nlinarith

end Demos.Slew.Angle
