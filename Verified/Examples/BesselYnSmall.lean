import Verified.Examples.BesselYnSteps
import Verified.Examples.BesselYnSmallReal
import Verified.Examples.BesselY0Theorem
import Verified.Examples.BesselY1Theorem

/-!
`yn`'s forward loop for `0 < x < 2` and `2 ≤ n ≤ 2^31` in floating point: the result is negative
infinity and `|Y_n(x)| > 2^1023`, or the result is finite and within `(250 + 12 n) u |Y_n(x)|` of
`Y_n(x)` (`yn_small`).  From `|Y_n(x)| ≥ 2^1025` on the result is negative infinity
(`yn_small_inf`), since a finite double lies below `2^1024`.  These are the statements of the
decision of 2026-10-12 for `yn` below 2.

Below `x = 2^-513` (`yn_tiny`), `y1` returns `-(tpi ⊘ x)` (`y1_code`), which is negative infinity
or at most `-2^511`, and `2 ⊘ x` is positive infinity or at least `2^513`
(`BesselYnSteps.div_pos_big`).  Their product is negative infinity, so the loop stops at the first
or second index with that value, while `|Y_n| ≥ |Y₂| ≥ 4/(π x²) > 2^1026` (`Y2_lower`, `Y_mono`).

From `2^-513` on (`yn_mid`), `y0` and `y1` are finite and within `11 u M₀` and `12 u M₁` of `Y₀` and
`Y₁` (`y0_facts`, `y1_facts`), and every quotient `2k ⊘ x` lies within `u λ_k + 2^-1075` of
`λ_k = 2k/x ≤ 2^546`.  While the values are finite, `BesselYnSteps.step_fin` bounds each step's
error as `BesselYnSmallReal.small_error` requires.  If some value is not finite, let `K` be the
first such index.  The values before `K` are accurate, and `|Y_(K-2)| ≤ (3/4) |Y_K|` below 2
(`Y31`, `Y_double`), so `|Y_K| ≤ 2^1023` would keep `λ_(K-1) |f_(K-1)|` and
`|λ_(K-1) f_(K-1) - f_(K-2)|` below `2^1024 - 2^1019` and make the step to `K` finite
(`step_bounds`, `BesselYnSteps.step_mag`).  Hence `|Y_K| > 2^1023`, the value at `K - 1` is
negative, the value at `K` is negative infinity (`BesselYnSteps.step_inf`), and the loop stops
there.
-/

namespace Verified.Examples.BesselYnSmall
open Real CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.EntireSeries LeanExe.ProofKit.Bessel
  PolyBound F64Approx BesselPQEval BesselOrderN BesselRecur BesselSmallSigns BesselYnSmallReal
  BesselStepF BesselOrderLoops BesselYnSteps BesselY1Tiny

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 4096

theorem value_513 : value (0x1FE0000000000000 : UInt64) = 1 / 2 ^ 513 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x1FE0000000000000 = 1 / 2 ^ 513 := by decide +kernel
  rw [this]; norm_num

theorem value_p511 : value (0x5FE0000000000000 : UInt64) = 2 ^ 511 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x5FE0000000000000 = 2 ^ 511 := by decide +kernel
  rw [this]; norm_num

theorem value_p513 : value (0x6000000000000000 : UInt64) = 2 ^ 513 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x6000000000000000 = 2 ^ 513 := by decide +kernel
  rw [this]; norm_num

theorem pos_value (w : UInt64) (hpos : w.toNat < 2 ^ 63) (hnz : w.toNat ≠ 0) : 0 < value w := by
  have h := F64PositiveOrder.value_strict (left := (0 : UInt64)) (right := w) hpos
    (by simp only [UInt64.toNat_zero]; omega)
  rwa [F64Magnitude.value_zero] at h

theorem sign_of_neg (w : UInt64) (h : value w < 0) : Wasm.IEEE64.sign w = true := by
  by_contra hs
  have := F64TwoSum.value_nonneg_of_sign w (by simpa using hs)
  linarith

theorem mag_ne_zero (w : UInt64) (h : value w ≠ 0) : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
  intro h0
  apply h
  simp only [value, Wasm.IEEE64.scaledValue, h0]
  split <;> simp

/-- `|Y_k|` is nondecreasing from `k = 1` below 2. -/
theorem Y_mono (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) (k : ℕ) (hk : 1 ≤ k) :
    ∀ m, k ≤ m → -Yn w k ≤ -Yn w m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hkm ih => exact ih.trans (g_mono w hw0 hw2 m (by omega))

/-- `|Y₂| ≥ 4/(π x²)` below 2, from the cross product `J₁ |Y₂| = 2/(π x) + J₂ |Y₁|`. -/
theorem Y2_lower (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : 4 / (π * w ^ 2) ≤ -Yn w 2 := by
  have hc := cross w hw0.ne' 1
  obtain ⟨hJ1p, hJ1⟩ := J1_le w hw0 hw2
  have hJ2 := Jn_pos 2 w hw0 hw2.le
  have hY1 := Y_neg w hw0 hw2.le 1 le_rfl
  have hY2 : 0 < -Yn w 2 := by have := Y_neg w hw0 hw2.le 2 (by norm_num); linarith
  have h2 : Jn 1 w * -Yn w 2 = 2 / (π * w) + Jn 2 w * -Yn w 1 := by
    show Jn 1 w * -Yn w (1 + 1) = _
    linarith
  have h3 : 2 / (π * w) ≤ Jn 1 w * -Yn w 2 := by
    have : 0 ≤ Jn 2 w * -Yn w 1 := mul_nonneg hJ2.le (by linarith)
    linarith
  have h4 : Jn 1 w * -Yn w 2 ≤ w / 2 * -Yn w 2 := mul_le_mul_of_nonneg_right hJ1 hY2.le
  have hpw : 0 < π * w := by positivity
  calc 4 / (π * w ^ 2) = 2 / w * (2 / (π * w)) := by field_simp; ring
    _ ≤ 2 / w * (w / 2 * -Yn w 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = -Yn w 2 := by field_simp

/-- `|Y₁| ≤ 4/x` below 2, from `π J₁ |Y₁| ≤ 2` and `J₁ ≥ x/6`. -/
theorem Y1_upper (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : -Yn w 1 ≤ 4 / w := by
  have hJ := (Jn_bounds 1 w hw0.le hw2.le).1
  have e1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
  have e2 : ((Nat.factorial (1 + 1) : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [e1, e2, pow_one] at hJ
  have hw4 : w ^ 2 ≤ 4 := by nlinarith
  have hJ1 : w / 6 ≤ Jn 1 w := by nlinarith [mul_le_mul_of_nonneg_left hw4 hw0.le]
  have ha := (a1_bounds w hw0 hw2).1
  have hg : 0 < -Yn w 1 := by have := Y_neg w hw0 hw2.le 1 le_rfl; linarith
  have hpi := Real.pi_gt_three
  have h3 : 3 * Jn 1 w ≤ π * Jn 1 w :=
    mul_le_mul_of_nonneg_right hpi.le (Jn_pos 1 w hw0 hw2.le).le
  have h4 : 3 * (w / 6) * -Yn w 1 ≤ π * Jn 1 w * -Yn w 1 :=
    mul_le_mul_of_nonneg_right (by linarith) hg.le
  rw [le_div_iff₀ hw0]
  linarith

/-- `|Y_(k+2)| ≥ 2 |Y_k|` below 2 for `k ≥ 2`, since `λ_(k+1) ≥ 3` and `|Y_(k+1)| ≥ |Y_k|`. -/
theorem Y_double (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) (k : ℕ) (hk : 2 ≤ k) :
    2 * -Yn w k ≤ -Yn w (k + 2) := by
  have hr : Yn w (k + 2) = 2 * ((k : ℝ) + 1) / w * Yn w (k + 1) - Yn w k := Yn_recur w k
  have hl : 3 ≤ 2 * ((k : ℝ) + 1) / w := by
    rw [le_div_iff₀ hw0]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hm := g_mono w hw0 hw2 k (by omega)
  have hg : 0 < -Yn w (k + 1) := by have := Y_neg w hw0 hw2.le (k + 1) (by omega); linarith
  have h := mul_le_mul_of_nonneg_right hl hg.le
  rw [hr]
  nlinarith

/-- `4 |Y₁| ≤ 3 |Y₃|` below 2, from `J₁ |Y₂| ≥ (J₁ + J₂) |Y₁|` and `J₂ ≥ 1/6` from `12/7` on. -/
theorem Y31 (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : 4 * -Yn w 1 ≤ 3 * -Yn w 3 := by
  have hc := cross w hw0.ne' 1
  obtain ⟨hJ1p, hJ1⟩ := J1_le w hw0 hw2
  have hJ2 := Jn_pos 2 w hw0 hw2.le
  have hg1 : 0 < -Yn w 1 := by have := Y_neg w hw0 hw2.le 1 le_rfl; linarith
  have ha := (a1_bounds w hw0 hw2).2
  have hpw : 0 < π * w := by positivity
  have h1 : Jn 1 w * -Yn w 1 ≤ 2 / (π * w) := by
    rw [le_div_iff₀ hpw]
    nlinarith
  have h2 : Jn 1 w * -Yn w 2 = 2 / (π * w) + Jn 2 w * -Yn w 1 := by
    show Jn 1 w * -Yn w (1 + 1) = _
    linarith
  have h3 : (Jn 1 w + Jn 2 w) * -Yn w 1 ≤ Jn 1 w * -Yn w 2 := by nlinarith
  have h4 : 7 / 3 * Jn 1 w ≤ 4 / w * (Jn 1 w + Jn 2 w) := by
    have hs : (0 : ℝ) ≤ Jn 1 w + Jn 2 w := by linarith
    by_cases hw : w ≤ 12 / 7
    · have h7 : 7 / 3 ≤ 4 / w := by rw [le_div_iff₀ hw0]; linarith
      nlinarith [mul_le_mul_of_nonneg_right h7 hs]
    · push Not at hw
      have hJ := (Jn_bounds 2 w hw0.le hw2.le).1
      have e2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
      have e3 : ((Nat.factorial (2 + 1) : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [e2, e3] at hJ
      have hz1 : 0 ≤ w ^ 2 - 144 / 49 := by nlinarith
      have hz2 : 0 ≤ 4 - w ^ 2 := by nlinarith
      have hz := mul_nonneg hz1 hz2
      have hJ2' : 1 / 6 ≤ Jn 2 w := by nlinarith
      have h2w : 2 ≤ 4 / w := by rw [le_div_iff₀ hw0]; linarith
      nlinarith [mul_le_mul_of_nonneg_right h2w hs]
  have h5 : 7 / 3 * Jn 1 w * -Yn w 1 ≤ 4 / w * (Jn 1 w * -Yn w 2) := by
    have h6 := mul_le_mul_of_nonneg_right h4 hg1.le
    have h7 : 4 / w * ((Jn 1 w + Jn 2 w) * -Yn w 1) ≤ 4 / w * (Jn 1 w * -Yn w 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have h8 : 7 / 3 * -Yn w 1 ≤ 4 / w * -Yn w 2 := by
    have : Jn 1 w * (7 / 3 * -Yn w 1) ≤ Jn 1 w * (4 / w * -Yn w 2) := by nlinarith
    exact le_of_mul_le_mul_left this hJ1p
  have e : Yn w 3 = 4 / w * Yn w 2 - Yn w 1 := by
    have h := Yn_recur w 1
    simp only [Nat.reduceAdd, Nat.cast_one] at h
    rw [h]
    ring
  rw [e]
  linarith

/-- `|Y₀(x)| ≤ -ln x + 2` for `0 < x ≤ 1/2`, from the series. -/
theorem Y0_log_abs (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 2) : |Y0 w| ≤ -Real.log w + 2 := by
  have hz0 : 0 ≤ w ^ 2 / 4 := by positivity
  have hz1 : w ^ 2 / 4 ≤ 1 := by nlinarith
  have hza : |w ^ 2 / 4| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hc := c0_remainder (w ^ 2 / 4) hza 1 (by norm_num)
  rw [c0_list1, abs_c0_1, abs_of_nonneg hz0] at hc
  simp only [eval_cons, eval_nil, Rat.cast_zero, mul_zero, add_zero, pow_one, sub_zero] at hc
  have hC : |psum c0 (w ^ 2 / 4)| ≤ 1 / 2 := by nlinarith
  have hJ0 := (j0y0_bounds w hw0 (by linarith)).1
  have hlog : Real.log (w / 2) = Real.log w - Real.log 2 := Real.log_div hw0.ne' two_ne_zero
  have hl0 : Real.log w ≤ 0 := Real.log_nonpos hw0.le (by linarith)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 := BesselModSmall.gamma_ge
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hL : |Real.log (w / 2) + eulerMascheroniConstant| ≤ -Real.log w + 1 := by
    rw [abs_le, hlog]; constructor <;> linarith
  have hL0 : 0 ≤ -Real.log w + 1 := by linarith
  have h2 : |Real.log (w / 2) + eulerMascheroniConstant| * |J0 w| ≤ -Real.log w + 1 := by
    calc _ ≤ (-Real.log w + 1) * 1 := mul_le_mul hL hJ0 (abs_nonneg _) hL0
      _ = _ := mul_one _
  have hpi : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  unfold Y0
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / π)]
  have h1 := abs_add_le ((Real.log (w / 2) + eulerMascheroniConstant) * J0 w)
    (psum c0 (w ^ 2 / 4))
  rw [abs_mul] at h1
  have h3 : |(Real.log (w / 2) + eulerMascheroniConstant) * J0 w + psum c0 (w ^ 2 / 4)| ≤
      -Real.log w + 2 := by linarith
  calc 2 / π * _ ≤ 1 * (-Real.log w + 2) := mul_le_mul hpi h3 (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- `M₀ ≤ 2^10` for `2^-1074 ≤ x < 2`. -/
theorem M0_le (w : ℝ) (hmin : 1 / 2 ^ 1074 ≤ w) (hw2 : w < 2) : modn w 0 ≤ 2 ^ 10 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hmin
  obtain ⟨hJ0, hY0b⟩ := j0y0_bounds w hw0 hw2
  have hY0 : |Y0 w| ≤ 747 := by
    by_cases hh : w ≤ 1 / 2
    · obtain ⟨-, -, hl⟩ := BesselY0Small.log_facts w hmin hh
      have := Y0_log_abs w hw0 hh
      linarith
    · push Not at hh
      have h1 : 2 / w ≤ 4 := by rw [div_le_iff₀ hw0]; linarith
      have h1' : 1 ≤ 2 / w := by rw [le_div_iff₀ hw0]; linarith
      have h2 : w ^ 2 / 2 ≤ 2 := by nlinarith
      have h3 : 0 ≤ 2 / w - 1 / 3 + w ^ 2 / 2 := by nlinarith [sq_nonneg w]
      have hpi : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      have : 2 / π * (2 / w - 1 / 3 + w ^ 2 / 2) ≤ 1 * 6 :=
        mul_le_mul hpi (by linarith) h3 (by norm_num)
      linarith
  unfold modn
  rw [Jn_zero, Yn_zero]
  have := sqrt_le_add (J0 w) (Y0 w)
  linarith

/-- `y0` below 2: finite and within `11 u M₀` of `Y₀`, with `M₀ ≤ 2^10`. -/
theorem y0_facts (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) (hw2 : value x.toBits < 2) :
    Finite (Bessel.y0 x).toBits ∧
      |value (Bessel.y0 x).toBits - Yn (value x.toBits) 0| ≤ 11 * 𝐮 * modn (value x.toBits) 0 ∧
      modn (value x.toBits) 0 ≤ 2 ^ 10 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 := pos_value x.toBits hpos hnz
  have hM := M0_le _ (BesselY0Small.value_ge_min x.toBits hpos hw0) hw2
  have e0 : modn (value x.toBits) 0 = √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) := by
    unfold modn; rw [Jn_zero, Yn_zero]
  have h := BesselY0Theorem.y0_accuracy x hxf hpos hnz
  have hv : |value (Bessel.y0 x).toBits - Yn (value x.toBits) 0| ≤
      11 * 𝐮 * modn (value x.toBits) 0 := by
    rw [Yn_zero, e0, hu]
    convert h using 1
    ring
  refine ⟨finite_of_abs_lt _ ?_, hv, hM⟩
  have hY := Y_le_modn (value x.toBits) 0
  have := abs_sub_abs_le_abs_sub (value (Bessel.y0 x).toBits) (Yn (value x.toBits) 0)
  have hM0 : 0 ≤ modn (value x.toBits) 0 := Real.sqrt_nonneg _
  have : 11 * 𝐮 * modn (value x.toBits) 0 ≤ modn (value x.toBits) 0 := by rw [hu]; nlinarith
  have : (2 : ℝ) ^ 10 * 2 < 2 ^ 1024 := by norm_num
  linarith

/-- `y1` from `2^-513` to 2: finite and within `12 u M₁` of `Y₁`, with `M₁ ≤ 2^516`. -/
theorem y1_facts (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnorm : 0x0010000000000000 ≤ x.toBits.toNat) (hw513 : 1 / 2 ^ 513 ≤ value x.toBits)
    (hw2 : value x.toBits < 2) :
    Finite (Bessel.y1 x).toBits ∧
      |value (Bessel.y1 x).toBits - Yn (value x.toBits) 1| ≤ 12 * 𝐮 * modn (value x.toBits) 1 ∧
      modn (value x.toBits) 1 ≤ 2 ^ 516 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 : 0 < value x.toBits := lt_of_lt_of_le (by positivity) hw513
  have e1 : modn (value x.toBits) 1 = √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2) := by
    unfold modn; rw [Jn_one, Yn_one]
  have h := BesselY1Theorem.y1_accuracy x hxf hpos hnorm
  have hv : |value (Bessel.y1 x).toBits - Yn (value x.toBits) 1| ≤
      12 * 𝐮 * modn (value x.toBits) 1 := by
    rw [Yn_one, e1, hu]
    convert h using 1
    ring
  have hM : modn (value x.toBits) 1 ≤ 2 ^ 516 := by
    obtain ⟨hJp, hJ⟩ := J1_le _ hw0 hw2
    have hY := Y1_upper _ hw0 hw2
    have hYn := Y_neg _ hw0 hw2.le 1 le_rfl
    have h4 : 4 / value x.toBits ≤ 2 ^ 515 := by
      rw [div_le_iff₀ hw0]
      have : (2 : ℝ) ^ 515 * (1 / 2 ^ 513) ≤ 2 ^ 515 * value x.toBits :=
        mul_le_mul_of_nonneg_left hw513 (by positivity)
      have e : (2 : ℝ) ^ 515 * (1 / 2 ^ 513) = 4 := by norm_num
      linarith
    unfold modn
    have := sqrt_le_add (Jn 1 (value x.toBits)) (Yn (value x.toBits) 1)
    rw [abs_of_pos hJp, abs_of_neg hYn] at this
    have : (1 : ℝ) + 2 ^ 515 ≤ 2 ^ 516 := by norm_num
    linarith
  refine ⟨finite_of_abs_lt _ ?_, hv, hM⟩
  have hY := Y_le_modn (value x.toBits) 1
  have := abs_sub_abs_le_abs_sub (value (Bessel.y1 x).toBits) (Yn (value x.toBits) 1)
  have hM0 : 0 ≤ modn (value x.toBits) 1 := Real.sqrt_nonneg _
  have : 12 * 𝐮 * modn (value x.toBits) 1 ≤ modn (value x.toBits) 1 := by rw [hu]; nlinarith
  have : (2 : ℝ) ^ 516 * 2 < 2 ^ 1024 := by norm_num
  linarith

/-- `y1` below the high word `0x3c900000` is `-(tpi ⊘ x)`. -/
theorem y1_code (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) (ht : x.toBits.toNat < 0x3C90000100000000)
    (hX0 : Wasm.IEEE64.scaledMagnitude x.toBits ≠ 0) :
    (Bessel.y1 x).toBits = Wasm.IEEE64.negate (Wasm.IEEE64.div tpiWord x.toBits) := by
  have hixN := TrigSinCos.high_word x.toBits
  have hN : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hpos
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by
      rw [BesselSpecial.double_zero, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by
      rw [BesselSpecial.sign_bit, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_left (show x.toBits >>> 32 &&& 2147483647 ≤ 1016070144 by
      rw [UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have hTf : Finite tpiWord := by unfold tpiWord CodeLib.IEEE64.Finite; decide
  have hneg : (-Bessel.tpi).toBits = Wasm.IEEE64.negate tpiWord := by
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, tpi_bits, not_nan_of_finite hTf]
    simp only [Bool.false_eq_true, ite_false]
  rw [F64Bits.toBits_div, hneg, F64NegateOps.div_negate_left tpiWord x.toBits hTf hxf hX0]

/-- **`yn`'s loop below `2^-513`**: the result is negative infinity and `|Y_n| > 2^1023`. -/
theorem yn_tiny (x : Float) (n : UInt64) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) (ht : x.toBits.toNat < 0x1FE0000000000000) (hn1 : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31) :
    (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
        (ystep x)).2.2.toBits = 0xFFF0000000000000 ∧
      2 ^ 1023 < -Yn (value x.toBits) n.toNat := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 := pos_value x.toBits hpos hnz
  have hwt : value x.toBits < 1 / 2 ^ 513 := by
    rw [← value_513]
    exact F64PositiveOrder.value_strict (by decide) ht
  have hw2 : value x.toBits < 2 := by linarith [show (1 : ℝ) / 2 ^ 513 < 2 by norm_num]
  refine ⟨?_, ?_⟩
  · have hf0 := (y0_facts x hxf hpos hnz hw2).1
    have hXs : Wasm.IEEE64.sign x.toBits = false := F64Exact.sign_of_pos _ hw0
    have hX0 := mag_ne_zero x.toBits hw0.ne'
    have hy1 := y1_code x hxf hpos hnz (by omega) hX0
    have hTf : Finite tpiWord := by unfold tpiWord CodeLib.IEEE64.Finite; decide
    have hTs : Wasm.IEEE64.sign tpiWord = false := by decide
    have hT := tpi_value
    have h2pi := BesselModSmall.two_div_pi_ge
    have hTv : 6365 / 10000 ≤ value tpiWord := by
      rw [hu] at hT; linarith [(abs_le.mp hT).1]
    have hs1 : 2 * value (0x5FE0000000000000 : UInt64) ≤ value tpiWord / value x.toBits := by
      rw [value_p511, le_div_iff₀ hw0]
      have h1 : (2 : ℝ) * 2 ^ 511 * value x.toBits ≤ 2 * 2 ^ 511 * (1 / 2 ^ 513) :=
        mul_le_mul_of_nonneg_left hwt.le (by positivity)
      have h2 : (2 : ℝ) * 2 ^ 511 * (1 / 2 ^ 513) = 1 / 2 := by norm_num
      linarith
    have hlo1 : 1 / 2 ^ 1022 ≤ value tpiWord / value x.toBits := by
      rw [value_p511] at hs1
      have : (1 : ℝ) / 2 ^ 1022 ≤ 2 * 2 ^ 511 := by norm_num
      linarith
    rcases div_pos_big tpiWord x.toBits 0x5FE0000000000000 hTf hxf hTs hXs (by decide)
      (by rw [value_p511]; positivity) hlo1 hs1 with hc | ⟨hcf, -, hcv⟩
    · have hinf : (ya x (Bessel.y0 x) (Bessel.y1 x) 1).toBits = 0xFFF0000000000000 := by
        show (Bessel.y1 x).toBits = _
        rw [hy1, hc, F64NegateOps.negate_infinity]
        decide
      rw [loop_stop x _ _ n 1 le_rfl (by omega) hn2 (fun j h1 h2 => absurd h2 (by omega)) hinf]
      exact hinf
    · obtain ⟨hf1, hv1⟩ := F64Magnitude.negate_value _ hcf
      rw [← hy1] at hf1 hv1
      rw [value_p511] at hcv
      have hv1' : value (Bessel.y1 x).toBits ≤ -2 ^ 511 := by rw [hv1]; linarith
      have hs1' := sign_of_neg _ (show value (Bessel.y1 x).toBits < 0 by
        linarith [show (0 : ℝ) < 2 ^ 511 by positivity])
      have hm1 := mag_ne_zero _ (show value (Bessel.y1 x).toBits ≠ 0 by
        linarith [show (0 : ℝ) < 2 ^ 511 by positivity])
      -- the quotient `2 ⊘ x`
      have hW := two_mul_word' 0 (by norm_num)
      obtain ⟨htf, htv⟩ := toFloat_exact (2 * UInt64.ofNat (0 + 1)) (by rw [hW]; norm_num)
      have htv' : value (2 * UInt64.ofNat (0 + 1)).toFloat.toBits = 2 := by
        rw [hW] at htv
        have := abs_nonpos_iff.mp htv
        rw [sub_eq_zero] at this
        rw [this]
        norm_num
      have hts := F64Exact.sign_of_pos _
        (show 0 < value (2 * UInt64.ofNat (0 + 1)).toFloat.toBits by rw [htv']; norm_num)
      have hs2 : 2 * value (0x6000000000000000 : UInt64) ≤
          value (2 * UInt64.ofNat (0 + 1)).toFloat.toBits / value x.toBits := by
        rw [value_p513, htv', le_div_iff₀ hw0]
        have h1 : (2 : ℝ) * 2 ^ 513 * value x.toBits ≤ 2 * 2 ^ 513 * (1 / 2 ^ 513) :=
          mul_le_mul_of_nonneg_left hwt.le (by positivity)
        have h2 : (2 : ℝ) * 2 ^ 513 * (1 / 2 ^ 513) = 2 := by norm_num
        linarith
      have hlo2 :
          1 / 2 ^ 1022 ≤ value (2 * UInt64.ofNat (0 + 1)).toFloat.toBits / value x.toBits := by
        rw [value_p513] at hs2
        have : (1 : ℝ) / 2 ^ 1022 ≤ 2 * 2 ^ 513 := by norm_num
        linarith
      have hp : Wasm.IEEE64.mul (Wasm.IEEE64.div (2 * UInt64.ofNat (0 + 1)).toFloat.toBits x.toBits)
          (Bessel.y1 x).toBits = Wasm.IEEE64.infinity true := by
        rcases div_pos_big _ x.toBits 0x6000000000000000 htf hxf hts hXs (by decide)
          (by rw [value_p513]; positivity) hlo2 hs2 with hq | ⟨hqf, hqs, hqv⟩
        · rw [hq, mul_inf_left false _ hf1 hm1, hs1']
          rfl
        · rw [value_p513] at hqv
          have hov : 2 ^ 1024 - 2 ^ 970 ≤
              |value (Wasm.IEEE64.div (2 * UInt64.ofNat (0 + 1)).toFloat.toBits x.toBits) *
                value (Bessel.y1 x).toBits| := by
            rw [abs_mul, abs_of_pos (by linarith [show (0 : ℝ) < 2 ^ 513 by positivity]),
              abs_of_neg (by linarith [show (0 : ℝ) < 2 ^ 511 by positivity])]
            have := mul_le_mul hqv (show (2 : ℝ) ^ 511 ≤ -value (Bessel.y1 x).toBits by linarith)
              (by positivity) (by linarith [show (0 : ℝ) < 2 ^ 513 by positivity])
            have e : (2 : ℝ) ^ 513 * 2 ^ 511 = 2 ^ 1024 := by norm_num
            linarith [show (0 : ℝ) < 2 ^ 970 by positivity]
          rw [mul_nonfinite _ _ hqf hf1 (mul_overflow _ _ hqf hf1 hov), hqs, hs1']
          rfl
      have hinf : (ya x (Bessel.y0 x) (Bessel.y1 x) 2).toBits = 0xFFF0000000000000 := by
        show ((((2 * UInt64.ofNat (0 + 1)).toFloat / x) * Bessel.y1 x) - Bessel.y0 x).toBits = _
        rw [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div, hp, sub_inf true _ hf0]
        exact neg_inf_bits
      rw [loop_stop x _ _ n 2 (by norm_num) hn1 hn2
        (fun j h1 h2 => by obtain rfl : j = 1 := (by omega); exact hf1) hinf]
      exact hinf
  · have h2 := Y2_lower _ hw0 hw2
    have hm := Y_mono _ hw0 hw2 2 (by norm_num) n.toNat hn1
    have hsq : value x.toBits ^ 2 ≤ 1 / 2 ^ 1026 := by
      have : value x.toBits ^ 2 ≤ (1 / 2 ^ 513) ^ 2 := pow_le_pow_left₀ hw0.le hwt.le 2
      have e : ((1 : ℝ) / 2 ^ 513) ^ 2 = 1 / 2 ^ 1026 := by norm_num
      linarith
    have : (2 : ℝ) ^ 1023 < 4 / (π * value x.toBits ^ 2) := by
      rw [lt_div_iff₀ (by positivity)]
      have hpi := Real.pi_lt_four
      have h1 : π * value x.toBits ^ 2 ≤ 4 * (1 / 2 ^ 1026) :=
        mul_le_mul hpi.le hsq (by positivity) (by norm_num)
      have h3 : (2 : ℝ) ^ 1023 * (π * value x.toBits ^ 2) ≤ 2 ^ 1023 * (4 * (1 / 2 ^ 1026)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : (2 : ℝ) ^ 1023 * (4 * (1 / 2 ^ 1026)) = 1 / 2 := by norm_num
      linarith
    linarith

/-- The magnitudes in the step to an index `k + 2` with `|Y_(k+2)| ≤ 2^1023`: with
`g = -Y`, `λ g_(k+1) = g_(k+2) + g_k`, `|g_k| ≤ 3 · 2^1021`, and the values within the stated
distances. -/
theorem step_bounds {L ga gb gc vb va : ℝ} (hL : 0 ≤ L) (hgb : 0 ≤ gb) (hgc0 : 0 ≤ gc)
    (hgc : gc ≤ 2 ^ 1023) (hga : |ga| ≤ 3 * 2 ^ 1021) (hrec : L * gb = gc + ga)
    (hb : L * |vb + gb| ≤ 2 ^ 1019) (ha : |va + ga| ≤ 2 ^ 1019) :
    L * |vb| ≤ 2 ^ 1024 - 2 ^ 1019 ∧ |L * vb - va| ≤ 2 ^ 1024 - 2 ^ 1019 := by
  constructor
  · have h1 : |vb| ≤ |vb + gb| + gb := by
      have := abs_sub (vb + gb) gb
      rw [add_sub_cancel_right, abs_of_nonneg hgb] at this
      exact this
    have h2 : L * |vb| ≤ L * (|vb + gb| + gb) := mul_le_mul_of_nonneg_left h1 hL
    have h3 : L * (|vb + gb| + gb) = L * |vb + gb| + L * gb := mul_add _ _ _
    have := le_abs_self ga
    have : (2 : ℝ) ^ 1023 + 3 * 2 ^ 1021 + 2 ^ 1019 ≤ 2 ^ 1024 - 2 ^ 1019 := by norm_num
    linarith
  · have e : L * vb - va = L * (vb + gb) - (va + ga) - gc := by linear_combination (-1 : ℝ) * hrec
    rw [e]
    have h1 := abs_sub (L * (vb + gb) - (va + ga)) gc
    have h2 := abs_sub (L * (vb + gb)) (va + ga)
    rw [abs_mul, abs_of_nonneg hL] at h2
    rw [abs_of_nonneg hgc0] at h1
    have : (2 : ℝ) ^ 1019 + 2 ^ 1019 + 2 ^ 1023 ≤ 2 ^ 1024 - 2 ^ 1019 := by norm_num
    linarith

set_option maxHeartbeats 1000000 in
/-- **`yn`'s loop from `2^-513` to 2.** -/
theorem yn_mid (x : Float) (n : UInt64) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hlo : 0x1FE0000000000000 ≤ x.toBits.toNat) (hw2 : value x.toBits < 2)
    (hn1 : 2 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31) :
    ((LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
        (ystep x)).2.2.toBits = 0xFFF0000000000000 ∧ 2 ^ 1023 < -Yn (value x.toBits) n.toNat) ∨
      (Finite (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
          (ystep x)).2.2.toBits ∧
        |value (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
          (ystep x)).2.2.toBits - Yn (value x.toBits) n.toNat| ≤
          (250 + 12 * (n.toNat : ℝ)) * 𝐮 * -Yn (value x.toBits) n.toNat) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw513 : 1 / 2 ^ 513 ≤ value x.toBits := by
    rw [← value_513]
    exact (F64PositiveOrder.value_le_iff (by decide) hpos).mpr hlo
  obtain ⟨hf0, he0, hM0⟩ := y0_facts x hxf hpos (by omega) hw2
  obtain ⟨hf1, he1, hM1⟩ := y1_facts x hxf hpos (by omega) hw513 hw2
  obtain ⟨w, hwx⟩ : ∃ w, w = value x.toBits := ⟨_, rfl⟩
  rw [← hwx] at hw2 hw513 he0 hM0 he1 hM1 ⊢
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw513
  have hx : FApprox x w 0 := by rw [hwx]; exact fapprox_exact x hxf
  -- the quotients `2 (k + 1) ⊘ x`
  have hq : ∀ k, k + 2 ≤ n.toNat →
      Finite ((2 * UInt64.ofNat (k + 1)).toFloat / x).toBits ∧
      |value ((2 * UInt64.ofNat (k + 1)).toFloat / x).toBits - lam w (k + 1)| ≤
        lam w (k + 1) / 2 ^ 53 + 1 / 2 ^ 1075 ∧ 1 ≤ lam w (k + 1) ∧ lam w (k + 1) ≤ 2 ^ 546 := by
    intro k hk
    have hk40 : k < 2 ^ 40 := by omega
    obtain ⟨ht, hl⟩ :=
      lam_word (w := w) k hk40 (2 * UInt64.ofNat (k + 1)) (two_mul_word' k hk40) rfl
    have hT : (0 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT33 : ((2 * (k + 1) : ℕ) : ℝ) ≤ 2 ^ 33 := by
      exact_mod_cast (show 2 * (k + 1) ≤ 2 ^ 33 by omega)
    have hTw : ((2 * (k + 1) : ℕ) : ℝ) / w ≤ 2 ^ 546 := by
      rw [div_le_iff₀ hw0]
      have h2 : (2 : ℝ) ^ 546 * (1 / 2 ^ 513) ≤ 2 ^ 546 * w :=
        mul_le_mul_of_nonneg_left hw513 (by positivity)
      have h3 : (2 : ℝ) ^ 546 * (1 / 2 ^ 513) = 2 ^ 33 := by norm_num
      linarith
    have hqa := fapprox_div ht hx _ w (by rw [abs_of_nonneg hT]) (le_abs_self w) (by linarith) _
      (by rw [add_zero, sub_zero]) (by linarith [show (2 : ℝ) ^ 546 < 2 ^ 1022 by norm_num])
    have hq' : FApprox ((2 * UInt64.ofNat (k + 1)).toFloat / x) (((2 * (k + 1) : ℕ) : ℝ) / w)
        (((2 * (k + 1) : ℕ) : ℝ) / w / 2 ^ 53 + 1 / 2 ^ 1075) := fmono hqa (by simp)
    rw [hl] at hq' hTw
    refine ⟨hq'.1, hq'.2, ?_, hTw⟩
    rw [← hl, le_div_iff₀ hw0]
    have : (2 : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * (k + 1) by omega)
    linarith
  have hrec : ∀ k, (yf x (k + 2)).toBits = Wasm.IEEE64.sub (Wasm.IEEE64.mul
      ((2 * UInt64.ofNat (k + 1)).toFloat / x).toBits (yf x (k + 1)).toBits) (yf x k).toBits := by
    intro k
    show ((((2 * UInt64.ofNat (k + 1)).toFloat / x) * yf x (k + 1)) - yf x k).toBits = _
    rw [F64Bits.toBits_sub, F64Bits.toBits_mul]
  have hsfin : ∀ k, k + 2 ≤ n.toNat → Finite (yf x k).toBits → Finite (yf x (k + 1)).toBits →
      Finite (yf x (k + 2)).toBits →
      |value (yf x (k + 2)).toBits -
          (lam w (k + 1) * value (yf x (k + 1)).toBits - value (yf x k).toBits)| ≤
        𝐮 * (301 / 100 * lam w (k + 1) * |value (yf x (k + 1)).toBits| +
          |value (yf x k).toBits|) + 1 / 2 ^ 1070 := by
    intro k hk fa fb fc
    obtain ⟨hqf, hqe, hL1, -⟩ := hq k hk
    rw [hrec] at fc ⊢
    exact step_fin hqf hqe hL1 fb fa fc
  have hg : ∀ j, 1 ≤ j → 0 < -Yn w j := fun j hj => by
    have := Y_neg w hw0 hw2.le j hj; linarith
  have hcu : ∀ j : ℕ, j ≤ n.toNat → (250 + 12 * (j : ℝ)) * 𝐮 ≤ 1 / 2 ^ 18 := by
    intro j hj
    have : (j : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (hj.trans hn2)
    rw [hu]
    have : (250 + 12 * (2 : ℝ) ^ 31) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 18 := by norm_num
    nlinarith
  by_cases hex : ∃ K, 2 ≤ K ∧ K ≤ n.toNat ∧ ¬Finite (yf x K).toBits
  swap
  · -- every value is finite
    push Not at hex
    have hfin : ∀ j, j ≤ n.toNat → Finite (yf x j).toBits := by
      intro j hj
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
      · exact hf0
      · exact hf1
      · exact hex j hj2 hj
    have hall := small_error w hw0 hw2 n.toNat hn2 (fun k => value (yf x k).toBits) he0 he1
      (fun k hk => hsfin k hk (hfin k (by omega)) (hfin (k + 1) (by omega)) (hfin (k + 2) hk))
    right
    rw [yn_loop_eq x _ _ n (by omega) hn2 (fun j _ hj => hfin j hj.le)]
    exact ⟨hfin _ le_rfl, hall _ hn1 le_rfl⟩
  · -- the first value that is not finite
    left
    obtain ⟨K, ⟨hK2, hKN, hKf⟩, hmin⟩ : ∃ K, (2 ≤ K ∧ K ≤ n.toNat ∧ ¬Finite (yf x K).toBits) ∧
        ∀ j < K, ¬(2 ≤ j ∧ j ≤ n.toNat ∧ ¬Finite (yf x j).toBits) := by
      classical
      exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hfin : ∀ j, j < K → Finite (yf x j).toBits := by
      intro j hj
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
      · exact hf0
      · exact hf1
      · by_contra hc
        exact hmin j hj ⟨hj2, by omega, hc⟩
    have hacc := small_error w hw0 hw2 (K - 1) (by omega) (fun k => value (yf x k).toBits) he0 he1
      (fun k hk => hsfin k (by omega) (hfin k (by omega)) (hfin (k + 1) (by omega))
        (hfin (k + 2) (by omega)))
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
    obtain ⟨hqf, hqe, hL1, hL546⟩ := hq k hKN
    have hlamrec : lam w (k + 1) * -Yn w (k + 1) = -Yn w (k + 2) + -Yn w k := by
      have := Yn_recur w k
      unfold lam
      push_cast
      rw [this]
      ring
    have hmono := Y_mono w hw0 hw2
    have hM1b : modn w 1 ≤ 1 + -Yn w 1 := by
      obtain ⟨hJp, hJ⟩ := J1_le w hw0 hw2
      unfold modn
      have := sqrt_le_add (Jn 1 w) (Yn w 1)
      rw [abs_of_pos hJp, abs_of_neg (show Yn w 1 < 0 by linarith [hg 1 le_rfl])] at this
      linarith
    have hE1 : |value (yf x 1).toBits - Yn w 1| ≤ 12 * 𝐮 * (1 + -Yn w 1) :=
      he1.trans (mul_le_mul_of_nonneg_left hM1b (by rw [hu]; positivity))
    -- `|Y_(k+2)| > 2^1023`
    have hbig : 2 ^ 1023 < -Yn w (k + 2) := by
      by_contra hle
      push Not at hle
      apply hKf
      rw [hrec]
      have hgc0 := (hg (k + 2) (by omega)).le
      have hga : |-Yn w k| ≤ 3 * 2 ^ 1021 := by
        rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
        · rw [abs_neg]
          have := Y_le_modn w 0
          have : (2 : ℝ) ^ 10 ≤ 3 * 2 ^ 1021 := by norm_num
          linarith
        · rw [abs_of_pos (hg 1 le_rfl)]
          have := Y31 w hw0 hw2
          have : (3 : ℝ) * 2 ^ 1023 = 4 * (3 * 2 ^ 1021) := by norm_num
          linarith
        · rw [abs_of_pos (hg k (by omega))]
          have := Y_double w hw0 hw2 k hk2
          have : (2 : ℝ) ^ 1023 = 2 * 2 ^ 1022 := by norm_num
          have : (2 : ℝ) ^ 1022 ≤ 3 * 2 ^ 1021 := by norm_num
          linarith
      have hb : lam w (k + 1) * |value (yf x (k + 1)).toBits + -Yn w (k + 1)| ≤ 2 ^ 1019 := by
        rw [← sub_eq_add_neg]
        rcases (show k = 0 ∨ 1 ≤ k by omega) with rfl | hk1
        · simp only [zero_add] at hlamrec hL546 hL1 hle ⊢
          have hY0 := Y_le_modn w 0
          have hY0' := neg_abs_le (Yn w 0)
          have hL0 : 0 ≤ lam w 1 := by linarith
          calc lam w 1 * |value (yf x 1).toBits - Yn w 1| ≤ lam w 1 * (12 * 𝐮 * (1 + -Yn w 1)) :=
                mul_le_mul_of_nonneg_left hE1 hL0
            _ = 12 * 𝐮 * (lam w 1 + lam w 1 * -Yn w 1) := by ring
            _ ≤ 12 * 𝐮 * (2 ^ 546 + (2 ^ 1023 + 2 ^ 10)) := by
                apply mul_le_mul_of_nonneg_left _ (by rw [hu]; positivity)
                rw [hlamrec]
                linarith
            _ ≤ 2 ^ 1019 := by rw [hu]; norm_num
        · have h1 := hacc (k + 1) (by omega) (by omega)
          have hLg : lam w (k + 1) * -Yn w (k + 1) ≤ 2 ^ 1024 := by
            rw [hlamrec]
            have := le_abs_self (-Yn w k)
            have : (2 : ℝ) ^ 1023 + 3 * 2 ^ 1021 ≤ 2 ^ 1024 := by norm_num
            linarith
          have hc1 := hcu (k + 1) (by omega)
          push_cast at hc1
          have hL0 : 0 ≤ lam w (k + 1) := by linarith
          calc lam w (k + 1) * |value (yf x (k + 1)).toBits - Yn w (k + 1)|
              ≤ lam w (k + 1) * ((250 + 12 * ((k : ℝ) + 1)) * 𝐮 * -Yn w (k + 1)) :=
                mul_le_mul_of_nonneg_left (by push_cast at h1; exact h1) hL0
            _ = (250 + 12 * ((k : ℝ) + 1)) * 𝐮 * (lam w (k + 1) * -Yn w (k + 1)) := by ring
            _ ≤ 1 / 2 ^ 18 * 2 ^ 1024 :=
                mul_le_mul hc1 hLg (mul_nonneg hL0 (hg (k + 1) (by omega)).le) (by positivity)
            _ ≤ 2 ^ 1019 := by norm_num
      have ha : |value (yf x k).toBits + -Yn w k| ≤ 2 ^ 1019 := by
        rw [← sub_eq_add_neg]
        rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
        · have : 11 * 𝐮 * modn w 0 ≤ 2 ^ 1019 := by
            rw [hu]
            have : (11 : ℝ) * (1 / 2 ^ 53) * 2 ^ 10 ≤ 2 ^ 1019 := by norm_num
            linarith
          exact he0.trans this
        · have : 12 * 𝐮 * modn w 1 ≤ 2 ^ 1019 := by
            rw [hu]
            have : (12 : ℝ) * (1 / 2 ^ 53) * 2 ^ 516 ≤ 2 ^ 1019 := by norm_num
            linarith
          exact he1.trans this
        · have h1 := hacc k hk2 (by omega)
          have hc1 := hcu k (by omega)
          have hgk := hmono k (by omega) (k + 2) (by omega)
          calc |value (yf x k).toBits - Yn w k| ≤ (250 + 12 * (k : ℝ)) * 𝐮 * -Yn w k := h1
            _ ≤ 1 / 2 ^ 18 * 2 ^ 1023 :=
                mul_le_mul hc1 (by linarith) (hg k (by omega)).le (by positivity)
            _ ≤ 2 ^ 1019 := by norm_num
      obtain ⟨m1, m2⟩ := step_bounds (by linarith) (hg (k + 1) (by omega)).le hgc0 hle hga
        hlamrec hb ha
      exact step_mag hqf hqe hL1 (hfin (k + 1) (by omega)) (hfin k (by omega)) m1 m2
    -- the value at `k + 1` is negative
    have hneg : value (yf x (k + 1)).toBits < 0 := by
      rcases (show k = 0 ∨ 1 ≤ k by omega) with rfl | hk1
      · -- `λ₁ |Y₁| = |Y₂| - Y₀ ≥ 2^1023 - 2^10`, so `|Y₁| ≥ 2^476`
        simp only [zero_add] at hlamrec hL546 hbig ⊢
        have hY0 := Y_le_modn w 0
        have hg1 : 2 ^ 476 ≤ -Yn w 1 := by
          by_contra h
          push Not at h
          have := mul_le_mul hL546 h.le (hg 1 le_rfl).le (by positivity)
          have e : (2 : ℝ) ^ 546 * 2 ^ 476 = 2 ^ 1022 := by norm_num
          have := le_abs_self (Yn w 0)
          have : (2 : ℝ) ^ 1022 + 2 ^ 10 < 2 ^ 1023 := by norm_num
          linarith
        have h1 := (abs_le.mp hE1).2
        rw [hu] at h1
        have : (12 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 := by norm_num
        have : (12 : ℝ) * (1 / 2 ^ 53) * (1 + -Yn w 1) ≤ 1 / 2 * (1 + -Yn w 1) :=
          mul_le_mul_of_nonneg_right this (by linarith)
        have : (1 : ℝ) < 2 ^ 476 := by norm_num
        linarith
      · have h1 := hacc (k + 1) (by omega) (by omega)
        have hc1 := hcu (k + 1) (by omega)
        have hgk := hg (k + 1) (by omega)
        have h2 : (250 + 12 * ((k + 1 : ℕ) : ℝ)) * 𝐮 * -Yn w (k + 1) ≤ 1 / 2 ^ 18 * -Yn w (k + 1) :=
          mul_le_mul_of_nonneg_right hc1 hgk.le
        have := (abs_le.mp h1).2
        linarith
    have hq0 : 0 < value ((2 * UInt64.ofNat (k + 1)).toFloat / x).toBits := by
      have := (abs_le.mp hqe).1
      have : lam w (k + 1) / 2 ^ 53 + 1 / 2 ^ 1075 < lam w (k + 1) := by
        have : (1 : ℝ) / 2 ^ 1075 < 1 / 2 := by norm_num
        linarith
      linarith
    have hinf : (yf x (k + 2)).toBits = 0xFFF0000000000000 := by
      rw [hrec, step_inf hqf hq0 (hfin (k + 1) (by omega)) hneg (hfin k (by omega))
        (by rw [← hrec]; exact hKf)]
      exact neg_inf_bits
    refine ⟨?_, lt_of_lt_of_le hbig (hmono (k + 2) (by omega) n.toNat hKN)⟩
    rw [loop_stop x _ _ n (k + 2) (by omega) hKN hn2 (fun j _ hj => hfin j hj) hinf]
    exact hinf

/-- **`yn`'s loop below 2**: for `0 < x < 2` and `2 ≤ n ≤ 2^31`, the result is negative infinity
and `|Y_n(x)| > 2^1023`, or it is finite and within `(250 + 12 n) u |Y_n(x)|` of `Y_n(x)`. -/
theorem yn_small (x : Float) (n : UInt64) (hxf : Finite x.toBits)
    (hpos : x.toBits.toNat < 2 ^ 63) (hnz : x.toBits.toNat ≠ 0) (hw2 : value x.toBits < 2)
    (hn1 : 2 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31) :
    ((LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
        (ystep x)).2.2.toBits = 0xFFF0000000000000 ∧ 2 ^ 1023 < -Yn (value x.toBits) n.toNat) ∨
      (Finite (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
          (ystep x)).2.2.toBits ∧
        |value (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
          (ystep x)).2.2.toBits - Yn (value x.toBits) n.toNat| ≤
          (250 + 12 * (n.toNat : ℝ)) * 𝐮 * -Yn (value x.toBits) n.toNat) := by
  by_cases ht : x.toBits.toNat < 0x1FE0000000000000
  · exact Or.inl (yn_tiny x n hxf hpos hnz ht hn1 hn2)
  · push Not at ht
    exact yn_mid x n hxf hpos ht hw2 hn1 hn2

/-- From `|Y_n(x)| ≥ 2^1025` on, the result of `yn`'s loop below 2 is negative infinity. -/
theorem yn_small_inf (x : Float) (n : UInt64) (hxf : Finite x.toBits)
    (hpos : x.toBits.toNat < 2 ^ 63) (hnz : x.toBits.toNat ≠ 0) (hw2 : value x.toBits < 2)
    (hn1 : 2 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31)
    (hbig : 2 ^ 1025 ≤ -Yn (value x.toBits) n.toNat) :
    (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
        (ystep x)).2.2.toBits = 0xFFF0000000000000 := by
  have h := yn_small x n hxf hpos hnz hw2 hn1 hn2
  generalize (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 x, Bessel.y1 x) (ycond n)
    (ystep x)).2.2 = r at h ⊢
  rcases h with ⟨h, -⟩ | ⟨hf, he⟩
  · exact h
  · exfalso
    have hmax := abs_value_max _ hf
    have hc : (250 + 12 * (n.toNat : ℝ)) * 𝐮 ≤ 1 / 2 := by
      have : (n.toNat : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hn2
      rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
      have : (250 + 12 * (2 : ℝ) ^ 31) * (1 / 2 ^ 53) ≤ 1 / 2 := by norm_num
      nlinarith
    have hg : 0 ≤ -Yn (value x.toBits) n.toNat := le_trans (by positivity) hbig
    have h1 := mul_le_mul_of_nonneg_right hc hg
    have h2 := (abs_le.mp he).2
    have h3 := neg_abs_le (value r.toBits)
    have : (2 : ℝ) ^ 1024 - 2 ^ 971 < 2 ^ 1024 := by norm_num
    have : (2 : ℝ) ^ 1025 = 2 * 2 ^ 1024 := by norm_num
    linarith

#print axioms yn_tiny
#print axioms yn_mid
#print axioms yn_small
#print axioms yn_small_inf

end Verified.Examples.BesselYnSmall
