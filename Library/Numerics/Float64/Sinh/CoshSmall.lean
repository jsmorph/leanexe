import Library.Numerics.Float64.Sinh.SinhWords
import Library.Numerics.Float64.Tanh.Expm1Near
import Library.Numerics.Float64.Tanh.TanhTheorem
import LeanExe.ProofKit.F64NearestHalve
import LeanExe.ProofKit.F64DivBounds
import LeanExe.ProofKit.F64RoundedStep

/-!
`Sinh.cosh` within one step of `cosh x` for `abs(x) < 0.34657359`, where the code computes
`t = expm1 abs(x)` and `w = 1 + t`, and returns `w` below `2 ^ -55` and `1 + t t / (w + w)`
above.  `expm1_small` bounds `t` within `2 u (exp a - 1)` of `exp a - 1` for `0 ≤ a < 0.3466`, on
the tiny path and the path without reduction.  With `τ = exp a - 1`, `cosh a = 1 + Q` for
`Q = τ² / (2 (1 + τ))`, and the quotient `r = p / (2 w)` of the rounded product `p` lies within
`(2 u T² + η) / (2 w)` of `R = T² / (2 (1 + T))` for the value `T` of `t`, while
`R - Q = (T - τ)(T + τ + T τ) / (2 (1 + T)(1 + τ))` (`small_core`).  The sum of the errors stays
below `0.68 u`, inside the `63/64 u` of `F64RoundedStep.within_one_add`, since `cosh a ≥ 1`.
-/

namespace Library.Numerics.Float64.Sinh.CoshSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords Library.Numerics.Float64.Tanh.Expm1Branches
  Expm1Theorem

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- `Tanh.expm1` on `0 ≤ x < θ1`: within `2 u (exp x - 1)` of `exp x - 1`. -/
theorem expm1_small (x : Float) (hxf : Finite x.toBits) (hpos : 0 ≤ value x.toBits)
    (hhi : value x.toBits < value (UInt64.ofNat (1071001155 * 2 ^ 32))) :
    Finite (Tanh.expm1 x).toBits ∧
      |value (Tanh.expm1 x).toBits - (Real.exp (value x.toBits) - 1)| ≤
        2 * u * (Real.exp (value x.toBits) - 1) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨-, hθ1, -, -, -⟩ := Library.Numerics.Float64.Tanh.Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  have habs : |value x.toBits| = value x.toBits := abs_of_nonneg hpos
  have h1 := high_finite x.toBits hxf
  have hn4 := Library.Numerics.Float64.Tanh.Expm1Near.high_of_lt x.toBits 1071001155 (by norm_num) (by rw [habs]; exact hhi)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1078159482 ≤ _ at this
    omega
  have h4 : ¬ highWord x.toBits > 1071001154 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change 1071001154 < _ at this
    omega
  have hτ := Real.add_one_le_exp (value x.toBits)
  have hq := Real.abs_exp_sub_one_sub_id_le (x := value x.toBits) (by rw [habs]; linarith)
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  by_cases hX : value x.toBits < 1 / 2 ^ 54
  · have h5 : highWord x.toBits < 1016070144 := by
      have := Library.Numerics.Float64.Tanh.Expm1Near.high_of_lt x.toBits 1016070144 (by norm_num)
        (by rw [habs, Library.Numerics.Float64.Tanh.Expm1Near.tiny_threshold]; exact hX)
      exact UInt64.lt_iff_toNat_lt.mpr this
    rw [select_tiny x h1 h2 h3 h4 h5]
    simp only [F64Bits.toBits_sub, F64Bits.toBits_add, Library.Numerics.Float64.Tanh.Expm1Words.float_ofBits, huge_bits]
    rw [tiny_zero x.toBits hxf (by rw [habs]; linarith)]
    have hz : Finite (0 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
    obtain ⟨hf, hb⟩ := F64AddBounds.sub_real_relative x.toBits 0 hxf hz
      (by rw [F64Magnitude.value_zero, sub_zero, habs]; linarith)
    rw [F64Magnitude.value_zero, sub_zero, habs] at hb
    refine ⟨hf, ?_⟩
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hsq : value x.toBits ^ 2 ≤ 1 / 2 ^ 54 * value x.toBits := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hX.le hpos
    rw [abs_le, hu]
    rw [hu] at hb1 hb2
    constructor <;> nlinarith
  · push Not at hX
    have h5 : ¬ highWord x.toBits < 1016070144 := by
      have := Library.Numerics.Float64.Tanh.Expm1Near.high_of_ge x.toBits 1016070144 (by norm_num)
        (by rw [habs, Library.Numerics.Float64.Tanh.Expm1Near.tiny_threshold]; exact hX)
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      change _ < 1016070144 at this
      omega
    rw [select_middle x h1 h2 h3 h4 h5, Library.Numerics.Float64.Tanh.Expm1Words.kernel_bits]
    have hk : Library.Numerics.Float64.Tanh.Expm1Words.kernel x.toBits (0.0 : Float).toBits false 0 = Wasm.IEEE64.sub x.toBits
        (Wasm.IEEE64.sub (Wasm.IEEE64.mul x.toBits (Library.Numerics.Float64.Tanh.Expm1Words.e0 x.toBits))
          (Library.Numerics.Float64.Tanh.Expm1Words.hxs x.toBits)) := by
      simp [Library.Numerics.Float64.Tanh.Expm1Words.kernel]
    rw [hk]
    obtain ⟨hwf, hw⟩ := Library.Numerics.Float64.Tanh.Expm1KernelOuter.m0_spec x.toBits hxf (by rw [habs]; linarith)
    set W := Wasm.IEEE64.sub (Wasm.IEEE64.mul x.toBits (Library.Numerics.Float64.Tanh.Expm1Words.e0 x.toBits))
      (Library.Numerics.Float64.Tanh.Expm1Words.hxs x.toBits)
    rw [habs] at hw
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    rw [hu, hη] at hw1 hw2
    have hXW : |value x.toBits - value W| < 2 ^ 1023 := by
      rw [abs_lt]; constructor <;> nlinarith
    obtain ⟨hf, hb⟩ := F64AddBounds.sub_real_relative x.toBits W hxf hwf hXW
    refine ⟨hf, ?_⟩
    have hXW0 : 0 ≤ value x.toBits - value W := by nlinarith
    rw [abs_of_nonneg hXW0] at hb
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    rw [abs_le, hu]
    rw [hu] at hb1 hb2
    have hsmall : (1 : ℝ) / 2 ^ 1075 * 17 ≤ 1 / 2 ^ 60 * value x.toBits := by
      have : (1 : ℝ) / 2 ^ 1075 * 17 ≤ 1 / 2 ^ 60 * (1 / 2 ^ 54) := by norm_num
      nlinarith
    constructor <;> nlinarith

/-- `exp a ≤ 1.4144` for `a ≤ 0.3466`. -/
theorem exp_upper_small (A : ℝ) (hA : A ≤ 3466 / 10000) : Real.exp A ≤ 14144 / 10000 := by
  have hl := Library.Numerics.Float64.Exp.ExpTight.log_two_bounds.1
  have h1 : Real.exp (A + A) ≤ Real.exp (Real.log 2 + 1 / 10 ^ 4) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_add, Real.exp_add, Real.exp_log two_pos] at h1
  have h2 := Real.add_one_le_exp (-(1 / 10 ^ 4 : ℝ))
  have h3 : Real.exp (1 / 10 ^ 4) * Real.exp (-(1 / 10 ^ 4)) = 1 := by
    rw [← Real.exp_add]; simp
  have he0 := Real.exp_pos (1 / 10 ^ 4 : ℝ)
  have he1 : Real.exp (1 / 10 ^ 4) ≤ 10002 / 10000 := by
    nlinarith [mul_le_mul_of_nonneg_left h2 he0.le]
  have hE0 := Real.exp_pos A
  nlinarith

/-- The error of `1 + q` for `q` the rounded `p / (2 w)`. -/
theorem small_core (A T w p q : ℝ) (hA0 : 1 / 2 ^ 55 ≤ A) (hA : A ≤ 3466 / 10000)
    (hT : |T - (Real.exp A - 1)| ≤ 2 * u * (Real.exp A - 1))
    (hw : |w - (1 + T)| ≤ u * |1 + T|)
    (hp : |p - T * T| ≤ u * |T * T| + η)
    (hq : |q - p / (2 * w)| ≤ u * |p / (2 * w)| + η) :
    |1 + q - Real.cosh A| ≤ 63 / 64 * u * |Real.cosh A| := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hE1 := exp_upper_small A hA
  have hEA := Real.add_one_le_exp A
  set τ := Real.exp A - 1 with hτdef
  have hτ0 : A ≤ τ := by linarith
  have hτ1 : τ ≤ 4144 / 10000 := by linarith
  have hcosh : Real.cosh A = 1 + (Real.cosh A - 1) := by ring
  set Q := Real.cosh A - 1 with hQdef
  have hQ : Q * (2 * (1 + τ)) = τ * τ := by
    have hE0 := Real.exp_pos A
    rw [hQdef, hτdef, cosh_exp]
    field_simp
    ring
  have hy1 : 1 ≤ Real.cosh A := by
    rw [Real.cosh_eq]
    linarith [Real.add_one_le_exp A, Real.add_one_le_exp (-A)]
  have hQ0 : 0 ≤ Q := by rw [hQdef]; linarith
  have hτp : 0 ≤ τ := le_trans (by positivity) (hA0.trans hτ0)
  rw [abs_of_pos (by linarith : 0 < Real.cosh A), hcosh,
    show 1 + q - (1 + Q) = q - Q by ring]
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  rw [hu] at hT1 hT2
  have hTlo : τ * (1 - 1 / 2 ^ 52) ≤ T := by linarith
  have hThi : T ≤ τ * (1 + 1 / 2 ^ 52) := by linarith
  have hT0 : 0 < T := by
    have : 0 < τ := lt_of_lt_of_le (by positivity) (hA0.trans hτ0)
    linarith
  have hT4 : T ≤ 41441 / 100000 := by linarith
  have hTT : T * T ≤ 1718 / 10000 := by
    have := mul_le_mul hT4 hT4 hT0.le (by norm_num)
    linarith
  have hTT0 : 1 / 2 ^ 112 ≤ T * T := by
    have h56 : 1 / 2 ^ 56 ≤ T := by
      have : (1 : ℝ) / 2 ^ 56 ≤ 1 / 2 ^ 55 * (1 - 1 / 2 ^ 52) := by norm_num
      linarith
    have := mul_le_mul h56 h56 (by positivity) hT0.le
    have h2 : (1 : ℝ) / 2 ^ 112 = 1 / 2 ^ 56 * (1 / 2 ^ 56) := by norm_num
    linarith
  rw [abs_of_pos (by linarith : 0 < 1 + T)] at hw
  rw [abs_of_pos (mul_pos hT0 hT0)] at hp
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  rw [hu] at hw1 hw2
  rw [hu, hη] at hp1 hp2
  have hw0 : 99 / 100 ≤ w := by linarith
  have hp0 : 0 < p := by linarith
  have hw2p : (0 : ℝ) < 2 * w := by linarith
  have hT2p : (0 : ℝ) < 2 * (1 + T) := by linarith
  set r := p / (2 * w) with hrdef
  have hr : r * (2 * w) = p := by rw [hrdef]; exact div_mul_cancel₀ p hw2p.ne'
  have hr0 : 0 < r := by rw [hrdef]; exact div_pos hp0 hw2p
  set R := T * T / (2 * (1 + T)) with hRdef
  have hR : R * (2 * (1 + T)) = T * T := by rw [hRdef]; exact div_mul_cancel₀ _ hT2p.ne'
  have hR0 : 0 ≤ R := by rw [hRdef]; exact div_nonneg (mul_self_nonneg T) hT2p.le
  have hR1 : R ≤ T * T / 2 := by
    rw [hRdef]
    exact div_le_div_of_nonneg_left (mul_self_nonneg T) (by norm_num) (by linarith)
  -- `r` against `R`.
  have hkey : (r - R) * (2 * w) = (p - T * T) + 2 * R * (1 + T - w) := by
    linear_combination hr - hR
  have hrR : |r - R| * (2 * w) ≤ 2 * (1 / 2 ^ 53) * (T * T) + 1 / 2 ^ 1075 := by
    have h1 : |(p - T * T) + 2 * R * (1 + T - w)| ≤
        |p - T * T| + 2 * R * |1 + T - w| := by
      calc |(p - T * T) + 2 * R * (1 + T - w)| ≤ |p - T * T| + |2 * R * (1 + T - w)| :=
            abs_add_le _ _
        _ = |p - T * T| + 2 * R * |1 + T - w| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * R)]
    have h2 : |p - T * T| ≤ 1 / 2 ^ 53 * (T * T) + 1 / 2 ^ 1075 := by
      rw [abs_le]; constructor <;> linarith
    have h3 : |1 + T - w| ≤ 1 / 2 ^ 53 * (1 + T) := by
      rw [abs_le]; constructor <;> linarith
    have h4 : 2 * R * |1 + T - w| ≤ 2 * R * (1 / 2 ^ 53 * (1 + T)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [← abs_of_pos hw2p, ← abs_mul, hkey]
    have h5 : 2 * R * (1 / 2 ^ 53 * (1 + T)) = 1 / 2 ^ 53 * (T * T) := by
      linear_combination (1 / 2 ^ 53) * hR
    linarith
  have hrR' : |r - R| ≤ (2 * (1 / 2 ^ 53) * (T * T) + 1 / 2 ^ 1075) / (198 / 100) := by
    rw [le_div_iff₀ (by norm_num)]
    calc |r - R| * (198 / 100) ≤ |r - R| * (2 * w) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ _ := hrR
  -- `R` against `Q`.
  have hkey2 : (R - Q) * (2 * (1 + T) * (1 + τ)) = (T - τ) * (T + τ + T * τ) := by
    linear_combination (1 + τ) * hR - (1 + T) * hQ
  have hTt := mul_le_mul hT4 hτ1 hτp (by norm_num)
  have hTt0 := mul_nonneg hT0.le hτp
  have hS : T + τ + T * τ ≤ 10006 / 10000 := by linarith
  have hS0 : 0 ≤ T + τ + T * τ := by linarith
  have hRQ : |R - Q| ≤ 2 * (1 / 2 ^ 53) * τ * (10006 / 10000) / 2 := by
    have hd : 2 ≤ 2 * (1 + T) * (1 + τ) := by
      have := mul_le_mul (show (1 : ℝ) ≤ 1 + T by linarith) (show (1 : ℝ) ≤ 1 + τ by linarith)
        (by norm_num) (by linarith)
      linarith
    have hdp : (0 : ℝ) < 2 * (1 + T) * (1 + τ) := by linarith
    rw [le_div_iff₀ (by norm_num)]
    have h1 : |R - Q| * (2 * (1 + T) * (1 + τ)) = |T - τ| * (T + τ + T * τ) := by
      rw [← abs_of_pos hdp, ← abs_mul, hkey2, abs_mul, abs_of_nonneg hS0]
    have h2 : |T - τ| ≤ 2 * (1 / 2 ^ 53) * τ := by
      rw [abs_le]; constructor <;> linarith
    have h3 : |T - τ| * (T + τ + T * τ) ≤ 2 * (1 / 2 ^ 53) * τ * (10006 / 10000) :=
      mul_le_mul h2 hS hS0 (by linarith)
    calc |R - Q| * 2 ≤ |R - Q| * (2 * (1 + T) * (1 + τ)) :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ ≤ _ := by rw [h1]; exact h3
  -- `q` against `r`.
  rw [abs_of_pos hr0] at hq
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  rw [hu, hη] at hq1 hq2
  obtain ⟨hrR1, hrR2⟩ := abs_le.mp hrR'
  obtain ⟨hRQ1, hRQ2⟩ := abs_le.mp hRQ
  rw [abs_le, hu]
  constructor <;> linarith

/-- Adding a word to itself doubles it exactly. -/
theorem add_double (w : UInt64) (hwf : Finite w) (hlo : 1 / 2 ^ 1022 < value w)
    (hhi : value w < 2 ^ 1022) :
    Finite (Wasm.IEEE64.add w w) ∧ value (Wasm.IEEE64.add w w) = 2 * value w := by
  have hn := F64NearestSum.add_nearest w w hwf hwf
    (by have : (0 : ℝ) < 1 / 2 ^ 1022 := by positivity
        linarith)
    (by have : (2 : ℝ) ^ 1022 * 2 = 2 ^ 1023 := by norm_num
        linarith)
  obtain ⟨hdl, hdv⟩ := F64NearestHalve.double_word w hwf hlo
    (hhi.trans (by norm_num))
  have h := hn.2 _ hdl
  rw [hdv, show 2 * value w - (value w + value w) = 0 by ring, abs_zero] at h
  refine ⟨(nearest_finite _ _ hn).1, ?_⟩
  have := abs_nonpos_iff.mp h
  linarith

theorem magnitude_ne_zero (v : UInt64) (hv : value v ≠ 0) :
    Wasm.IEEE64.scaledMagnitude v ≠ 0 := by
  intro h
  apply hv
  have hz : Wasm.IEEE64.scaledValue v = 0 := by
    have := natAbs_scaledValue v
    rw [h] at this
    exact Int.natAbs_eq_zero.mp this
  rw [value, hz]
  simp

/-- The range `abs(x) < 2 ^ -55`, where the code returns `1 + t`. -/
theorem cosh_tiny (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits))
      (1.0 + Tanh.expm1 x.abs).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨hθ1, -, -, -, -⟩ := Library.Numerics.Float64.Tanh.Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  rw [← Real.cosh_abs]
  have hA0 : 0 ≤ |value x.toBits| := abs_nonneg _
  generalize hA : |value x.toBits| = A at hx hav hA0 ⊢
  obtain ⟨htf, ht⟩ := expm1_small x.abs haf (by rw [hav]; exact hA0)
    (by rw [hav]; linarith [show (1 : ℝ) / 2 ^ 55 ≤ 34657359 / 10 ^ 8 by norm_num])
  rw [hav] at ht
  rw [F64Bits.toBits_add, Library.Numerics.Float64.Tanh.TanhTheorem.one_bits]
  generalize (Tanh.expm1 x.abs).toBits = t at htf ht ⊢
  have hone := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_values.1
  have hcf := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_finite.1
  have hq := Real.abs_exp_sub_one_sub_id_le (x := A) (by rw [abs_of_nonneg hA0]; linarith)
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  have hsq : A ^ 2 ≤ 1 / 2 ^ 55 * A := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hx.le hA0
  have hE := Real.add_one_le_exp A
  have hEn := Real.add_one_le_exp (-A)
  have hy1 : 1 ≤ Real.cosh A := by rw [Real.cosh_eq]; linarith
  have hyE : Real.cosh A ≤ Real.exp A := by
    rw [Real.cosh_eq]
    have : Real.exp (-A) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hyE' : Real.exp A - Real.cosh A ≤ Real.exp A - 1 := by linarith
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  rw [hu] at ht1 ht2
  apply F64RoundedStep.within_one_add _ _ _ hcf htf
  · rw [abs_of_pos (by linarith)]
    linarith [show (1 : ℝ) / 2 ^ 1000 ≤ 1 by norm_num]
  · rw [abs_of_pos (by linarith)]
    linarith [show (3 : ℝ) ≤ 2 ^ 1000 by norm_num]
  · rw [hone, abs_of_pos (show (0 : ℝ) < Real.cosh A by linarith), abs_le, hu]
    constructor <;> nlinarith

/-- The range `2 ^ -55 ≤ abs(x) < θ1`, where the code returns `1 + t t / (w + w)`. -/
theorem cosh_small (x : Float) (hxf : Finite x.toBits) (hlo : 1 / 2 ^ 55 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < value (UInt64.ofNat (1071001155 * 2 ^ 32))) :
    F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits))
      (1.0 + Tanh.expm1 x.abs * Tanh.expm1 x.abs /
        ((1.0 + Tanh.expm1 x.abs) + (1.0 + Tanh.expm1 x.abs))).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨-, hθ1, -, -, -⟩ := Library.Numerics.Float64.Tanh.Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  rw [← Real.cosh_abs]
  generalize hA : |value x.toBits| = A at hlo hhi hav ⊢
  have hA0 : 0 ≤ A := le_trans (by positivity) hlo
  obtain ⟨htf, ht⟩ := expm1_small x.abs haf (by rw [hav]; exact hA0) (by rw [hav]; exact hhi)
  rw [hav] at ht
  simp only [F64Bits.toBits_add, F64Bits.toBits_div, F64Bits.toBits_mul, Library.Numerics.Float64.Tanh.TanhTheorem.one_bits]
  generalize (Tanh.expm1 x.abs).toBits = t at htf ht ⊢
  have hone := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_values.1
  have hcf := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_finite.1
  have hE1 := exp_upper_small A (by linarith)
  have hE := Real.add_one_le_exp A
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  rw [hu] at ht1 ht2
  have hT0 : 0 ≤ value t := by linarith
  have hT1 : value t ≤ 1 / 2 := by linarith
  -- `w = 1 + t`.
  obtain ⟨hwf, hw⟩ := F64AddBounds.add_real_relative _ t hcf htf (by
    rw [hone, abs_of_pos (by linarith)]
    linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  rw [hone] at hw
  set w := Wasm.IEEE64.add Library.Numerics.Float64.Tanh.Expm1Words.one t
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + value t), hu] at hw1 hw2
  have hw0 : 99 / 100 ≤ value w := by linarith
  have hw3 : value w ≤ 2 := by linarith
  -- `w + w`.
  obtain ⟨hdf, hdv⟩ := add_double w hwf
    (by linarith [show (1 : ℝ) / 2 ^ 1022 ≤ 99 / 100 by norm_num])
    (by linarith [show (2 : ℝ) ≤ 2 ^ 1022 by norm_num])
  -- `t t`.
  have hTT : value t * value t ≤ 1 := by nlinarith
  obtain ⟨hpf, hp⟩ := F64MulBounds.mul_real_mixed t t htf htf (by
    rw [abs_of_nonneg (mul_nonneg hT0 hT0)]
    linarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  set p := Wasm.IEEE64.mul t t
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  rw [abs_of_nonneg (mul_nonneg hT0 hT0), hu, hη] at hp1 hp2
  -- `p / (w + w)`.
  have hd0 : value (Wasm.IEEE64.add w w) ≠ 0 := by rw [hdv]; linarith
  obtain ⟨hqf, hq⟩ := F64DivBounds.div_real_mixed p _ hpf hdf (magnitude_ne_zero _ hd0) (by
    rw [hdv, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * value w), div_lt_iff₀ (by linarith)]
    have : |value p| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [show (2 : ℝ) ≤ 2 ^ 1022 by norm_num])
  rw [hdv] at hq
  apply F64RoundedStep.within_one_add _ _ _ hcf hqf
  · have : 1 ≤ Real.cosh A := by
      rw [Real.cosh_eq]; linarith [Real.add_one_le_exp A, Real.add_one_le_exp (-A)]
    rw [abs_of_pos (by linarith)]
    linarith [show (1 : ℝ) / 2 ^ 1000 ≤ 1 by norm_num]
  · have : Real.cosh A ≤ Real.exp A := by
      rw [Real.cosh_eq]
      have : Real.exp (-A) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [abs_of_pos (Real.cosh_pos A)]
    linarith [show (2 : ℝ) ≤ 2 ^ 1000 by norm_num]
  · rw [hone]
    refine small_core A (value t) (value w) (value p) _ hlo (by linarith) ht ?_ hp hq
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + value t)]
    exact (abs_le.mpr ⟨by rw [hu]; linarith, by rw [hu]; linarith⟩)

#print axioms add_double
#print axioms cosh_tiny
#print axioms cosh_small

#print axioms expm1_small
#print axioms exp_upper_small
#print axioms small_core

end Library.Numerics.Float64.Sinh.CoshSmall
