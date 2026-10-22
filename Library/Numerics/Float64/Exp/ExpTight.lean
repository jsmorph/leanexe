import Library.Numerics.Float64.Exp.ExpTightPoly
import Library.Numerics.Float64.Exp.ExpSpecialReconstruction
import LeanExe.ProofKit.F64ApproxStages
import LeanExe.ProofKit.F64NearestSum

/-!
A tight bound for the reconstruction of Arm's `exp`.  The final operation `s + s w` of the code
rounds once, so its result is `F64NearestNonnegative.Nearest` to the exact sum, and the sum lies
within `u/32` of `2 ^ d exp x`, relative to `2 ^ d exp x`.  The bound composes four facts with
tighter constants than `ExpTableReconstruction`: the residual lies in `abs(r) ≤ 0.002708`
(`residual_tight`), where the polynomial is within `2 ^ -64` of `exp r - 1`
(`ExpTightPoly.polynomial_tight`); the rounded evaluation is within `u/100` of the polynomial
(`evaluation_tight`), counting each rounding against the magnitude of its own result; and the
product `s w` and the residual add `u/60` and `u/127` relative to `s`.
-/

namespace Library.Numerics.Float64.Exp.ExpTight
open CodeLib.IEEE64 LeanExe.ProofKit F64ApproxStages

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem log_two_bounds : (6931471805 / 10 ^ 10 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ 6931471806 / 10 ^ 10 := by
  obtain ⟨hl, hu⟩ := ExpReductionBounds.log_two_enclosure
  have h1 : (6931471805 / 10 ^ 10 : ℚ) ≤ ExpReductionBounds.lowerLogTwo := by decide +kernel
  have h2 : ExpReductionBounds.upperLogTwo ≤ (6931471806 / 10 ^ 10 : ℚ) := by decide +kernel
  have h1' : ((6931471805 / 10 ^ 10 : ℚ) : ℝ) ≤ (ExpReductionBounds.lowerLogTwo : ℝ) :=
    Rat.cast_le.mpr h1
  have h2' : (ExpReductionBounds.upperLogTwo : ℝ) ≤ ((6931471806 / 10 ^ 10 : ℚ) : ℝ) :=
    Rat.cast_le.mpr h2
  push_cast at h1' h2'
  exact ⟨h1'.trans hl, hu.trans h2'⟩

/-- The ideal residual `x - k log 2 / 128` lies within `0.0027077`. -/
theorem ideal_tight (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    |ExpResidualBounds.ideal x| ≤ 27077 / 10 ^ 7 := by
  obtain ⟨k, -, hks, -, hke⟩ := ExpReductionSelection.integer_selection x hxf hx
  have hkv : value (ExpReductionSelection.integer x) = k := by
    rw [value, hks, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
      div_self (by positivity), mul_one]
  obtain ⟨-, -, hIL⟩ := ExpReductionBounds.inverse_bounds
  obtain ⟨hL1, hL2⟩ := log_two_bounds
  have hLpos : 0 < Real.log 2 := by linarith
  unfold ExpResidualBounds.ideal
  rw [hkv]
  set L := Real.log 2
  set I := value 0x40671547652B82FE
  set X := value x
  have h1 : X - k * (L / 128) = (L / 128) * (X * (128 / L - I) + (I * X - k)) := by
    field_simp
    ring
  rw [h1, abs_mul, abs_of_pos (by positivity)]
  have h2 : |X * (128 / L - I)| ≤ 768 * (128 / L / 2 ^ 53) := by
    rw [abs_mul]
    apply mul_le_mul hx _ (abs_nonneg _) (by norm_num)
    rw [show 128 / L - I = (128 / L) * (1 - I * L / 128) by field_simp, abs_mul,
      abs_of_pos (by positivity), abs_sub_comm]
    calc 128 / L * |I * L / 128 - 1| ≤ 128 / L * (1 / 2 ^ 53) :=
          mul_le_mul_of_nonneg_left hIL (by positivity)
      _ = 128 / L / 2 ^ 53 := by ring
  have h3 : |I * X - k| ≤ 1 / 2 + 1 / 2 ^ 35 := by rw [abs_sub_comm]; exact hke
  calc L / 128 * |X * (128 / L - I) + (I * X - k)| ≤
      L / 128 * (768 * (128 / L / 2 ^ 53) + (1 / 2 + 1 / 2 ^ 35)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h2 h3)) (by positivity)
    _ = 768 / 2 ^ 53 + L / 128 * (1 / 2 + 1 / 2 ^ 35) := by field_simp
    _ ≤ 27077 / 10 ^ 7 := by nlinarith

theorem residual_tight (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (ExpResidualBounds.residual x) ∧
      |value (ExpResidualBounds.residual x)| ≤ 2708 / 10 ^ 6 ∧
      |value (ExpResidualBounds.residual x) - ExpResidualBounds.ideal x| ≤ 1 / 2 ^ 60 := by
  obtain ⟨hf, -, he⟩ := ExpResidualBounds.residual_bounds x hxf hx
  have hi := ideal_tight x hxf hx
  refine ⟨hf, ?_, he⟩
  have := abs_sub_abs_le_abs_sub (value (ExpResidualBounds.residual x))
    (ExpResidualBounds.ideal x)
  have h60 : (1 : ℝ) / 2 ^ 60 ≤ 1 / 10 ^ 12 := by norm_num
  linarith

/-- The rounded evaluation within `u/100` of `t + polynomial r`. -/
theorem evaluation_tight (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 2708 / 10 ^ 6) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (ExpEvaluationBounds.evaluation r t) ∧
      |value (ExpEvaluationBounds.evaluation r t) -
        (value t + ExpApproximation.polynomial (value r))| ≤ u / 100 := by
  obtain ⟨h2f, h3f, h4f, h5f⟩ := ExpEvaluationBounds.coefficient_finite
  obtain ⟨h2, h3, h4, h5⟩ := ExpEvaluationBounds.coefficient_bounds
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  set R := value r
  set T := value t
  set c2 := value 0x3FDFFFFFFFFFFDBD
  set c3 := value 0x3FC555555555543C
  set c4 := value 0x3FA55555CF172B91
  set c5 := value 0x3F81111167A4D017
  set ρ : ℝ := 2708 / 10 ^ 6 with hρ
  have hRR : |R * R| ≤ ρ * ρ := by rw [abs_mul]; exact mul_le_mul hr hr (abs_nonneg _) (by norm_num)
  have hz : ∀ a : ℝ, |a - a| ≤ 0 := fun a => by simp
  -- r2 = r r
  obtain ⟨f1, e1⟩ := mul_approx r r hrf hrf R R 0 0 ρ ρ (hz _) (hz _) hr hr (by norm_num)
  have e1' : |value (Wasm.IEEE64.mul r r) - R * R| ≤ 1 / 2 ^ 69 :=
    e1.trans (by rw [hu, hη, hρ]; norm_num)
  -- a3 = r c3
  obtain ⟨f2, e2⟩ := mul_approx r _ hrf h3f R c3 0 0 ρ (1 / 6) (hz _) (hz _) hr h3 (by norm_num)
  have e2' : |value (Wasm.IEEE64.mul r 0x3FC555555555543C) - R * c3| ≤ 1 / 2 ^ 63 :=
    e2.trans (by rw [hu, hη, hρ]; norm_num)
  -- p23 = c2 + a3
  have m3 : |c2 + R * c3| ≤ 501 / 1000 := by
    have : |R * c3| ≤ ρ * (1 / 6) := by
      rw [abs_mul]; exact mul_le_mul hr h3 (abs_nonneg _) (by norm_num)
    calc |c2 + R * c3| ≤ |c2| + |R * c3| := abs_add_le _ _
      _ ≤ 1 / 2 + ρ * (1 / 6) := add_le_add h2 this
      _ ≤ 501 / 1000 := by rw [hρ]; norm_num
  obtain ⟨f3, e3⟩ := add_approx _ _ h2f f2 c2 (R * c3) 0 (1 / 2 ^ 63) (501 / 1000) (hz _) e2' m3
    (by norm_num)
  have e3' : |value (Wasm.IEEE64.add 0x3FDFFFFFFFFFFDBD (Wasm.IEEE64.mul r 0x3FC555555555543C)) -
      (c2 + R * c3)| ≤ 1 / 2 ^ 53 := e3.trans (by rw [hu]; norm_num)
  -- q23 = r2 p23
  obtain ⟨f4, e4⟩ := mul_approx _ _ f1 f3 (R * R) (c2 + R * c3) (1 / 2 ^ 69) (1 / 2 ^ 53)
    (ρ * ρ) (501 / 1000) e1' e3' hRR m3 (by rw [hρ]; norm_num)
  have e4' : |value (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r)
      (Wasm.IEEE64.add 0x3FDFFFFFFFFFFDBD (Wasm.IEEE64.mul r 0x3FC555555555543C))) -
      R * R * (c2 + R * c3)| ≤ 1 / 2 ^ 68 := e4.trans (by rw [hu, hη, hρ]; norm_num)
  -- a5 = r c5
  obtain ⟨f5, e5⟩ := mul_approx r _ hrf h5f R c5 0 0 ρ (1 / 64) (hz _) (hz _) hr h5 (by norm_num)
  have e5' : |value (Wasm.IEEE64.mul r 0x3F81111167A4D017) - R * c5| ≤ 1 / 2 ^ 66 :=
    e5.trans (by rw [hu, hη, hρ]; norm_num)
  -- p45 = c4 + a5
  have m6 : |c4 + R * c5| ≤ 63 / 1000 := by
    have : |R * c5| ≤ ρ * (1 / 64) := by
      rw [abs_mul]; exact mul_le_mul hr h5 (abs_nonneg _) (by norm_num)
    calc |c4 + R * c5| ≤ |c4| + |R * c5| := abs_add_le _ _
      _ ≤ 1 / 16 + ρ * (1 / 64) := add_le_add h4 this
      _ ≤ 63 / 1000 := by rw [hρ]; norm_num
  obtain ⟨f6, e6⟩ := add_approx _ _ h4f f5 c4 (R * c5) 0 (1 / 2 ^ 66) (63 / 1000) (hz _) e5' m6
    (by norm_num)
  have e6' : |value (Wasm.IEEE64.add 0x3FA55555CF172B91 (Wasm.IEEE64.mul r 0x3F81111167A4D017)) -
      (c4 + R * c5)| ≤ 1 / 2 ^ 56 := e6.trans (by rw [hu]; norm_num)
  -- r4 = r2 r2
  obtain ⟨f7, e7⟩ := mul_approx _ _ f1 f1 (R * R) (R * R) (1 / 2 ^ 69) (1 / 2 ^ 69) (ρ * ρ)
    (ρ * ρ) e1' e1' hRR hRR (by rw [hρ]; norm_num)
  have e7' : |value (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r) (Wasm.IEEE64.mul r r)) -
      R * R * (R * R)| ≤ 1 / 2 ^ 84 := e7.trans (by rw [hu, hη, hρ]; norm_num)
  have hR4 : |R * R * (R * R)| ≤ ρ * ρ * (ρ * ρ) := by
    rw [abs_mul]; exact mul_le_mul hRR hRR (abs_nonneg _) (by positivity)
  -- q45 = r4 p45
  obtain ⟨f8, e8⟩ := mul_approx _ _ f7 f6 (R * R * (R * R)) (c4 + R * c5) (1 / 2 ^ 84)
    (1 / 2 ^ 56) (ρ * ρ * (ρ * ρ)) (63 / 1000) e7' e6' hR4 m6 (by rw [hρ]; norm_num)
  have e8' : |value (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul r r)
      (Wasm.IEEE64.mul r r))
      (Wasm.IEEE64.add 0x3FA55555CF172B91 (Wasm.IEEE64.mul r 0x3F81111167A4D017))) -
      R * R * (R * R) * (c4 + R * c5)| ≤ 1 / 2 ^ 86 := e8.trans (by rw [hu, hη, hρ]; norm_num)
  -- a01 = t + r
  have m9 : |T + R| ≤ 1 / 2 ^ 53 + ρ := (abs_add_le _ _).trans (add_le_add ht hr)
  obtain ⟨f9, e9⟩ := add_approx t r htf hrf T R 0 0 (1 / 2 ^ 53 + ρ) (hz _) (hz _) m9
    (by rw [hρ]; norm_num)
  have e9' : |value (Wasm.IEEE64.add t r) - (T + R)| ≤ u * (27081 / 10 ^ 7) :=
    e9.trans (by rw [hu, hρ]; norm_num)
  -- a0123 = a01 + q23
  have m10 : |(T + R) + R * R * (c2 + R * c3)| ≤ 27117 / 10 ^ 7 := by
    have : |R * R * (c2 + R * c3)| ≤ ρ * ρ * (501 / 1000) := by
      rw [abs_mul]; exact mul_le_mul hRR m3 (abs_nonneg _) (by positivity)
    calc _ ≤ |T + R| + |R * R * (c2 + R * c3)| := abs_add_le _ _
      _ ≤ (1 / 2 ^ 53 + ρ) + ρ * ρ * (501 / 1000) := add_le_add m9 this
      _ ≤ 27117 / 10 ^ 7 := by rw [hρ]; norm_num
  obtain ⟨f10, e10⟩ := add_approx _ _ f9 f4 (T + R) (R * R * (c2 + R * c3)) (u * (27081 / 10 ^ 7))
    (1 / 2 ^ 68) (27117 / 10 ^ 7) e9' e4' m10 (by rw [hu]; norm_num)
  -- y = a0123 + q45
  have m11 : |(T + R) + R * R * (c2 + R * c3) + R * R * (R * R) * (c4 + R * c5)| ≤
      2712 / 10 ^ 6 := by
    have : |R * R * (R * R) * (c4 + R * c5)| ≤ ρ * ρ * (ρ * ρ) * (63 / 1000) := by
      rw [abs_mul]; exact mul_le_mul hR4 m6 (abs_nonneg _) (by positivity)
    calc _ ≤ |(T + R) + R * R * (c2 + R * c3)| + |R * R * (R * R) * (c4 + R * c5)| :=
          abs_add_le _ _
      _ ≤ 27117 / 10 ^ 7 + ρ * ρ * (ρ * ρ) * (63 / 1000) := add_le_add m10 this
      _ ≤ 2712 / 10 ^ 6 := by rw [hρ]; norm_num
  obtain ⟨f11, e11⟩ := add_approx _ _ f10 f8 ((T + R) + R * R * (c2 + R * c3))
    (R * R * (R * R) * (c4 + R * c5))
    (u * (27117 / 10 ^ 7 + u * (27081 / 10 ^ 7) + 1 / 2 ^ 68) + (u * (27081 / 10 ^ 7) +
      1 / 2 ^ 68)) (1 / 2 ^ 86) (2712 / 10 ^ 6) e10 e8' m11 (by rw [hu]; norm_num)
  refine ⟨f11, ?_⟩
  have hid : (T + R) + R * R * (c2 + R * c3) + R * R * (R * R) * (c4 + R * c5) =
      T + ExpApproximation.polynomial R := by
    simp only [ExpApproximation.polynomial, c2, c3, c4, c5]
    ring
  rw [← hid]
  exact e11.trans (by rw [hu]; norm_num)

/-- The sum before the final rounding, `s + s w`, within `u/60` of `s (1 + t) exp r`, relative to
`s`. -/
theorem presum_tight (s r t : UInt64) (hsf : Finite s) (hrf : Finite r) (htf : Finite t)
    (hslo : 1 / 2 ^ 1000 ≤ value s) (hshi : value s ≤ 2 ^ 1000)
    (hr : |value r| ≤ 2708 / 10 ^ 6) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)) ∧
      |value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t))| ≤ value s / 300 ∧
      |value s + value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)) -
        value s * (1 + value t) * Real.exp (value r)| ≤ u / 60 * value s := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨hwf, hw⟩ := evaluation_tight r t hrf htf hr ht
  have hp := ExpTightPoly.polynomial_tight (value r) hr
  set S := value s
  set W := value (ExpEvaluationBounds.evaluation r t)
  set R := value r
  set T := value t
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  -- `abs(exp r - 1) ≤ 0.00272`.
  have he := TaylorRemainder.exp_remainder R (hr.trans (by norm_num)) 2 (by norm_num)
  have hc2 : TaylorRemainder.expCoeffs 2 = [1, 1] := by decide +kernel
  rw [hc2] at he
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at he
  norm_num [Nat.factorial] at he
  have hR2 : R ^ 2 ≤ (2708 / 10 ^ 6) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hRb := abs_le.mp hr
  have hE1 : |Real.exp R - 1| ≤ 27136 / 10 ^ 7 := by
    have heb := abs_le.mp he
    rw [abs_le]; constructor <;> nlinarith
  have hpoly : |ExpApproximation.polynomial R| ≤ 27137 / 10 ^ 7 := by
    have hpb := abs_le.mp hp
    have heb := abs_le.mp hE1
    rw [abs_le]; constructor <;> nlinarith
  have hW : |W| ≤ 2714 / 10 ^ 6 := by
    have hwb := abs_le.mp hw
    have htb := abs_le.mp ht
    have hpb := abs_le.mp hpoly
    rw [abs_le]; constructor <;> (rw [hu] at hwb; nlinarith)
  have hSW : |S * W| ≤ S * (2714 / 10 ^ 6) := by
    rw [abs_mul, abs_of_pos hS]; exact mul_le_mul_of_nonneg_left hW hS.le
  have hm := F64MulBounds.mul_real_mixed s _ hsf hwf (hSW.trans_lt (by
    calc S * (2714 / 10 ^ 6) ≤ 2 ^ 1000 * (2714 / 10 ^ 6) := by nlinarith
      _ < 2 ^ 1022 := by norm_num))
  refine ⟨hm.1, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)))
      (S * W)
    have h1 : u * |S * W| ≤ u * (S * (2714 / 10 ^ 6)) :=
      mul_le_mul_of_nonneg_left hSW (by rw [hu]; positivity)
    have h2 : η ≤ S / 10 ^ 6 := by
      rw [hη]
      calc (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 / 10 ^ 6 := by norm_num
        _ ≤ S / 10 ^ 6 := by gcongr
    rw [hu] at h1
    nlinarith
  · set P := value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t))
    have hsplit : S + P - S * (1 + T) * Real.exp R =
        (P - S * W) + S * (W - (T + ExpApproximation.polynomial R)) +
          S * ((1 + ExpApproximation.polynomial R) - Real.exp R) - S * T * (Real.exp R - 1) := by
      ring
    rw [hsplit]
    have h1 : |P - S * W| ≤ u * (S * (2714 / 10 ^ 6)) + η :=
      hm.2.trans (add_le_add (mul_le_mul_of_nonneg_left hSW (by rw [hu]; positivity)) le_rfl)
    have h2 : |S * (W - (T + ExpApproximation.polynomial R))| ≤ S * (u / 100) := by
      rw [abs_mul, abs_of_pos hS]; exact mul_le_mul_of_nonneg_left hw hS.le
    have h3 : |S * ((1 + ExpApproximation.polynomial R) - Real.exp R)| ≤ S * (1 / 2 ^ 64) := by
      rw [abs_mul, abs_of_pos hS, abs_sub_comm]; exact mul_le_mul_of_nonneg_left hp hS.le
    have h4 : |S * T * (Real.exp R - 1)| ≤ S * (1 / 2 ^ 53 * (27136 / 10 ^ 7)) := by
      rw [abs_mul, abs_mul, abs_of_pos hS, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul ht hE1 (abs_nonneg _) (by positivity)) hS.le
    have h5 : η ≤ S * (u / 10 ^ 6) := by
      rw [hη, hu]
      calc (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 53 / 10 ^ 6) := by norm_num
        _ ≤ S * (1 / 2 ^ 53 / 10 ^ 6) := by gcongr
    calc _ ≤ |P - S * W| + |S * (W - (T + ExpApproximation.polynomial R))| +
          |S * ((1 + ExpApproximation.polynomial R) - Real.exp R)| +
          |S * T * (Real.exp R - 1)| :=
          (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (u * (S * (2714 / 10 ^ 6)) + η) + S * (u / 100) + S * (1 / 2 ^ 64) +
          S * (1 / 2 ^ 53 * (27136 / 10 ^ 7)) := by gcongr
      _ ≤ u / 60 * S := by
          rw [hu] at h5 ⊢
          have : S * (1 / 2 ^ 64) ≤ S * (1 / 2 ^ 53 / 2048) := by
            apply mul_le_mul_of_nonneg_left _ hS.le; norm_num
          nlinarith

/-- The residual's change of the exponential, `abs(r - ideal) ≤ 2 ^ -60`, relative to `s`. -/
theorem residual_change_tight (x s t : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768)
    (hS : 0 < value s) (ht : |value t| ≤ 1 / 2 ^ 53) :
    |value s * (1 + value t) * Real.exp (value (ExpResidualBounds.residual x)) -
      value s * (1 + value t) * Real.exp (ExpResidualBounds.ideal x)| ≤ u / 127 * value s := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨-, -, hre⟩ := residual_tight x hxf hx
  have hi := ideal_tight x hxf hx
  set a := ExpResidualBounds.ideal x
  set R := value (ExpResidualBounds.residual x)
  have hz : |R - a| ≤ 1 / 2 ^ 60 := hre
  have he := TaylorRemainder.exp_remainder (R - a) (hz.trans (by norm_num)) 2 (by norm_num)
  have hc2 : TaylorRemainder.expCoeffs 2 = [1, 1] := by decide +kernel
  rw [hc2] at he
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at he
  norm_num [Nat.factorial] at he
  have hz2 : (R - a) ^ 2 ≤ (1 / 2 ^ 60) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hd : |Real.exp (R - a) - 1| ≤ 1 / 2 ^ 60 + 1 / 2 ^ 119 := by
    have heb := abs_le.mp he
    have hzb := abs_le.mp hz
    rw [abs_le]; constructor <;> nlinarith
  have ha := TaylorRemainder.exp_remainder a (hi.trans (by norm_num)) 2 (by norm_num)
  rw [hc2] at ha
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at ha
  norm_num [Nat.factorial] at ha
  have ha2 : a ^ 2 ≤ (27077 / 10 ^ 7) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hea : Real.exp a ≤ 10028 / 10000 := by
    have hab := abs_le.mp ha
    have hib := abs_le.mp hi
    nlinarith
  have h1t : |1 + value t| ≤ 1 + 1 / 2 ^ 53 :=
    (abs_add_le _ _).trans (by rw [abs_one]; linarith)
  have hsplit : value s * (1 + value t) * Real.exp R - value s * (1 + value t) * Real.exp a =
      value s * (1 + value t) * Real.exp a * (Real.exp (R - a) - 1) := by
    rw [Real.exp_sub]; field_simp
  rw [hsplit, abs_mul, abs_mul, abs_mul, abs_of_pos hS, abs_of_pos (Real.exp_pos a)]
  calc value s * |1 + value t| * Real.exp a * |Real.exp (R - a) - 1| ≤
      value s * (1 + 1 / 2 ^ 53) * (10028 / 10000) * (1 / 2 ^ 60 + 1 / 2 ^ 119) := by gcongr
    _ ≤ u / 127 * value s := by rw [hu]; nlinarith

/-- The reconstruction with a scale `s = 2 ^ (q + d) H j`: its result is nearest to the exact sum
`s + s w`, which lies within `u/32` of `2 ^ d exp x`, relative to `2 ^ d exp x`. -/
theorem reconstruction_near (x s : UInt64) (k q d : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hsf : Finite s)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000) :
    let w := Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x)
      (ExpTableBounds.tailBits j.val))
    Finite (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
        (ExpTableBounds.tailBits j.val)) ∧
      F64NearestNonnegative.Nearest (value s + value w)
        (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
          (ExpTableBounds.tailBits j.val)) ∧
      |value s + value w - (2 : ℝ) ^ d * Real.exp (value x)| ≤
        u / 32 * ((2 : ℝ) ^ d * Real.exp (value x)) := by
  intro w
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨-, htf, -, -, ht⟩ := ExpTableBounds.entry_bounds j
  obtain ⟨hrf, hr, -⟩ := residual_tight x hxf hx
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  obtain ⟨hpf, hPm, hpre⟩ := presum_tight s _ _ hsf hrf htf hslo hshi hr ht
  have hres := residual_change_tight x s (ExpTableBounds.tailBits j.val) hxf hx hS ht
  have htab := ExpTableReconstruction.table_change x s k q d j hxf hx hkv hk hs hS
  set S := value s
  set P := value w
  set E := (2 : ℝ) ^ d * Real.exp (value x)
  have hsum : |S + P - E| ≤ (u / 60 + u / 127 + 1 / 2 ^ 98) * S := by
    calc |S + P - E| ≤ |S + P - S * (1 + value (ExpTableBounds.tailBits j.val)) *
          Real.exp (value (ExpResidualBounds.residual x))| +
        |S * (1 + value (ExpTableBounds.tailBits j.val)) *
          Real.exp (value (ExpResidualBounds.residual x)) -
          S * (1 + value (ExpTableBounds.tailBits j.val)) *
            Real.exp (ExpResidualBounds.ideal x)| +
        |S * (1 + value (ExpTableBounds.tailBits j.val)) * Real.exp (ExpResidualBounds.ideal x) -
          E| := (abs_sub_le _ _ _).trans (add_le_add (abs_sub_le _ _ _) le_rfl)
      _ ≤ u / 60 * S + u / 127 * S + S * (1 / 2 ^ 98) := add_le_add (add_le_add hpre hres) htab
      _ = (u / 60 + u / 127 + 1 / 2 ^ 98) * S := by ring
  -- `S ≤ 1.003 E`.
  have hi := ideal_tight x hxf hx
  have hea : 9972 / 10000 ≤ Real.exp (ExpResidualBounds.ideal x) := by
    have := Real.add_one_le_exp (ExpResidualBounds.ideal x)
    have := (abs_le.mp hi).1
    linarith
  have htb := abs_le.mp ht
  have htabb := abs_le.mp htab
  have hSE : S ≤ 10029 / 10000 * E := by
    have h1 : S * (9972 / 10000 * (1 - 1 / 2 ^ 53)) ≤
        S * (1 + value (ExpTableBounds.tailBits j.val)) * Real.exp (ExpResidualBounds.ideal x) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hS.le
      have h0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ 53 := by norm_num
      nlinarith
    nlinarith
  have hE0 : 0 < E := by positivity
  have hsumb := abs_le.mp hsum
  refine ⟨?_, ?_, ?_⟩
  · exact (F64AddBounds.add_real_relative s w hsf hpf (by
      have := abs_le.mp hPm
      rw [abs_lt]; constructor <;> nlinarith [show (2 : ℝ) ^ 1000 * 2 ≤ 2 ^ 1023 by norm_num])).1
  · apply F64NearestSum.add_nearest s w hsf hpf
    · have := abs_le.mp hPm; nlinarith
    · have := abs_le.mp hPm; nlinarith [show (2 : ℝ) ^ 1000 * 2 ≤ 2 ^ 1023 by norm_num]
  · calc |S + P - E| ≤ (u / 60 + u / 127 + 1 / 2 ^ 98) * S := hsum
      _ ≤ (u / 60 + u / 127 + 1 / 2 ^ 98) * (10029 / 10000 * E) :=
          mul_le_mul_of_nonneg_left hSE (by rw [hu]; positivity)
      _ ≤ u / 32 * E := by rw [hu]; nlinarith

#print axioms ideal_tight
#print axioms evaluation_tight
#print axioms presum_tight
#print axioms residual_change_tight
#print axioms reconstruction_near

end Library.Numerics.Float64.Exp.ExpTight
