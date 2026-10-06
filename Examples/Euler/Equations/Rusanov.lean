import Examples.Euler.Equations.CharacteristicSpeed
import Examples.Euler.Equations.LaxFriedrichs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! The Rusanov flux and update in exact arithmetic.  The interface flux is the local
Lax–Friedrichs flux of `xFlux`, so it has the two-wave form of `LaxFriedrichs`.  An update of a
cell from its two interfaces is a convex combination of the cell state and two split states when
the CFL numbers are at most 1/2, and a split state keeps positive density and at least 6/7 of the
internal energy, scaled by the density factor, when its wave speed bound holds. -/

namespace Examples.Euler.Equations.Rusanov

open Examples.Euler.Equations LaxFriedrichs

noncomputable section

/-- The state moved along the flux by `b`. -/
def splitState (q : Vec4) (b : ℝ) : Vec4 := fun i => q i + b * xFlux q i

def interfaceFlux (a : ℝ) (left right : Vec4) : Vec4 :=
  fun i => (xFlux left i + xFlux right i) / 2 - a * (right i - left i) / 2

/-- A cell updated from its left and right interfaces, with speeds `aLeft` and `aRight` and the
ratio of the timestep to the cell width. -/
def update (ratio aLeft aRight : ℝ) (left center right : Vec4) : Vec4 :=
  fun i => center i - ratio * (interfaceFlux aRight center right i - interfaceFlux aLeft left center i)

def combine (a b c : ℝ) (q r s : Vec4) : Vec4 := fun i => a * q i + b * r i + c * s i

theorem update_decomposition (ratio aLeft aRight : ℝ) (left center right : Vec4)
    (hLeft : aLeft ≠ 0) (hRight : aRight ≠ 0) :
    update ratio aLeft aRight left center right =
      combine (1 - ratio * (aLeft + aRight) / 2) (ratio * aLeft / 2) (ratio * aRight / 2)
        center (splitState left (1 / aLeft)) (splitState right (-1 / aRight)) := by
  funext i
  simp only [update, interfaceFlux, combine, splitState]
  field_simp [hLeft, hRight]
  ring

theorem coefficients (ratio aLeft aRight : ℝ) (hRatio : 0 ≤ ratio) (hLeft : 0 < aLeft)
    (hRight : 0 < aRight) (hCflLeft : ratio * aLeft ≤ 1 / 2) (hCflRight : ratio * aRight ≤ 1 / 2) :
    1 / 2 ≤ 1 - ratio * (aLeft + aRight) / 2 ∧ 0 ≤ ratio * aLeft / 2 ∧ 0 ≤ ratio * aRight / 2 ∧
      (1 - ratio * (aLeft + aRight) / 2) + ratio * aLeft / 2 + ratio * aRight / 2 = 1 := by
  refine ⟨by nlinarith, by positivity, by positivity, by ring⟩

def kineticTest (u v : ℝ) (q : Vec4) : ℝ := q 3 - u * q 1 - v * q 2 + q 0 * (u^2 + v^2) / 2

theorem kineticTest_identity (q : Vec4) (hDensity : q 0 ≠ 0) (u v : ℝ) :
    kineticTest u v q =
      internalEnergy q + ((q 1 - q 0 * u)^2 + (q 2 - q 0 * v)^2) / (2 * q 0) := by
  simp only [kineticTest, internalEnergy]
  field_simp [hDensity]
  ring

theorem internalEnergy_le_test (q : Vec4) (hDensity : 0 < q 0) (u v : ℝ) :
    internalEnergy q ≤ kineticTest u v q := by
  rw [kineticTest_identity q (ne_of_gt hDensity)]
  exact le_add_of_nonneg_right (by positivity)

theorem kineticTest_at_velocity (q : Vec4) (hDensity : q 0 ≠ 0) :
    kineticTest (q 1 / q 0) (q 2 / q 0) q = internalEnergy q := by
  simp only [kineticTest, internalEnergy]
  field_simp [hDensity]
  ring

theorem combine_density_positive (a b c : ℝ) (q r s : Vec4) (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hq : 0 < q 0) (hr : 0 < r 0) (hs : 0 < s 0) : 0 < combine a b c q r s 0 := by
  simp only [combine]
  positivity

/-- Internal energy is concave along convex combinations of states with positive density. -/
theorem combine_internalEnergy_lower (a b c : ℝ) (q r s : Vec4) (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hq : 0 < q 0) (hr : 0 < r 0) (hs : 0 < s 0) :
    a * internalEnergy q + b * internalEnergy r + c * internalEnergy s ≤
      internalEnergy (combine a b c q r s) := by
  let result := combine a b c q r s
  let u := result 1 / result 0
  let v := result 2 / result 0
  have hResult : 0 < result 0 := combine_density_positive a b c q r s ha hb hc hq hr hs
  calc
    a * internalEnergy q + b * internalEnergy r + c * internalEnergy s ≤
        a * kineticTest u v q + b * kineticTest u v r + c * kineticTest u v s :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test q hq u v) ha.le)
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test r hr u v) hb))
        (mul_le_mul_of_nonneg_left (internalEnergy_le_test s hs u v) hc)
    _ = kineticTest u v result := by simp only [kineticTest, result, combine]; ring
    _ = internalEnergy result := kineticTest_at_velocity result (ne_of_gt hResult)

def energyMargin (q : Vec4) : ℝ := 2 * q 0 * q 3 - (q 1)^2 - (q 2)^2

theorem internalEnergy_eq_margin (q : Vec4) (hDensity : q 0 ≠ 0) :
    internalEnergy q = energyMargin q / (2 * q 0) := by
  simp only [internalEnergy, energyMargin]
  field_simp [hDensity]
  ring

theorem split_density (q : Vec4) (b : ℝ) (hDensity : q 0 ≠ 0) :
    splitState q b 0 = q 0 * (1 + b * (q 1 / q 0)) := by
  simp [splitState, xFlux]
  field_simp [hDensity]

theorem split_energyMargin (q : Vec4) (b : ℝ) (hDensity : q 0 ≠ 0) :
    energyMargin (splitState q b) =
      (1 + b * (q 1 / q 0))^2 * energyMargin q - (b * pressure q)^2 := by
  simp [energyMargin, splitState, xFlux, velocity, pressure, internalEnergy]
  field_simp [hDensity]
  ring

theorem split_internalEnergy_lower (q : Vec4) (b theta : ℝ) (hDensity : 0 < q 0)
    (hFactor : 0 < 1 + b * (q 1 / q 0))
    (hLoss : (b * pressure q)^2 ≤ theta * (1 + b * (q 1 / q 0))^2 * energyMargin q) :
    0 < splitState q b 0 ∧
      (1 - theta) * (1 + b * (q 1 / q 0)) * internalEnergy q ≤ internalEnergy (splitState q b) := by
  have hSplit : 0 < splitState q b 0 := by
    rw [split_density q b (ne_of_gt hDensity)]
    exact mul_pos hDensity hFactor
  refine ⟨hSplit, ?_⟩
  rw [internalEnergy_eq_margin (splitState q b) (ne_of_gt hSplit)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * splitState q b 0)).mpr
  rw [split_density q b (ne_of_gt hDensity), internalEnergy_eq_margin q (ne_of_gt hDensity),
    split_energyMargin q b (ne_of_gt hDensity)]
  have hCancel :
      (1 - theta) * (1 + b * (q 1 / q 0)) * (energyMargin q / (2 * q 0)) *
          (2 * (q 0 * (1 + b * (q 1 / q 0)))) =
        (1 - theta) * (1 + b * (q 1 / q 0))^2 * energyMargin q := by
    field_simp [ne_of_gt hDensity]
  rw [hCancel]
  nlinarith

theorem energyMargin_positive (q : Vec4) (hDensity : 0 < q 0) (hInternal : 0 < internalEnergy q) :
    0 < energyMargin q := by
  rw [internalEnergy_eq_margin q (ne_of_gt hDensity)] at hInternal
  exact (div_pos_iff_of_pos_right (by positivity : 0 < 2 * q 0)).mp hInternal

theorem wave_factor (u c b : ℝ) (hc : 0 < c) (hWave : |b| * (|u| + c) ≤ 1) :
    0 < 1 + b * u ∧ |b| * c ≤ 1 + b * u := by
  have hProduct := neg_abs_le (b * u)
  rw [abs_mul] at hProduct
  have hLower : |b| * c ≤ 1 + b * u := by nlinarith
  refine ⟨?_, hLower⟩
  by_cases hb : b = 0
  · simp [hb]
  · exact lt_of_lt_of_le (mul_pos (abs_pos.mpr hb) hc) hLower

theorem sound_pressure_identity (q : Vec4) (c : ℝ) (hDensity : q 0 ≠ 0)
    (hSound : c^2 = (7 / 5) * pressure q / q 0) : 7 * (pressure q)^2 = c^2 * energyMargin q := by
  rw [hSound]
  simp only [pressure, internalEnergy, energyMargin]
  field_simp [hDensity]
  ring

/-- A split state with wave speed bound `|b| (|u| + c) ≤ 1` has positive density and keeps at
least 6/7 of the internal energy, scaled by its density factor. -/
theorem split_sound_lower (q : Vec4) (b c : ℝ) (hDensity : 0 < q 0)
    (hInternal : 0 < internalEnergy q) (hc : 0 < c) (hSound : c^2 = (7 / 5) * pressure q / q 0)
    (hWave : |b| * (|q 1 / q 0| + c) ≤ 1) :
    0 < splitState q b 0 ∧
      (6 / 7) * (1 + b * (q 1 / q 0)) * internalEnergy q ≤ internalEnergy (splitState q b) := by
  obtain ⟨hFactor, hLower⟩ := wave_factor (q 1 / q 0) c b hc hWave
  have hMargin := energyMargin_positive q hDensity hInternal
  have hSquare : (b * c)^2 ≤ (1 + b * (q 1 / q 0))^2 := by
    have hAbs : |b * c| ≤ 1 + b * (q 1 / q 0) := by
      simpa only [abs_mul, abs_of_pos hc] using hLower
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b * c)) hFactor.le).mpr hAbs
  have hWeighted := mul_le_mul_of_nonneg_right hSquare hMargin.le
  have hIdentity := sound_pressure_identity q c (ne_of_gt hDensity) hSound
  have hLoss : (b * pressure q)^2 ≤ (1 / 7) * (1 + b * (q 1 / q 0))^2 * energyMargin q := by
    have hScaled := congrArg (fun x : ℝ => b^2 * x) hIdentity
    nlinarith only [hWeighted, hScaled]
  have hResult := split_internalEnergy_lower q b (1 / 7) hDensity hFactor hLoss
  norm_num only at hResult
  exact hResult

/-! The two-wave form of the interface flux. -/

theorem interfaceFlux_eq_numericalFlux (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = numericalFlux xFlux a L R := rfl

theorem interface_consistent (a : ℝ) (U : Vec4) : interfaceFlux a U U = xFlux U :=
  numericalFlux_consistent _ _ _

theorem interface_left_fluctuation (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = xFlux L + fluctuationMinus a (R - L) (xFlux R - xFlux L) :=
  numericalFlux_left _ _ _ _

theorem interface_right_fluctuation (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = xFlux R - fluctuationPlus a (R - L) (xFlux R - xFlux L) :=
  numericalFlux_right _ _ _ _

/-- In every direction, the two waves of a jump sum to the jump, and their sum weighted by the
speeds `-a` and `a` is the flux jump. -/
theorem directional_wave_identities (n : Direction) (a : ℝ) (ha : a ≠ 0) (L R : Vec4) :
    let jump := R - L
    let fluxJump := directionalFlux n R - directionalFlux n L
    waveMinus a jump fluxJump + wavePlus a jump fluxJump = jump ∧
      -a • waveMinus a jump fluxJump + a • wavePlus a jump fluxJump = fluxJump :=
  ⟨wave_sum _ _ _, weighted_wave_sum _ ha _ _⟩

theorem directional_flux_reverse (n : Direction) (U : Vec4) :
    directionalFlux (-n) U = -directionalFlux n U := by
  funext i
  simp only [directionalFlux, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The numerical flux from `R` to `L` in direction `-n` is the negated flux from `L` to `R` in
direction `n`. -/
theorem directional_interface_reverse (n : Direction) (a : ℝ) (L R : Vec4) :
    numericalFlux (directionalFlux (-n)) a R L = -numericalFlux (directionalFlux n) a L R := by
  have h : directionalFlux (-n) = fun U => -directionalFlux n U :=
    funext (directional_flux_reverse n)
  rw [h]
  exact numericalFlux_reverse _ _ _ _

end
end Examples.Euler.Equations.Rusanov
