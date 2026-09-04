import Project.EulerRusanov.Bounds
import Project.EulerRusanov.RealEigenbasis

/-!
# Raw guards imply real Euler admissibility and spectral bounds

The executable entry accepts primitive states as raw binary64 words.  This
module joins the existing word-level guard proof to the conservative-coordinate
real Euler theory:

* an accepted state decodes to strictly positive density and pressure;
* its primitive-to-conservative image is in the open admissible set; and
* every characteristic value of the conservative flux Jacobian has absolute
  value at most the artifact's fixed `alpha = 7 / 4`.

The sound speed in the last statement is the exact-real `Real.sqrt` appearing
in the mathematical eigensystem.  Nothing here claims that the executable
evaluates a square root: the generated flux continues to use the already
certified fixed signal-speed bound.
-/

namespace Project.EulerRusanov.RealGuardBridge

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealEigenbasis

noncomputable section

/-! ## Decoded positivity and conservative admissibility -/

/-- A successfully bounded raw density decodes to a strictly positive real. -/
theorem decodedPrimitive_density_pos
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) :
    0 < (Model.primitiveRealOfBits rho u p).rho := by
  change 0 < CodeLib.IEEE64.value rho
  linarith [h.densityLower]

/-- A successfully bounded raw pressure decodes to a strictly positive real. -/
theorem decodedPrimitive_pressure_pos
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) :
    0 < (Model.primitiveRealOfBits rho u p).pressure := by
  change 0 < CodeLib.IEEE64.value p
  linarith [h.pressureLower]

/-- The primitive positivity facts supplied by a successful state guard. -/
theorem decodedPrimitive_positive
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) :
    0 < (Model.primitiveRealOfBits rho u p).rho ∧
      0 < (Model.primitiveRealOfBits rho u p).pressure :=
  ⟨decodedPrimitive_density_pos h, decodedPrimitive_pressure_pos h⟩

/-- Guarded primitive data maps to an admissible conservative Euler state. -/
theorem decodedConservative_admissible
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) :
    Admissible
      (primitiveToConservative (Model.primitiveRealOfBits rho u p)) := by
  apply primitiveToConservative_admissible
  · exact decodedPrimitive_density_pos h
  · exact decodedPrimitive_pressure_pos h

/-- Direct state-guard interface to conservative admissibility. -/
theorem stateGuard_decodedConservative_admissible
    (rho u p : UInt64) (hguard : Model.stateGuard rho u p = true) :
    Admissible
      (primitiveToConservative (Model.primitiveRealOfBits rho u p)) :=
  decodedConservative_admissible (Bounds.stateGuard_spec rho u p hguard)

/-- A successful six-word guard supplies admissibility on both sides of the
Rusanov interface. -/
theorem eulerGuard_decodedConservative_admissible
    (rhoL uL pL rhoR uR pR : UInt64)
    (hguard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    Admissible
        (primitiveToConservative
          (Model.primitiveRealOfBits rhoL uL pL)) ∧
      Admissible
        (primitiveToConservative
          (Model.primitiveRealOfBits rhoR uR pR)) := by
  have hbounds := Bounds.eulerGuard_spec
    rhoL uL pL rhoR uR pR hguard
  exact ⟨decodedConservative_admissible hbounds.1,
    decodedConservative_admissible hbounds.2⟩

/-! ## Fixed alpha as a characteristic-value bound -/

/-- The conservative sound speed agrees with the primitive ideal-gas
expression after the primitive-to-conservative map.  This is an exact-real
identity, not an executable square-root evaluation. -/
theorem soundSpeed_primitiveToConservative (q : Model.PrimitiveReal) :
    soundSpeed (primitiveToConservative q) =
      Real.sqrt (Model.gammaReal * q.pressure / q.rho) := by
  simp only [soundSpeed, soundSpeedSquared,
    pressure_primitiveToConservative q,
    density_primitiveToConservative]

/-- Each of `u-c`, `u`, and `u+c` is bounded in magnitude by `|u|+c` when
the sound-speed parameter is nonnegative. -/
theorem abs_eigenvalues_le_signalSpeed
    (u c : ℝ) (hc : 0 ≤ c) (i : Fin 3) :
    |eigenvalues u c i| ≤ |u| + c := by
  fin_cases i
  · change |u - c| ≤ |u| + c
    rw [abs_le]
    constructor <;> linarith [le_abs_self u, neg_abs_le u]
  · change |u| ≤ |u| + c
    linarith
  · change |u + c| ≤ |u| + c
    rw [abs_le]
    constructor <;> linarith [le_abs_self u, neg_abs_le u]

/-- At a positive-density primitive state, every conservative characteristic
value is bounded by the standard local signal-speed expression. -/
theorem primitive_characteristic_abs_le_signalSpeed
    (q : Model.PrimitiveReal) (hrho : 0 < q.rho) (i : Fin 3) :
    |characteristicValues (primitiveToConservative q) i| ≤
      |q.velocity| +
        Real.sqrt (Model.gammaReal * q.pressure / q.rho) := by
  simpa only [characteristicValues,
    velocity_primitiveToConservative q (ne_of_gt hrho),
    soundSpeed_primitiveToConservative q] using
    abs_eigenvalues_le_signalSpeed q.velocity
      (Real.sqrt (Model.gammaReal * q.pressure / q.rho))
      (Real.sqrt_nonneg _) i

/-- The word-level state bounds and the fixed-speed certificate together
bound every eigenvalue of the decoded conservative Jacobian by `alpha`. -/
theorem decodedCharacteristic_abs_le_alpha
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) (i : Fin 3) :
    |characteristicValues
        (primitiveToConservative (Model.primitiveRealOfBits rho u p)) i| ≤
      Model.alphaReal := by
  calc
    |characteristicValues
        (primitiveToConservative (Model.primitiveRealOfBits rho u p)) i| ≤
        |(Model.primitiveRealOfBits rho u p).velocity| +
          Real.sqrt
            (Model.gammaReal *
              (Model.primitiveRealOfBits rho u p).pressure /
              (Model.primitiveRealOfBits rho u p).rho) :=
      primitive_characteristic_abs_le_signalSpeed
        (Model.primitiveRealOfBits rho u p)
        (decodedPrimitive_density_pos h) i
    _ = |CodeLib.IEEE64.value u| +
          Real.sqrt
            (Model.gammaReal * CodeLib.IEEE64.value p /
              CodeLib.IEEE64.value rho) := by
      rfl
    _ ≤ Model.alphaReal := h.signalSpeed_le_alpha

/-- Spectral form of `decodedCharacteristic_abs_le_alpha`: every one of the
three characteristic values lies in the closed interval `[-alpha, alpha]`. -/
theorem decodedCharacteristic_spectralBound
    {rho u p : UInt64} (h : Bounds.StateBounds rho u p) :
    ∀ i : Fin 3,
      |characteristicValues
          (primitiveToConservative (Model.primitiveRealOfBits rho u p)) i| ≤
        Model.alphaReal :=
  fun i => decodedCharacteristic_abs_le_alpha h i

/-- Direct state-guard interface to the characteristic absolute bound. -/
theorem stateGuard_characteristic_spectralBound
    (rho u p : UInt64) (hguard : Model.stateGuard rho u p = true) :
    ∀ i : Fin 3,
      |characteristicValues
          (primitiveToConservative (Model.primitiveRealOfBits rho u p)) i| ≤
        Model.alphaReal :=
  decodedCharacteristic_spectralBound
    (Bounds.stateGuard_spec rho u p hguard)

/-- Both decoded states admitted by the complete entry guard have all three
characteristic values bounded in magnitude by the fixed Rusanov speed. -/
theorem eulerGuard_characteristic_spectralBound
    (rhoL uL pL rhoR uR pR : UInt64)
    (hguard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    (∀ i : Fin 3,
      |characteristicValues
          (primitiveToConservative
            (Model.primitiveRealOfBits rhoL uL pL)) i| ≤
        Model.alphaReal) ∧
      (∀ i : Fin 3,
        |characteristicValues
            (primitiveToConservative
              (Model.primitiveRealOfBits rhoR uR pR)) i| ≤
          Model.alphaReal) := by
  have hbounds := Bounds.eulerGuard_spec
    rhoL uL pL rhoR uR pR hguard
  exact ⟨decodedCharacteristic_spectralBound hbounds.1,
    decodedCharacteristic_spectralBound hbounds.2⟩

#print axioms decodedConservative_admissible
#print axioms stateGuard_decodedConservative_admissible
#print axioms decodedCharacteristic_abs_le_alpha
#print axioms eulerGuard_characteristic_spectralBound

end

end Project.EulerRusanov.RealGuardBridge
