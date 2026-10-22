import LeanExe.ProofKit.Bessel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
The functions `P` and `Q` of the large-argument form of the Bessel functions
([DLMF 10.17.3](https://dlmf.nist.gov/10.17)): for `x > 0`,

* `J₀ x = √(2/(π x)) (P₀ x cos θ₀ - Q₀ x sin θ₀)` and `Y₀ x = √(2/(π x)) (P₀ x sin θ₀ + Q₀ x cos θ₀)`
  with `θ₀ = x - π/4`;
* `J₁ x = √(2/(π x)) (P₁ x cos θ₁ - Q₁ x sin θ₁)` and `Y₁ x = √(2/(π x)) (P₁ x sin θ₁ + Q₁ x cos θ₁)`
  with `θ₁ = x - 3π/4`.

The definitions invert the rotation: `P₀ = √(π x/2) (J₀ cos θ₀ + Y₀ sin θ₀)` and
`Q₀ = √(π x/2) (Y₀ cos θ₀ - J₀ sin θ₀)`, and likewise for order 1, so the forms above and the
modulus `J ^ 2 + Y ^ 2 = (2/(π x)) (P ^ 2 + Q ^ 2)` are identities.  With `U = √(π x/2) J` and
`V = √(π x/2) Y`, Bessel's equation becomes `U'' = -(1 + κ/x ^ 2) U`, with `κ = 1/4` for order 0
and `κ = -3/4` for order 1, and the rotated pair satisfies
`P'' = 2 Q' - (κ/x ^ 2) P` and `Q'' = -2 P' - (κ/x ^ 2) Q`.  The derivatives `P₀d`, `Q₀d`, `P₁d`,
and `Q₁d` are explicit, so the energy bounds of `BesselEnergy` apply to them.
-/

namespace LeanExe.ProofKit.BesselPQ

open Real Bessel

/-- `√(π x / 2)`. -/
noncomputable def amp (x : ℝ) : ℝ := √(π * x / 2)

theorem amp_pos (x : ℝ) (hx : 0 < x) : 0 < amp x := Real.sqrt_pos.mpr (by positivity)

theorem amp_sq (x : ℝ) (hx : 0 < x) : amp x ^ 2 = π * x / 2 := Real.sq_sqrt (by positivity)

theorem hasDerivAt_amp (x : ℝ) (hx : 0 < x) : HasDerivAt amp (amp x / (2 * x)) x := by
  have hpos : 0 < π * x / 2 := by positivity
  have h := (Real.hasDerivAt_sqrt hpos.ne').comp x (((hasDerivAt_id' x).const_mul π).div_const 2)
  refine h.congr_deriv ?_
  have hs := amp_pos x hx
  have hs2 := amp_sq x hx
  simp only [amp] at hs hs2 ⊢
  field_simp
  nlinarith [hs2]

/-- `U cos (y - φ) + V sin (y - φ)`. -/
noncomputable def rotP (U V : ℝ → ℝ) (φ y : ℝ) : ℝ := U y * cos (y - φ) + V y * sin (y - φ)

/-- `V cos (y - φ) - U sin (y - φ)`. -/
noncomputable def rotQ (U V : ℝ → ℝ) (φ y : ℝ) : ℝ := V y * cos (y - φ) - U y * sin (y - φ)

theorem hasDerivAt_rotP {U V : ℝ → ℝ} {U' V' φ x : ℝ} (hU : HasDerivAt U U' x)
    (hV : HasDerivAt V V' x) :
    HasDerivAt (rotP U V φ) (U' * cos (x - φ) + V' * sin (x - φ) + rotQ U V φ x) x := by
  have hc : HasDerivAt (fun y => cos (y - φ)) (-sin (x - φ)) x := by
    have h := (Real.hasDerivAt_cos (x - φ)).comp x ((hasDerivAt_id' x).sub_const φ)
    rw [mul_one] at h
    exact h
  have hs : HasDerivAt (fun y => sin (y - φ)) (cos (x - φ)) x := by
    have h := (Real.hasDerivAt_sin (x - φ)).comp x ((hasDerivAt_id' x).sub_const φ)
    rw [mul_one] at h
    exact h
  refine ((hU.mul hc).add (hV.mul hs)).congr_deriv ?_
  simp only [rotQ]
  ring

theorem hasDerivAt_rotQ {U V : ℝ → ℝ} {U' V' φ x : ℝ} (hU : HasDerivAt U U' x)
    (hV : HasDerivAt V V' x) :
    HasDerivAt (rotQ U V φ) (V' * cos (x - φ) - U' * sin (x - φ) - rotP U V φ x) x := by
  have hc : HasDerivAt (fun y => cos (y - φ)) (-sin (x - φ)) x := by
    have h := (Real.hasDerivAt_cos (x - φ)).comp x ((hasDerivAt_id' x).sub_const φ)
    rw [mul_one] at h
    exact h
  have hs : HasDerivAt (fun y => sin (y - φ)) (cos (x - φ)) x := by
    have h := (Real.hasDerivAt_sin (x - φ)).comp x ((hasDerivAt_id' x).sub_const φ)
    rw [mul_one] at h
    exact h
  refine ((hV.mul hc).sub (hU.mul hs)).congr_deriv ?_
  simp only [rotP]
  ring

/-- The system of the rotated pair, from `U'' = -(1 + f) U` and `V'' = -(1 + f) V` at `x`. -/
theorem rot_system {U V U1 V1 : ℝ → ℝ} {f φ x : ℝ} (hU : HasDerivAt U (U1 x) x)
    (hV : HasDerivAt V (V1 x) x) (hU1 : HasDerivAt U1 (-(1 + f) * U x) x)
    (hV1 : HasDerivAt V1 (-(1 + f) * V x) x) :
    HasDerivAt (rotP U V φ) (rotP U1 V1 φ x + rotQ U V φ x) x ∧
      HasDerivAt (rotQ U V φ) (rotQ U1 V1 φ x - rotP U V φ x) x ∧
      HasDerivAt (fun y => rotP U1 V1 φ y + rotQ U V φ y)
        (2 * (rotQ U1 V1 φ x - rotP U V φ x) - f * rotP U V φ x) x ∧
      HasDerivAt (fun y => rotQ U1 V1 φ y - rotP U V φ y)
        (-2 * (rotP U1 V1 φ x + rotQ U V φ x) - f * rotQ U V φ x) x := by
  have hP := hasDerivAt_rotP (φ := φ) hU hV
  have hQ := hasDerivAt_rotQ (φ := φ) hU hV
  have hP1 := hasDerivAt_rotP (φ := φ) hU1 hV1
  have hQ1 := hasDerivAt_rotQ (φ := φ) hU1 hV1
  refine ⟨hP, hQ, (hP1.add hQ).congr_deriv ?_, (hQ1.sub hP).congr_deriv ?_⟩
  · simp only [rotP, rotQ]; ring
  · simp only [rotP, rotQ]; ring

/-! Order 0. -/

noncomputable def U0 (y : ℝ) : ℝ := amp y * J0 y
noncomputable def V0 (y : ℝ) : ℝ := amp y * Y0 y
noncomputable def U0d (y : ℝ) : ℝ := amp y * (J0 y / (2 * y) - J1 y)
noncomputable def V0d (y : ℝ) : ℝ := amp y * (Y0 y / (2 * y) - Y1 y)

theorem hasDerivAt_U0 (x : ℝ) (hx : 0 < x) : HasDerivAt U0 (U0d x) x := by
  refine ((hasDerivAt_amp x hx).mul (hasDerivAt_J0 x)).congr_deriv ?_
  simp only [U0d]
  ring

theorem hasDerivAt_V0 (x : ℝ) (hx : 0 < x) : HasDerivAt V0 (V0d x) x := by
  refine ((hasDerivAt_amp x hx).mul (hasDerivAt_Y0 x hx.ne')).congr_deriv ?_
  simp only [V0d]
  ring

theorem hasDerivAt_U0d (x : ℝ) (hx : 0 < x) :
    HasDerivAt U0d (-(1 + 1 / 4 / x ^ 2) * U0 x) x := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
  have h := (hasDerivAt_amp x hx).mul (((hasDerivAt_J0 x).div h2 (by positivity)).sub
    (hasDerivAt_J1' x hx.ne'))
  refine h.congr_deriv ?_
  simp only [U0, Pi.div_apply, Pi.sub_apply]
  field_simp
  ring

theorem hasDerivAt_V0d (x : ℝ) (hx : 0 < x) :
    HasDerivAt V0d (-(1 + 1 / 4 / x ^ 2) * V0 x) x := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
  have h := (hasDerivAt_amp x hx).mul (((hasDerivAt_Y0 x hx.ne').div h2 (by positivity)).sub
    (hasDerivAt_Y1 x hx.ne'))
  refine h.congr_deriv ?_
  simp only [V0, Pi.div_apply, Pi.sub_apply]
  field_simp
  ring

/-- `P₀ = √(π x/2) (J₀ cos θ₀ + Y₀ sin θ₀)`. -/
noncomputable def P0 : ℝ → ℝ := rotP U0 V0 (π / 4)
/-- `Q₀ = √(π x/2) (Y₀ cos θ₀ - J₀ sin θ₀)`. -/
noncomputable def Q0 : ℝ → ℝ := rotQ U0 V0 (π / 4)
/-- The derivative of `P₀`. -/
noncomputable def P0d (y : ℝ) : ℝ := rotP U0d V0d (π / 4) y + rotQ U0 V0 (π / 4) y
/-- The derivative of `Q₀`. -/
noncomputable def Q0d (y : ℝ) : ℝ := rotQ U0d V0d (π / 4) y - rotP U0 V0 (π / 4) y

theorem P0_eq (x : ℝ) : P0 x = √(π * x / 2) * (J0 x * cos (x - π / 4) + Y0 x * sin (x - π / 4)) := by
  simp only [P0, rotP, U0, V0, amp]; ring

theorem Q0_eq (x : ℝ) : Q0 x = √(π * x / 2) * (Y0 x * cos (x - π / 4) - J0 x * sin (x - π / 4)) := by
  simp only [Q0, rotQ, U0, V0, amp]; ring

theorem P0_system (x : ℝ) (hx : 0 < x) :
    HasDerivAt P0 (P0d x) x ∧ HasDerivAt Q0 (Q0d x) x ∧
      HasDerivAt P0d (2 * Q0d x - 1 / 4 / x ^ 2 * P0 x) x ∧
      HasDerivAt Q0d (-2 * P0d x - 1 / 4 / x ^ 2 * Q0 x) x := by
  obtain ⟨h1, h2, h3, h4⟩ := rot_system (φ := π / 4) (hasDerivAt_U0 x hx) (hasDerivAt_V0 x hx)
    (hasDerivAt_U0d x hx) (hasDerivAt_V0d x hx)
  exact ⟨h1, h2, h3, h4⟩

/-! Order 1. -/

noncomputable def U1 (y : ℝ) : ℝ := amp y * J1 y
noncomputable def V1 (y : ℝ) : ℝ := amp y * Y1 y
noncomputable def U1d (y : ℝ) : ℝ := amp y * (J0 y - J1 y / (2 * y))
noncomputable def V1d (y : ℝ) : ℝ := amp y * (Y0 y - Y1 y / (2 * y))

theorem hasDerivAt_U1 (x : ℝ) (hx : 0 < x) : HasDerivAt U1 (U1d x) x := by
  refine ((hasDerivAt_amp x hx).mul (hasDerivAt_J1' x hx.ne')).congr_deriv ?_
  simp only [U1d]
  field_simp
  ring

theorem hasDerivAt_V1 (x : ℝ) (hx : 0 < x) : HasDerivAt V1 (V1d x) x := by
  refine ((hasDerivAt_amp x hx).mul (hasDerivAt_Y1 x hx.ne')).congr_deriv ?_
  simp only [V1d]
  field_simp
  ring

theorem hasDerivAt_U1d (x : ℝ) (hx : 0 < x) :
    HasDerivAt U1d (-(1 + -3 / 4 / x ^ 2) * U1 x) x := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
  have h := (hasDerivAt_amp x hx).mul ((hasDerivAt_J0 x).sub
    ((hasDerivAt_J1' x hx.ne').div h2 (by positivity)))
  refine h.congr_deriv ?_
  simp only [U1, Pi.div_apply, Pi.sub_apply]
  field_simp
  ring

theorem hasDerivAt_V1d (x : ℝ) (hx : 0 < x) :
    HasDerivAt V1d (-(1 + -3 / 4 / x ^ 2) * V1 x) x := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)
  have h := (hasDerivAt_amp x hx).mul ((hasDerivAt_Y0 x hx.ne').sub
    ((hasDerivAt_Y1 x hx.ne').div h2 (by positivity)))
  refine h.congr_deriv ?_
  simp only [V1, Pi.div_apply, Pi.sub_apply]
  field_simp
  ring

/-- `P₁ = √(π x/2) (J₁ cos θ₁ + Y₁ sin θ₁)`. -/
noncomputable def P1 : ℝ → ℝ := rotP U1 V1 (3 * π / 4)
/-- `Q₁ = √(π x/2) (Y₁ cos θ₁ - J₁ sin θ₁)`. -/
noncomputable def Q1 : ℝ → ℝ := rotQ U1 V1 (3 * π / 4)
/-- The derivative of `P₁`. -/
noncomputable def P1d (y : ℝ) : ℝ := rotP U1d V1d (3 * π / 4) y + rotQ U1 V1 (3 * π / 4) y
/-- The derivative of `Q₁`. -/
noncomputable def Q1d (y : ℝ) : ℝ := rotQ U1d V1d (3 * π / 4) y - rotP U1 V1 (3 * π / 4) y

theorem P1_eq (x : ℝ) :
    P1 x = √(π * x / 2) * (J1 x * cos (x - 3 * π / 4) + Y1 x * sin (x - 3 * π / 4)) := by
  simp only [P1, rotP, U1, V1, amp]; ring

theorem Q1_eq (x : ℝ) :
    Q1 x = √(π * x / 2) * (Y1 x * cos (x - 3 * π / 4) - J1 x * sin (x - 3 * π / 4)) := by
  simp only [Q1, rotQ, U1, V1, amp]; ring

theorem P1_system (x : ℝ) (hx : 0 < x) :
    HasDerivAt P1 (P1d x) x ∧ HasDerivAt Q1 (Q1d x) x ∧
      HasDerivAt P1d (2 * Q1d x - -3 / 4 / x ^ 2 * P1 x) x ∧
      HasDerivAt Q1d (-2 * P1d x - -3 / 4 / x ^ 2 * Q1 x) x := by
  obtain ⟨h1, h2, h3, h4⟩ := rot_system (φ := 3 * π / 4) (hasDerivAt_U1 x hx) (hasDerivAt_V1 x hx)
    (hasDerivAt_U1d x hx) (hasDerivAt_V1d x hx)
  exact ⟨h1, h2, h3, h4⟩

/-! The large-argument forms and the moduli. -/

theorem amp_inv (x : ℝ) (hx : 0 < x) : √(2 / (π * x)) * amp x = 1 := by
  rw [amp, ← Real.sqrt_mul (by positivity)]
  rw [show 2 / (π * x) * (π * x / 2) = 1 by field_simp]
  exact Real.sqrt_one

theorem rot_inverse (U V : ℝ → ℝ) (φ y : ℝ) :
    rotP U V φ y * cos (y - φ) - rotQ U V φ y * sin (y - φ) = U y ∧
      rotP U V φ y * sin (y - φ) + rotQ U V φ y * cos (y - φ) = V y := by
  have h := Real.sin_sq_add_cos_sq (y - φ)
  constructor
  · simp only [rotP, rotQ]; linear_combination U y * h
  · simp only [rotP, rotQ]; linear_combination V y * h

theorem J0_large (x : ℝ) (hx : 0 < x) :
    J0 x = √(2 / (π * x)) * (P0 x * cos (x - π / 4) - Q0 x * sin (x - π / 4)) := by
  rw [P0, Q0, (rot_inverse U0 V0 (π / 4) x).1, U0, ← mul_assoc, amp_inv x hx, one_mul]

theorem Y0_large (x : ℝ) (hx : 0 < x) :
    Y0 x = √(2 / (π * x)) * (P0 x * sin (x - π / 4) + Q0 x * cos (x - π / 4)) := by
  rw [P0, Q0, (rot_inverse U0 V0 (π / 4) x).2, V0, ← mul_assoc, amp_inv x hx, one_mul]

theorem J1_large (x : ℝ) (hx : 0 < x) :
    J1 x = √(2 / (π * x)) * (P1 x * cos (x - 3 * π / 4) - Q1 x * sin (x - 3 * π / 4)) := by
  rw [P1, Q1, (rot_inverse U1 V1 (3 * π / 4) x).1, U1, ← mul_assoc, amp_inv x hx, one_mul]

theorem Y1_large (x : ℝ) (hx : 0 < x) :
    Y1 x = √(2 / (π * x)) * (P1 x * sin (x - 3 * π / 4) + Q1 x * cos (x - 3 * π / 4)) := by
  rw [P1, Q1, (rot_inverse U1 V1 (3 * π / 4) x).2, V1, ← mul_assoc, amp_inv x hx, one_mul]

theorem rot_norm (U V : ℝ → ℝ) (φ y : ℝ) :
    rotP U V φ y ^ 2 + rotQ U V φ y ^ 2 = U y ^ 2 + V y ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (y - φ)
  simp only [rotP, rotQ]
  linear_combination (U y ^ 2 + V y ^ 2) * h

theorem modulus0 (x : ℝ) (hx : 0 < x) :
    J0 x ^ 2 + Y0 x ^ 2 = 2 / (π * x) * (P0 x ^ 2 + Q0 x ^ 2) := by
  rw [P0, Q0, rot_norm, U0, V0, mul_pow, mul_pow, amp_sq x hx]
  field_simp

theorem modulus1 (x : ℝ) (hx : 0 < x) :
    J1 x ^ 2 + Y1 x ^ 2 = 2 / (π * x) * (P1 x ^ 2 + Q1 x ^ 2) := by
  rw [P1, Q1, rot_norm, U1, V1, mul_pow, mul_pow, amp_sq x hx]
  field_simp

#print axioms P0_system
#print axioms P1_system
#print axioms J0_large
#print axioms Y0_large
#print axioms J1_large
#print axioms Y1_large
#print axioms modulus0
#print axioms modulus1

end LeanExe.ProofKit.BesselPQ
