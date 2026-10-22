import LeanExe.ProofKit.BesselPQ
import LeanExe.ProofKit.BesselConstants
import LeanExe.ProofKit.BesselAsym

/-!
Enclosures of `P`, `Q`, and their derivatives at `x = 2`, where the chains of `BesselChain`
start.  At `x = 2`, `z = x ^ 2/4 = 1` and `ln (x/2) = 0`, so `J₀ 2`, `J₁ 2`, `Y₀ 2`, and `Y₁ 2`
are the four series at 1 combined with `γ` and `1/π`.  The amplitude and the phases give
`√(π x/2) cos (2 - π/4) = √(π/2) (cos 2 + sin 2)` and `√(π x/2) sin (2 - π/4) = √(π/2) (sin 2 - cos 2)`,
and the order 1 phase `2 - 3π/4` exchanges them.  `root0_le_encl` and `root1_le_encl` bound the
square root of the energy by the enclosures of the four errors.
-/

namespace LeanExe.ProofKit.BesselStart

open Real Library.Numerics.Float64.Bessel BesselPQ BesselConstants EulerGamma PolyBound PolyCalc EntireSeries BesselChain
  BesselEnergy

/-! The series at `z = 1`. -/

theorem encl_A0 : Encl (psum a0 1) (evalQ (a0List 30) 1) (2 * qabs (qa0 30)) := by
  have h := a0_remainder 1 (by norm_num) 30 (by norm_num)
  unfold Encl
  rw [evalQ_cast]
  push_cast [qabs_cast]
  simpa [a0] using h

theorem encl_A1 : Encl (psum a1 1) (evalQ (a1List 30) 1) (2 * qabs (qa1 30)) := by
  have h := a1_remainder 1 (by norm_num) 30 (by norm_num)
  unfold Encl
  rw [evalQ_cast]
  push_cast [qabs_cast]
  simpa [a1] using h

theorem encl_C0 : Encl (psum c0 1) (evalQ (c0List 30) 1) (2 * qabs (qc0 30)) := by
  have h := c0_remainder 1 (by norm_num) 30 (by norm_num)
  unfold Encl
  rw [evalQ_cast]
  push_cast [qabs_cast]
  simpa [c0] using h

theorem encl_C1 : Encl (psum c1 1) (evalQ (c1List 30) 1) (2 * qabs (qc1 30)) := by
  have h := c1_remainder 1 (by norm_num) 30 (by norm_num)
  unfold Encl
  rw [evalQ_cast]
  push_cast [qabs_cast]
  simpa [c1] using h

/-! The functions at 2. -/

theorem J0_two : J0 2 = psum a0 1 := by rw [J0]; norm_num

theorem J1_two : J1 2 = psum a1 1 := by rw [J1]; norm_num

theorem Y0_two : Y0 2 = 2 * π⁻¹ * (eulerMascheroniConstant * psum a0 1 + psum c0 1) := by
  rw [Y0, J0, show (2 : ℝ) / 2 = 1 by norm_num, Real.log_one, show (2 : ℝ) ^ 2 / 4 = 1 by norm_num]
  ring

theorem Y1_two : Y1 2 = π⁻¹ * (2 * eulerMascheroniConstant * psum a1 1 - 1 - psum c1 1) := by
  rw [Y1, J1, show (2 : ℝ) / 2 = 1 by norm_num, Real.log_one, show (2 : ℝ) ^ 2 / 4 = 1 by norm_num]
  ring

theorem sqrt_half_pi : √π * (√2 / 2) = √(π / 2) := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : √2 ≠ 0 := by positivity
  rw [Real.sqrt_div pi_pos.le, eq_div_iff hs]
  calc √π * (√2 / 2) * √2 = √π * (√2 * √2) / 2 := by ring
    _ = √π := by rw [h2]; ring

theorem amp_two : amp 2 = √π := by rw [amp]; norm_num

theorem amp_cos0 : amp 2 * cos (2 - π / 4) = √(π / 2) * (cos 2 + sin 2) := by
  rw [amp_two, Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four, ← sqrt_half_pi]
  ring

theorem amp_sin0 : amp 2 * sin (2 - π / 4) = √(π / 2) * (sin 2 - cos 2) := by
  rw [amp_two, Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four, ← sqrt_half_pi]
  ring

theorem amp_cos1 : amp 2 * cos (2 - 3 * π / 4) = √(π / 2) * (sin 2 - cos 2) := by
  have e : 3 * π / 4 = π - π / 4 := by ring
  rw [amp_two, e, Real.cos_sub, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, ← sqrt_half_pi]
  ring

theorem amp_sin1 : amp 2 * sin (2 - 3 * π / 4) = -(√(π / 2) * (sin 2 + cos 2)) := by
  have e : 3 * π / 4 = π - π / 4 := by ring
  rw [amp_two, e, Real.sin_sub, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, ← sqrt_half_pi]
  ring

/-- `√(π/2) (cos 2 + sin 2)`. -/
noncomputable def KP : ℝ := √(π / 2) * (cos 2 + sin 2)
/-- `√(π/2) (sin 2 - cos 2)`. -/
noncomputable def KM : ℝ := √(π / 2) * (sin 2 - cos 2)

theorem P0_two : P0 2 = J0 2 * KP + Y0 2 * KM := by
  have hc := amp_cos0; have hs := amp_sin0
  simp only [P0, rotP, U0, V0, KP, KM]
  linear_combination J0 2 * hc + Y0 2 * hs

theorem Q0_two : Q0 2 = Y0 2 * KP - J0 2 * KM := by
  have hc := amp_cos0; have hs := amp_sin0
  simp only [Q0, rotQ, U0, V0, KP, KM]
  linear_combination Y0 2 * hc - J0 2 * hs

theorem P0d_two : P0d 2 = (J0 2 / 4 - J1 2) * KP + (Y0 2 / 4 - Y1 2) * KM + Q0 2 := by
  have hc := amp_cos0; have hs := amp_sin0
  simp only [P0d, Q0, rotP, rotQ, U0d, V0d, U0, V0, KP, KM]
  linear_combination (J0 2 / 4 - J1 2) * hc + (Y0 2 / 4 - Y1 2) * hs

theorem Q0d_two : Q0d 2 = (Y0 2 / 4 - Y1 2) * KP - (J0 2 / 4 - J1 2) * KM - P0 2 := by
  have hc := amp_cos0; have hs := amp_sin0
  simp only [Q0d, P0, rotP, rotQ, U0d, V0d, U0, V0, KP, KM]
  linear_combination (Y0 2 / 4 - Y1 2) * hc - (J0 2 / 4 - J1 2) * hs

theorem P1_two : P1 2 = J1 2 * KM - Y1 2 * KP := by
  have hc := amp_cos1; have hs := amp_sin1
  simp only [P1, rotP, U1, V1, KP, KM]
  linear_combination J1 2 * hc + Y1 2 * hs

theorem Q1_two : Q1 2 = Y1 2 * KM + J1 2 * KP := by
  have hc := amp_cos1; have hs := amp_sin1
  simp only [Q1, rotQ, U1, V1, KP, KM]
  linear_combination Y1 2 * hc - J1 2 * hs

theorem P1d_two : P1d 2 = (J0 2 - J1 2 / 4) * KM - (Y0 2 - Y1 2 / 4) * KP + Q1 2 := by
  have hc := amp_cos1; have hs := amp_sin1
  simp only [P1d, Q1, rotP, rotQ, U1d, V1d, U1, V1, KP, KM]
  linear_combination (J0 2 - J1 2 / 4) * hc + (Y0 2 - Y1 2 / 4) * hs

theorem Q1d_two : Q1d 2 = (Y0 2 - Y1 2 / 4) * KM + (J0 2 - J1 2 / 4) * KP - P1 2 := by
  have hc := amp_cos1; have hs := amp_sin1
  simp only [Q1d, P1, rotP, rotQ, U1d, V1d, U1, V1, KP, KM]
  linear_combination (Y0 2 - Y1 2 / 4) * hc - (J0 2 - J1 2 / 4) * hs

/-! The enclosures. -/

def sqrtLo : ℚ := 1665940238832783241448727957807967470 / 2 ^ 120
def sqrtHi : ℚ := 1665940238832783241448727957807967472 / 2 ^ 120

theorem encl_K : Encl √(π / 2) ((sqrtLo + sqrtHi) / 2) ((sqrtHi - sqrtLo) / 2) := by
  have h := pi_encl.const_mul (1 / 2)
  have e : ((1 / 2 : ℚ) : ℝ) * π = π / 2 := by push_cast; ring
  exact (h.congr e).sqrt (by norm_num [sqrtLo]) (by rw [piMid, piRad, sqrtLo]; decide +kernel)
    (by rw [piMid, piRad, sqrtHi]; decide +kernel) (by norm_num [sqrtLo, sqrtHi])

theorem encl_invpi : Encl π⁻¹ piMid⁻¹ (piRad / (qabs piMid * (qabs piMid - piRad))) :=
  pi_encl.inv (by rw [piMid, piRad]; decide +kernel)

def P0Hat : ℚ := 1250177077722705640849276670781 / 2 ^ 100
def Q0Hat : ℚ := -71593989898006085511148993749 / 2 ^ 100
def P0dHat : ℚ := 14477222934580684179788337872 / 2 ^ 100
def Q0dHat : ℚ := 30262222630554812885448801132 / 2 ^ 100
def P1Hat : ℚ := 1298337797827761975112512720350 / 2 ^ 100
def Q1Hat : ℚ := 226473056598089640521381836075 / 2 ^ 100
def P1dHat : ℚ := -26517402960844767745597350264 / 2 ^ 100
def Q1dHat : ℚ := -104778984254578744393581508588 / 2 ^ 100

theorem encl_series :
    Encl (J0 2) (evalQ (a0List 30) 1) (2 * qabs (qa0 30)) ∧
      Encl (J1 2) (evalQ (a1List 30) 1) (2 * qabs (qa1 30)) := by
  exact ⟨encl_A0.congr J0_two.symm, encl_A1.congr J1_two.symm⟩

set_option maxRecDepth 100000 in
/-- `P₀`, `Q₀`, and their derivatives at 2, within `2 ^ -86`. -/
theorem start_values0 :
    Encl (P0 2) P0Hat (1 / 2 ^ 86) ∧ Encl (Q0 2) Q0Hat (1 / 2 ^ 86) ∧
      Encl (P0d 2) P0dHat (1 / 2 ^ 86) ∧ Encl (Q0d 2) Q0dHat (1 / 2 ^ 86) := by
  obtain ⟨eJ0, eJ1⟩ := encl_series
  have eG : Encl eulerMascheroniConstant gammaMid gammaRad := gamma_close
  have eY0 := ((encl_invpi.const_mul 2).mul ((eG.mul encl_A0).add encl_C0)).congr (v := Y0 2)
    (by rw [Y0_two]; push_cast; ring)
  have eY1 := (encl_invpi.mul ((((eG.const_mul 2).mul encl_A1).sub (Encl.exact 1)).sub
    encl_C1)).congr (v := Y1 2) (by rw [Y1_two]; push_cast; ring)
  have eKP := (encl_K.mul (cos2_encl.add sin2_encl)).congr (v := KP) (by rw [KP])
  have eKM := (encl_K.mul (sin2_encl.sub cos2_encl)).congr (v := KM) (by rw [KM])
  have eP0 := ((eJ0.mul eKP).add (eY0.mul eKM)).congr P0_two.symm
  have eQ0 := ((eY0.mul eKP).sub (eJ0.mul eKM)).congr Q0_two.symm
  have eDJ := ((eJ0.const_mul (1 / 4)).sub eJ1).congr (by push_cast; ring :
    ((1 / 4 : ℚ) : ℝ) * J0 2 - J1 2 = J0 2 / 4 - J1 2)
  have eDY := ((eY0.const_mul (1 / 4)).sub eY1).congr (by push_cast; ring :
    ((1 / 4 : ℚ) : ℝ) * Y0 2 - Y1 2 = Y0 2 / 4 - Y1 2)
  have eP0d := (((eDJ.mul eKP).add (eDY.mul eKM)).add eQ0).congr P0d_two.symm
  have eQ0d := (((eDY.mul eKP).sub (eDJ.mul eKM)).sub eP0).congr Q0d_two.symm
  refine ⟨eP0.recenter ?_, eQ0.recenter ?_, eP0d.recenter ?_, eQ0d.recenter ?_⟩ <;>
    decide +kernel

set_option maxRecDepth 100000 in
/-- `P₁`, `Q₁`, and their derivatives at 2, within `2 ^ -86`. -/
theorem start_values1 :
    Encl (P1 2) P1Hat (1 / 2 ^ 86) ∧ Encl (Q1 2) Q1Hat (1 / 2 ^ 86) ∧
      Encl (P1d 2) P1dHat (1 / 2 ^ 86) ∧ Encl (Q1d 2) Q1dHat (1 / 2 ^ 86) := by
  obtain ⟨eJ0, eJ1⟩ := encl_series
  have eG : Encl eulerMascheroniConstant gammaMid gammaRad := gamma_close
  have eY0 := ((encl_invpi.const_mul 2).mul ((eG.mul encl_A0).add encl_C0)).congr (v := Y0 2)
    (by rw [Y0_two]; push_cast; ring)
  have eY1 := (encl_invpi.mul ((((eG.const_mul 2).mul encl_A1).sub (Encl.exact 1)).sub
    encl_C1)).congr (v := Y1 2) (by rw [Y1_two]; push_cast; ring)
  have eKP := (encl_K.mul (cos2_encl.add sin2_encl)).congr (v := KP) (by rw [KP])
  have eKM := (encl_K.mul (sin2_encl.sub cos2_encl)).congr (v := KM) (by rw [KM])
  have eP1 := ((eJ1.mul eKM).sub (eY1.mul eKP)).congr P1_two.symm
  have eQ1 := ((eY1.mul eKM).add (eJ1.mul eKP)).congr Q1_two.symm
  have eEJ := (eJ0.sub (eJ1.const_mul (1 / 4))).congr (by push_cast; ring :
    J0 2 - ((1 / 4 : ℚ) : ℝ) * J1 2 = J0 2 - J1 2 / 4)
  have eEY := (eY0.sub (eY1.const_mul (1 / 4))).congr (by push_cast; ring :
    Y0 2 - ((1 / 4 : ℚ) : ℝ) * Y1 2 = Y0 2 - Y1 2 / 4)
  have eP1d := (((eEJ.mul eKM).sub (eEY.mul eKP)).add eQ1).congr P1d_two.symm
  have eQ1d := (((eEY.mul eKM).add (eEJ.mul eKP)).sub eP1).congr Q1d_two.symm
  refine ⟨eP1.recenter ?_, eQ1.recenter ?_, eP1d.recenter ?_, eQ1d.recenter ?_⟩ <;>
    decide +kernel

/-- The energy root from enclosures of the four errors, order 0. -/
theorem root0_le_encl (κ x : ℝ) {p q p' q' : ℝ} {cp ep cq eq cp' ep' cq' eq' s : ℚ}
    (hp : Encl p cp ep) (hq : Encl q cq eq) (hp' : Encl p' cp' ep') (hq' : Encl q' cq' eq')
    (hm : 0 ≤ 1 + κ / x ^ 2) (hs : 0 ≤ s) (hs2 : 1 + κ / x ^ 2 ≤ (s : ℝ) ^ 2) :
    √(energy0 κ x p q p' q') ≤ ((qabs (cp' - cq) + (ep' + eq) + (qabs (cq' + cp) + (eq' + ep)) +
      s * (qabs cp + ep + (qabs cq + eq)) : ℚ) : ℝ) := by
  have h := energy0_shift κ x 0 0 0 0 p q p' q' s hm (by exact_mod_cast hs) hs2
  simp only [zero_add] at h
  have h0 : energy0 κ x 0 0 0 0 = 0 := by simp [energy0]
  rw [h0, Real.sqrt_zero, zero_add] at h
  refine h.trans ?_
  have a1 := (hp'.sub hq).abs_bound
  have a2 := (hq'.add hp).abs_bound
  have a3 := hp.abs_bound
  have a4 := hq.abs_bound
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast at a1 a2 a3 a4 ⊢
  have := mul_le_mul_of_nonneg_left (add_le_add a3 a4) hs'
  linarith

/-- The energy root from enclosures of the four errors, order 1. -/
theorem root1_le_encl (κ x : ℝ) {p q p' q' : ℝ} {cp ep cq eq cp' ep' cq' eq' s : ℚ}
    (hp : Encl p cp ep) (hq : Encl q cq eq) (hp' : Encl p' cp' ep') (hq' : Encl q' cq' eq')
    (hm : 0 < 1 + κ / x ^ 2) (hs : 0 ≤ s) (hs2 : 1 ≤ (1 + κ / x ^ 2) * (s : ℝ) ^ 2) :
    √(energy1 κ x p q p' q') ≤ ((s * (qabs (cp' - cq) + (ep' + eq) + (qabs (cq' + cp) + (eq' + ep))) +
      (qabs cp + ep + (qabs cq + eq)) : ℚ) : ℝ) := by
  have h := energy1_shift κ x 0 0 0 0 p q p' q' s hm (by exact_mod_cast hs) hs2
  simp only [zero_add] at h
  have h0 : energy1 κ x 0 0 0 0 = 0 := by simp [energy1]
  rw [h0, Real.sqrt_zero, zero_add] at h
  refine h.trans ?_
  have a1 := (hp'.sub hq).abs_bound
  have a2 := (hq'.add hp).abs_bound
  have a3 := hp.abs_bound
  have a4 := hq.abs_bound
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast at a1 a2 a3 a4 ⊢
  have := mul_le_mul_of_nonneg_left (add_le_add a1 a2) hs'
  linarith

#print axioms start_values0
#print axioms start_values1
#print axioms root0_le_encl
#print axioms root1_le_encl

end LeanExe.ProofKit.BesselStart
