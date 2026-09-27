import Project.Euler2DConservative.Model
import Project.EulerRusanov.RealConservative

namespace Project.Euler2DConservative.Guard
open Project.ProofKit.F64Order

structure NarrowStateBounds (rho momentum transverse energy : UInt64) : Prop where
  densityFinite : CodeLib.IEEE64.Finite rho
  momentumFinite : CodeLib.IEEE64.Finite momentum
  transverseFinite : CodeLib.IEEE64.Finite transverse
  energyFinite : CodeLib.IEEE64.Finite energy
  densityPositive : 0 < CodeLib.IEEE64.value rho
  momentumMagnitude : |CodeLib.IEEE64.value momentum| ≤ CodeLib.IEEE64.value rho
  transverseMagnitude : |CodeLib.IEEE64.value transverse| ≤ CodeLib.IEEE64.value rho
  energyLower : CodeLib.IEEE64.value rho < CodeLib.IEEE64.value energy

theorem narrowStateGuard_spec (rho momentum transverse energy : UInt64)
    (hguard : Model.narrowStateGuard rho momentum transverse energy = true) :
    NarrowStateBounds rho momentum transverse energy := by
  simp only [Model.narrowStateGuard, Bool.and_eq_true_iff, decide_eq_true_eq] at hguard
  obtain ⟨⟨⟨⟨⟨⟨hr, hm⟩, ht⟩, he⟩, hmr⟩, htr⟩, hre⟩ := hguard
  change absBits momentum ≤ rho at hmr
  change absBits transverse ≤ rho at htr
  have hrf := positiveBits_spec rho hr
  have hef := positiveBits_spec energy he
  have hmag := abs_value_mono momentum rho (by
    simpa only [absBits_of_positive rho hr] using hmr)
  have htmag := abs_value_mono transverse rho (by
    simpa only [absBits_of_positive rho hr] using htr)
  have henergy := abs_value_lt rho energy (by
    simpa only [absBits_of_positive rho hr, absBits_of_positive energy he] using hre)
  rw [abs_of_pos hrf.2] at hmag htmag
  rw [abs_of_pos hrf.2, abs_of_pos hef.2] at henergy
  exact ⟨hrf.1, (finiteBits_iff momentum).mp hm, (finiteBits_iff transverse).mp ht,
    hef.1, hrf.2, hmag, htmag, henergy⟩

abbrev Vec4 := Fin 4 → ℝ
noncomputable def decodedState (rho momentum transverse energy : UInt64) : Vec4 :=
  ![CodeLib.IEEE64.value rho, CodeLib.IEEE64.value momentum,
    CodeLib.IEEE64.value transverse, CodeLib.IEEE64.value energy]

noncomputable def internalEnergy (q : Vec4) : ℝ := q 3 - ((q 1)^2 + (q 2)^2) / (2 * q 0)
noncomputable def pressure (q : Vec4) : ℝ := (2 / 5 : ℝ) * internalEnergy q
noncomputable def Admissible (q : Vec4) : Prop := 0 < q 0 ∧ 0 < pressure q

/-- Both kinetic-energy contributions are present in the exact-real margin. -/
theorem internalEnergy_lower (rho momentum transverse energy : UInt64)
    (h : NarrowStateBounds rho momentum transverse energy) :
    CodeLib.IEEE64.value energy - CodeLib.IEEE64.value rho ≤
      internalEnergy (decodedState rho momentum transverse energy) := by
  let r := CodeLib.IEEE64.value rho
  let m := CodeLib.IEEE64.value momentum
  let t := CodeLib.IEEE64.value transverse
  let e := CodeLib.IEEE64.value energy
  have hr : 0 < r := h.densityPositive
  have hsquare (v : ℝ) (hv : |v| ≤ r) : v^2 ≤ r^2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hv
    have hp := mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ r + v)
    nlinarith
  have hm := hsquare m h.momentumMagnitude
  have ht := hsquare t h.transverseMagnitude
  have hkinetic : (m^2+t^2)/(2*r) ≤ r := by
    apply (div_le_iff₀ (by positivity : 0 < 2*r)).mpr
    nlinarith
  change e-r ≤ e-(m^2+t^2)/(2*r)
  linarith

structure StateBounds (rho momentum transverse energy : UInt64) : Prop where
  densityFinite : CodeLib.IEEE64.Finite rho
  momentumFinite : CodeLib.IEEE64.Finite momentum
  transverseFinite : CodeLib.IEEE64.Finite transverse
  energyFinite : CodeLib.IEEE64.Finite energy
  densityPositive : 0 < CodeLib.IEEE64.value rho
  energyPositive : 0 < CodeLib.IEEE64.value energy
  internalPositive : 0 < internalEnergy (decodedState rho momentum transverse energy)

theorem stateGuard_spec (rho momentum transverse energy : UInt64)
    (hguard : Model.stateGuard rho momentum transverse energy = true) :
    StateBounds rho momentum transverse energy := by
  simp only [Model.stateGuard, Bool.or_eq_true] at hguard
  rcases hguard with hn | he
  · have hb := narrowStateGuard_spec rho momentum transverse energy hn
    have hlo := internalEnergy_lower rho momentum transverse energy hb
    exact ⟨hb.densityFinite, hb.momentumFinite, hb.transverseFinite, hb.energyFinite,
      hb.densityPositive, hb.densityPositive.trans hb.energyLower, by linarith [hb.energyLower]⟩
  · change Project.ProofKit.F64Admissibility.checked rho momentum transverse energy = true at he
    obtain ⟨hr, hm, ht, he, hrp, hep, hi⟩ :=
      Project.ProofKit.F64Admissibility.checked_sound rho momentum transverse energy he
    refine ⟨hr, hm, ht, he, hrp, hep, ?_⟩
    change 0 < CodeLib.IEEE64.value energy -
      ((CodeLib.IEEE64.value momentum)^2 + (CodeLib.IEEE64.value transverse)^2) /
        (2 * CodeLib.IEEE64.value rho)
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < 2 * CodeLib.IEEE64.value rho)).mpr
    nlinarith

theorem stateGuard_admissible (rho momentum transverse energy : UInt64)
    (hguard : Model.stateGuard rho momentum transverse energy = true) :
    Admissible (decodedState rho momentum transverse energy) := by
  have hb := stateGuard_spec rho momentum transverse energy hguard
  exact ⟨hb.densityPositive, mul_pos (by norm_num : (0 : ℝ) < 2 / 5) hb.internalPositive⟩

#print axioms narrowStateGuard_spec
#print axioms stateGuard_spec
#print axioms internalEnergy_lower
#print axioms stateGuard_admissible
end Project.Euler2DConservative.Guard
