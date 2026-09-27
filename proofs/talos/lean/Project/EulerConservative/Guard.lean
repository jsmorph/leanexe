import Project.EulerConservative.Model
import Project.EulerRusanov.RealConservative

namespace Project.EulerConservative.Guard
open Project.ProofKit.F64Order
open Project.EulerRusanov.RealConservative

/-- A sufficient domain, deliberately narrower than all admissible Euler states. -/
structure StateBounds (rho momentum energy : UInt64) : Prop where
  densityFinite : CodeLib.IEEE64.Finite rho
  momentumFinite : CodeLib.IEEE64.Finite momentum
  energyFinite : CodeLib.IEEE64.Finite energy
  densityPositive : 0 < CodeLib.IEEE64.value rho
  momentumMagnitude : |CodeLib.IEEE64.value momentum| ≤ CodeLib.IEEE64.value rho
  energyLower : CodeLib.IEEE64.value rho ≤ CodeLib.IEEE64.value energy

theorem stateGuard_spec (rho momentum energy : UInt64)
    (hguard : Model.stateGuard rho momentum energy = true) :
    StateBounds rho momentum energy := by
  obtain ⟨h1234, hreBool⟩ := Bool.and_eq_true_iff.mp hguard
  obtain ⟨h123, hmrBool⟩ := Bool.and_eq_true_iff.mp h1234
  obtain ⟨h12, he⟩ := Bool.and_eq_true_iff.mp h123
  obtain ⟨hr, hm⟩ := Bool.and_eq_true_iff.mp h12
  have hmr : absBits momentum ≤ rho := of_decide_eq_true hmrBool
  have hre : rho ≤ energy := of_decide_eq_true hreBool
  have hrf := positiveBits_spec rho hr
  have hef := positiveBits_spec energy he
  have hmag := abs_value_mono momentum rho (by
    simpa only [absBits_of_positive rho hr] using hmr)
  have henergy := abs_value_mono rho energy (by
    simpa only [absBits_of_positive rho hr, absBits_of_positive energy he] using hre)
  rw [abs_of_pos hrf.2] at hmag
  rw [abs_of_pos hrf.2, abs_of_pos hef.2] at henergy
  exact ⟨hrf.1, (finiteBits_iff momentum).mp hm, hef.1, hrf.2, hmag, henergy⟩

noncomputable def decodedState (rho momentum energy : UInt64) : Vec3 :=
  ![CodeLib.IEEE64.value rho, CodeLib.IEEE64.value momentum, CodeLib.IEEE64.value energy]

/-- The exact physical internal energy has a strictly positive density margin.
This states a property of decoded conservative words; it is not a rounding bound. -/
theorem internalEnergy_lower (rho momentum energy : UInt64)
    (h : StateBounds rho momentum energy) :
    CodeLib.IEEE64.value rho / 2 ≤ internalEnergy (decodedState rho momentum energy) := by
  let r := CodeLib.IEEE64.value rho
  let m := CodeLib.IEEE64.value momentum
  let e := CodeLib.IEEE64.value energy
  have hr : 0 < r := h.densityPositive
  have hm : |m| ≤ r := h.momentumMagnitude
  have he : r ≤ e := h.energyLower
  have hb := abs_le.mp hm
  have hsquare : m ^ 2 ≤ r ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hb.2) (by linarith : 0 ≤ r + m)
    nlinarith
  have hkinetic : m ^ 2 / (2 * r) ≤ r / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    nlinarith
  change r / 2 ≤ e - m ^ 2 / (2 * r)
  linarith

theorem stateGuard_admissible (rho momentum energy : UInt64)
    (hguard : Model.stateGuard rho momentum energy = true) :
    Admissible (decodedState rho momentum energy) := by
  have hb := stateGuard_spec rho momentum energy hguard
  refine ⟨hb.densityPositive, ?_⟩
  apply (pressure_pos_iff_internalEnergy_pos _).mpr
  have hlo := internalEnergy_lower rho momentum energy hb
  linarith [hb.densityPositive]

#print axioms stateGuard_spec
#print axioms internalEnergy_lower
#print axioms stateGuard_admissible
end Project.EulerConservative.Guard
