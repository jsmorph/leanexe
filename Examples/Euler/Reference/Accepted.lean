import Examples.Euler.Reference.Interface
import Examples.Euler.ReconstructedSpec
import Examples.Euler.Balance
import Examples.Euler.Words
import LeanExe.ProofKit.F64RusanovResidual
import LeanExe.ProofKit.F64ErrorPropagation
import LeanExe.ProofKit.F64QuotientResidual

/-! Error bounds computed from the words of an accepted evaluation.  When `side` or `outwardSide`
accepts a state, each of its four fluxes is within `sideFluxErrorBound` of the exact flux
`Equations.xFlux` of the state's values.  When `flux` or `outwardFlux` accepts two states, each
of its four components is within a bound computed from the words of its arithmetic of the exact
Rusanov flux `Rusanov.interfaceFlux` of the two states' values with the computed speed.  The
bounds assume nothing about the states beyond acceptance. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit.F64Order
open LeanExe.ProofKit.F64RoundingResidual (radius div_error)

set_option exponentiation.threshold 4096

theorem rejectedSide_status {c : Prop} [Decidable c] {u : Side}
    (h : (if c then u else rejectedSide).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

theorem rejectedComponent_status {c : Prop} [Decidable c] {u : Component}
    (h : (if c then u else rejectedComponent).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

theorem rejectedFlux_status {c : Prop} [Decidable c] {u : Flux}
    (h : (if c then u else rejectedFlux).status = 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [ite_eq_right hc] at h
    simp at h

/-- A state that passes the state guard has finite components and positive density. -/
theorem stateGuard_inputs {rho mx my energy : Float} (h : stateGuard rho mx my energy = true) :
    Finite rho.toBits ∧ Finite mx.toBits ∧ Finite my.toBits ∧ Finite energy.toBits ∧
      0 < real rho := by
  have hpos := ((admissible_iff _ _ _ _).mp (stateGuard_admissible h)).1
  rcases Bool.or_eq_true_iff.mp h with hn | he
  · obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.mp hn
    obtain ⟨h2, -⟩ := Bool.and_eq_true_iff.mp h1
    obtain ⟨h3, -⟩ := Bool.and_eq_true_iff.mp h2
    obtain ⟨h4, he⟩ := Bool.and_eq_true_iff.mp h3
    obtain ⟨h5, hy⟩ := Bool.and_eq_true_iff.mp h4
    obtain ⟨hr, hx⟩ := Bool.and_eq_true_iff.mp h5
    exact ⟨(positiveBits_spec _ hr).1, finite_bits hx, finite_bits hy, (positiveBits_spec _ he).1,
      hpos⟩
  · obtain ⟨hr, hx, hy, he, -⟩ := F64Admissibility.checked_sound _ _ _ _ (energyGuard_checked he)
    exact ⟨hr, hx, hy, he, hpos⟩

/-! Side fluxes. -/

/-- The finiteness of the words that the flux arithmetic of `side` and `outwardSide` computes. -/
def SideFinite (rho mx my energy : UInt64) : Prop :=
  let u := Wasm.IEEE64.div mx rho
  let v := Wasm.IEEE64.div my rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my v
  let total := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 total
  let internal := Wasm.IEEE64.sub energy kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  Finite u ∧ Finite v ∧ Finite tx ∧ Finite ty ∧ Finite total ∧ Finite kinetic ∧ Finite internal ∧
    Finite pressure ∧ Finite (Wasm.IEEE64.add tx pressure) ∧ Finite (Wasm.IEEE64.mul my u) ∧
    Finite (Wasm.IEEE64.add energy pressure) ∧
    Finite (Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure))

structure SideErrorBounds where
  pressure : ℝ
  momentum : ℝ
  transverse : ℝ
  energy : ℝ

/-- The error bounds of the pressure and of the momentum, transverse, and energy fluxes, computed
from the rounding radii of the words of the flux arithmetic. -/
noncomputable def sideErrorBounds (rho mx my energy : UInt64) : SideErrorBounds :=
  let u := Wasm.IEEE64.div mx rho
  let v := Wasm.IEEE64.div my rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my v
  let total := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 total
  let internal := Wasm.IEEE64.sub energy kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let enthalpy := Wasm.IEEE64.add energy pressure
  let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  let txError := radius tx + |value mx| * radius u
  let tyError := radius ty + |value my| * radius v
  let sumError := radius total + (txError + tyError)
  let internalError := radius internal + (radius kinetic + (1 / 2) * sumError)
  let pressureError := radius pressure + (|value 0x3FD999999999999A| * internalError +
    |value 0x3FD999999999999A - 2 / 5| * |I|)
  ⟨pressureError,
    radius (Wasm.IEEE64.add tx pressure) + (txError + pressureError),
    radius (Wasm.IEEE64.mul my u) + |value my| * radius u,
    radius (Wasm.IEEE64.mul u enthalpy) +
      (|value u| * (radius enthalpy + pressureError) +
        radius u * |value energy + (2 / 5) * I|)⟩

/-- The error bounds of the four side fluxes of a state: the mass flux is exact. -/
noncomputable def sideFluxErrorBound (rho mx my energy : Float) : Fin 4 → ℝ :=
  let bound := sideErrorBounds rho.toBits mx.toBits my.toBits energy.toBits
  ![0, bound.momentum, bound.transverse, bound.energy]

theorem side_reference_words (rho mx my energy : UInt64) (hrho : Finite rho) (hmx : Finite mx)
    (hmy : Finite my) (henergy : Finite energy) (hpos : 0 < value rho)
    (finite : SideFinite rho mx my energy) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let internal :=
      Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let bound := sideErrorBounds rho mx my energy
    |value pressure - (2 / 5) * I| ≤ bound.pressure ∧
    |value (Wasm.IEEE64.add tx pressure) - ((value mx)^2 / value rho + (2 / 5) * I)| ≤
      bound.momentum ∧
    |value (Wasm.IEEE64.mul my u) - value mx * value my / value rho| ≤ bound.transverse ∧
    |value (Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure)) -
      (value energy + (2 / 5) * I) * (value mx / value rho)| ≤ bound.energy := by
  obtain ⟨hu, hv, htx, hty, htotal, hkinetic, hi, hp, hnormal, htransverse, henthalpy, heflux⟩ :=
    finite
  have hr0 : Wasm.IEEE64.scaledMagnitude rho ≠ 0 := by
    intro hz
    have hzValue : value rho = 0 := by
      simp [value, Wasm.IEEE64.scaledValue, hz]
    linarith
  have halfFinite : Finite 0x3FE0000000000000 := by
    unfold CodeLib.IEEE64.Finite
    decide
  have halfValue : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have coefficientFinite : Finite 0x3FD999999999999A := by
    unfold CodeLib.IEEE64.Finite
    decide
  have eu := div_error mx rho hmx hrho hr0 hu
  have ev := div_error my rho hmy hrho hr0 hv
  have etx := F64ErrorPropagation.mul mx _ (value mx) _ 0 _ hmx hu htx (by simp) eu
  have ety := F64ErrorPropagation.mul my _ (value my) _ 0 _ hmy hv hty (by simp) ev
  simp only [zero_mul, add_zero] at etx ety
  have esum := F64ErrorPropagation.add _ _ _ _ _ _ htx hty htotal etx ety
  have ek := F64ErrorPropagation.mul 0x3FE0000000000000 _ (1 / 2) _ 0 _
    halfFinite htotal hkinetic (by rw [halfValue]; simp) esum
  simp only [halfValue, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), zero_mul, add_zero] at ek
  have ei := F64ErrorPropagation.sub energy _ (value energy) _ 0 _ henergy hkinetic hi (by simp) ek
  simp only [zero_add] at ei
  have internalIdentity : value energy - (1 / 2) *
      (value mx * (value mx / value rho) + value my * (value my / value rho)) =
      value energy - ((value mx)^2 + (value my)^2) / (2 * value rho) := by
    field_simp [ne_of_gt hpos]
  rw [internalIdentity] at ei
  have ep := F64ErrorPropagation.mul 0x3FD999999999999A _ (2 / 5) _ _ _
    coefficientFinite hi hp le_rfl ei
  have en := F64ErrorPropagation.add _ _ _ _ _ _ htx hp hnormal etx ep
  have et := F64ErrorPropagation.mul my _ (value my) _ 0 _ hmy hu htransverse (by simp) eu
  simp only [zero_mul, add_zero] at et
  have eh := F64ErrorPropagation.add energy _ (value energy) _ 0 _ henergy hp henthalpy (by simp) ep
  simp only [zero_add] at eh
  have ee := F64ErrorPropagation.mul _ _ _ _ _ _ hu henthalpy heflux eu eh
  dsimp only
  refine ⟨ep, ?_, ?_, ?_⟩
  · convert en using 1 <;> first | rfl | ring_nf
  · convert et using 1 <;> first | rfl | ring_nf
  · convert ee using 1 <;> first | rfl | ring_nf

/-- The four fluxes that `side` and `outwardSide` compute. -/
def fluxValues (rho mx my energy : Float) : Fin 4 → Float :=
  let velocity := mx / rho
  let pressure := 0.4 * (energy - 0.5 * (mx * velocity + my * (my / rho)))
  ![mx, mx * velocity + pressure, my * velocity, velocity * (energy + pressure)]

/-- For a state that passes the state guard and whose flux arithmetic stays finite, each flux is
within its bound of the exact flux. -/
theorem fluxValues_error {rho mx my energy : Float} (hg : stateGuard rho mx my energy = true)
    (hf : SideFinite rho.toBits mx.toBits my.toBits energy.toBits) (i : Fin 4) :
    |real (fluxValues rho mx my energy i) - Equations.xFlux (vec ⟨rho, mx, my, energy⟩) i| ≤
      sideFluxErrorBound rho mx my energy i := by
  obtain ⟨hrho, hmx, hmy, henergy, hr⟩ := stateGuard_inputs hg
  obtain ⟨-, hn, ht, he⟩ :=
    side_reference_words rho.toBits mx.toBits my.toBits energy.toBits hrho hmx hmy henergy hr hf
  have hx1 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 1 = (real mx)^2 / real rho +
      (2 / 5) * (real energy - ((real mx)^2 + (real my)^2) / (2 * real rho)) := by
    simp [Equations.xFlux, vec, Equations.velocity, Equations.pressure, Equations.internalEnergy]
    field_simp
  have hx2 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 2 = real mx * real my / real rho := by
    simp [Equations.xFlux, vec, Equations.velocity]
    field_simp
  have hx3 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 3 = (real energy + (2 / 5) *
      (real energy - ((real mx)^2 + (real my)^2) / (2 * real rho))) * (real mx / real rho) := by
    simp [Equations.xFlux, vec, Equations.velocity, Equations.pressure, Equations.internalEnergy]
  fin_cases i
  · show |real mx - Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 0| ≤ 0
    simp [Equations.xFlux, vec]
  · show |real (mx * (mx / rho) + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho)))) -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 1| ≤
        (sideErrorBounds rho.toBits mx.toBits my.toBits energy.toBits).momentum
    simp only [real, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub,
      F64Bits.toBits_div, half_toBits, twoFifths_toBits]
    rw [hx1]
    exact hn
  · show |real (my * (mx / rho)) - Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 2| ≤
        (sideErrorBounds rho.toBits mx.toBits my.toBits energy.toBits).transverse
    simp only [real, F64Bits.toBits_mul, F64Bits.toBits_div]
    rw [hx2]
    exact ht
  · show |real (mx / rho * (energy + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))))) -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 3| ≤
        (sideErrorBounds rho.toBits mx.toBits my.toBits energy.toBits).energy
    simp only [real, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub,
      F64Bits.toBits_div, half_toBits, twoFifths_toBits]
    rw [hx3]
    exact he

/-- When `side` accepts a state, the state passes the guard, its flux arithmetic stays finite, and
its fluxes are `fluxValues`. -/
theorem side_accepted {rho mx my energy : Float} (h : (side rho mx my energy).status = 0) :
    stateGuard rho mx my energy = true ∧ SideFinite rho.toBits mx.toBits my.toBits energy.toBits ∧
      ∀ i, sideComponents (side rho mx my energy) i = fluxValues rho mx my energy i := by
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  unfold side at h ⊢
  dsimp only at h ⊢
  have hc := rejectedSide_status h
  rw [ite_eq_left hc]
  simp only [hBits, positive_eq, Bool.and_eq_true, and_assoc, finiteBits_iff, F64Bits.toBits_add,
    F64Bits.toBits_mul, F64Bits.toBits_sub, F64Bits.toBits_div, half_toBits,
    twoFifths_toBits] at hc
  obtain ⟨hg, hu, htx, hv, hty, hsum, hk, hi, hp, -, -, -, -, hn, ht, he, hef⟩ := hc
  exact ⟨hg, ⟨hu, hv, htx, hty, hsum, hk, (positiveBits_spec _ hi).1, (positiveBits_spec _ hp).1,
    hn, ht, he, hef⟩, fun i => by fin_cases i <;> rfl⟩

/-- When `outwardSide` accepts a state, the state passes the guard, its flux arithmetic stays
finite, and its fluxes are `fluxValues`. -/
theorem outwardSide_accepted {rho mx my energy : Float}
    (h : (outwardSide rho mx my energy).status = 0) :
    stateGuard rho mx my energy = true ∧ SideFinite rho.toBits mx.toBits my.toBits energy.toBits ∧
      ∀ i, sideComponents (outwardSide rho mx my energy) i = fluxValues rho mx my energy i := by
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  have hg := outwardSide_guard h
  unfold outwardSide at h ⊢
  dsimp only at h ⊢
  have hc := rejectedSide_status h
  rw [ite_eq_left hc]
  simp only [hBits, positive_eq, Bool.and_eq_true, and_assoc, beq_iff_eq, finiteBits_iff,
    F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub, F64Bits.toBits_div, half_toBits,
    twoFifths_toBits] at hc
  obtain ⟨-, hu, htx, hv, hty, hsum, hk, hi, hp, hn, ht, he, hef⟩ := hc
  exact ⟨hg, ⟨hu, hv, htx, hty, hsum, hk, (positiveBits_spec _ hi).1, (positiveBits_spec _ hp).1,
    hn, ht, he, hef⟩, fun i => by fin_cases i <;> rfl⟩

theorem side_flux_residual {rho mx my energy : Float} (h : (side rho mx my energy).status = 0)
    (i : Fin 4) :
    |real (sideComponents (side rho mx my energy) i) -
      Equations.xFlux (vec ⟨rho, mx, my, energy⟩) i| ≤ sideFluxErrorBound rho mx my energy i := by
  obtain ⟨hg, hf, hv⟩ := side_accepted h
  rw [hv i]
  exact fluxValues_error hg hf i

theorem outwardSide_flux_residual {rho mx my energy : Float}
    (h : (outwardSide rho mx my energy).status = 0) (i : Fin 4) :
    |real (sideComponents (outwardSide rho mx my energy) i) -
      Equations.xFlux (vec ⟨rho, mx, my, energy⟩) i| ≤ sideFluxErrorBound rho mx my energy i := by
  obtain ⟨hg, hf, hv⟩ := outwardSide_accepted h
  rw [hv i]
  exact fluxValues_error hg hf i

/-! Flux components. -/

/-- An accepted component has a positive speed and the rounding certificate of its arithmetic. -/
theorem component_accepted {alpha fluxL fluxR stateL stateR : Float}
    (h : (component alpha fluxL fluxR stateL stateR).status = 0) :
    0 < real alpha ∧ F64RusanovResidual.Certificate 0x3FE0000000000000 alpha.toBits
      fluxL.toBits fluxR.toBits stateL.toBits stateR.toBits
      (component alpha fluxL fluxR stateL stateR).value.toBits := by
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  unfold component at h ⊢
  dsimp only at h ⊢
  have hc := rejectedComponent_status h
  rw [ite_eq_left hc]
  simp only [hBits, positive_eq, Bool.and_eq_true, and_assoc, finiteBits_iff, F64Bits.toBits_add,
    F64Bits.toBits_mul, F64Bits.toBits_sub, half_toBits] at hc
  obtain ⟨ha, hfl, hfr, hsl, hsr, hsum, hmean, hjump, hvisc, hhalf, hresult⟩ := hc
  have hpa := positiveBits_spec _ ha
  simp only [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_sub, half_toBits]
  exact ⟨hpa.2, F64RusanovResidual.rounded_component _ _ _ _ _ _
    (by unfold CodeLib.IEEE64.Finite; decide) hpa.1 hfl hfr hsl hsr hsum hmean hjump hvisc hhalf
    hresult⟩

/-- The error bound of a component, computed from the words of its arithmetic. -/
noncomputable def componentErrorBound (alpha fluxL fluxR stateL stateR : Float) : ℝ :=
  F64RusanovResidual.errorBound 0x3FE0000000000000 alpha.toBits fluxL.toBits fluxR.toBits
    stateL.toBits stateR.toBits (component alpha fluxL fluxR stateL stateR).value.toBits

/-- An accepted component against the Rusanov formula with reference side fluxes `FL` and `FR`
within `eL` and `eR` of its input fluxes. -/
theorem component_reference_residual {alpha fluxL fluxR stateL stateR : Float} {FL FR eL eR : ℝ}
    (h : (component alpha fluxL fluxR stateL stateR).status = 0)
    (hL : |real fluxL - FL| ≤ eL) (hR : |real fluxR - FR| ≤ eR) :
    |real (component alpha fluxL fluxR stateL stateR).value -
      ((FL + FR) / 2 - real alpha * (real stateR - real stateL) / 2)| ≤
      componentErrorBound alpha fluxL fluxR stateL stateR + (eL + eR) / 2 := by
  obtain ⟨ha, hcert⟩ := component_accepted h
  have hv : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have hc := F64RusanovResidual.residual_bound (by rw [hv]; norm_num) ha.le hcert
  unfold F64RusanovResidual.residual at hc
  rw [hv] at hc
  obtain ⟨hl1, hl2⟩ := abs_le.mp hL
  obtain ⟨hr1, hr2⟩ := abs_le.mp hR
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  unfold componentErrorBound
  simp only [real] at hl1 hl2 hr1 hr2 ⊢
  apply abs_le.mpr
  constructor <;> linarith

/-! Interface fluxes. -/

/-- When `flux` accepts two states, both sides and every component accept, and the components
are those of `flux`. -/
theorem flux_parts {rhoL mxL myL energyL rhoR mxR myR energyR : Float}
    (h : (flux rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) :
    (side rhoL mxL myL energyL).status = 0 ∧ (side rhoR mxR myR energyR).status = 0 ∧ ∀ i,
      let f := flux rhoL mxL myL energyL rhoR mxR myR energyR
      let c := component f.alpha (sideComponents (side rhoL mxL myL energyL) i)
        (sideComponents (side rhoR mxR myR energyR) i) (stateAt ⟨rhoL, mxL, myL, energyL⟩ i)
        (stateAt ⟨rhoR, mxR, myR, energyR⟩ i)
      c.status = 0 ∧ fluxAt f i = c.value := by
  unfold flux at h ⊢
  dsimp only at h ⊢
  have hc := rejectedFlux_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hc
  obtain ⟨hl, hr, h0, h1, h2, h3⟩ := hc
  refine ⟨hl, hr, fun i => ?_⟩
  fin_cases i
  exacts [⟨h0, rfl⟩, ⟨h1, rfl⟩, ⟨h2, rfl⟩, ⟨h3, rfl⟩]

/-- When `outwardFlux` accepts two states, both sides and every component accept, and the
components are those of `outwardFlux`. -/
theorem outwardFlux_parts {rhoL mxL myL energyL rhoR mxR myR energyR : Float}
    (h : (outwardFlux rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) :
    (outwardSide rhoL mxL myL energyL).status = 0 ∧
      (outwardSide rhoR mxR myR energyR).status = 0 ∧ ∀ i,
      let f := outwardFlux rhoL mxL myL energyL rhoR mxR myR energyR
      let c := component f.alpha (sideComponents (outwardSide rhoL mxL myL energyL) i)
        (sideComponents (outwardSide rhoR mxR myR energyR) i)
        (stateAt ⟨rhoL, mxL, myL, energyL⟩ i) (stateAt ⟨rhoR, mxR, myR, energyR⟩ i)
      c.status = 0 ∧ fluxAt f i = c.value := by
  unfold outwardFlux at h ⊢
  dsimp only at h ⊢
  have hc := rejectedFlux_status h
  rw [ite_eq_left hc]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hc
  obtain ⟨hl, hr, h0, h1, h2, h3⟩ := hc
  refine ⟨hl, hr, fun i => ?_⟩
  fin_cases i
  exacts [⟨h0, rfl⟩, ⟨h1, rfl⟩, ⟨h2, rfl⟩, ⟨h3, rfl⟩]

/-- The error bound of component `i` of `flux`, computed from the words of its arithmetic. -/
noncomputable def fluxErrorBound (rhoL mxL myL energyL rhoR mxR myR energyR : Float)
    (i : Fin 4) : ℝ :=
  componentErrorBound (flux rhoL mxL myL energyL rhoR mxR myR energyR).alpha
      (sideComponents (side rhoL mxL myL energyL) i) (sideComponents (side rhoR mxR myR energyR) i)
      (stateAt ⟨rhoL, mxL, myL, energyL⟩ i) (stateAt ⟨rhoR, mxR, myR, energyR⟩ i) +
    (sideFluxErrorBound rhoL mxL myL energyL i + sideFluxErrorBound rhoR mxR myR energyR i) / 2

/-- The error bound of component `i` of `outwardFlux`, computed from the words of its
arithmetic. -/
noncomputable def outwardFluxErrorBound (rhoL mxL myL energyL rhoR mxR myR energyR : Float)
    (i : Fin 4) : ℝ :=
  componentErrorBound (outwardFlux rhoL mxL myL energyL rhoR mxR myR energyR).alpha
      (sideComponents (outwardSide rhoL mxL myL energyL) i)
      (sideComponents (outwardSide rhoR mxR myR energyR) i)
      (stateAt ⟨rhoL, mxL, myL, energyL⟩ i) (stateAt ⟨rhoR, mxR, myR, energyR⟩ i) +
    (sideFluxErrorBound rhoL mxL myL energyL i + sideFluxErrorBound rhoR mxR myR energyR i) / 2

/-- When `flux` accepts two states, each of its components is within `fluxErrorBound` of the
exact Rusanov flux of the two states' values with the computed speed. -/
theorem flux_reference_residual {rhoL mxL myL energyL rhoR mxR myR energyR : Float}
    (h : (flux rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    let f := flux rhoL mxL myL energyL rhoR mxR myR energyR
    |real (fluxAt f i) - Equations.Rusanov.interfaceFlux (real f.alpha)
      (vec ⟨rhoL, mxL, myL, energyL⟩) (vec ⟨rhoR, mxR, myR, energyR⟩) i| ≤
      fluxErrorBound rhoL mxL myL energyL rhoR mxR myR energyR i := by
  obtain ⟨hl, hr, hc⟩ := flux_parts h
  obtain ⟨hci, hv⟩ := hc i
  have e := component_reference_residual hci (side_flux_residual hl i) (side_flux_residual hr i)
  dsimp only
  rw [hv]
  simpa only [real_stateAt, Equations.Rusanov.interfaceFlux, fluxErrorBound] using e

/-- When `outwardFlux` accepts two states, each of its components is within
`outwardFluxErrorBound` of the exact Rusanov flux of the two states' values with the computed
speed. -/
theorem outwardFlux_reference_residual {rhoL mxL myL energyL rhoR mxR myR energyR : Float}
    (h : (outwardFlux rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    let f := outwardFlux rhoL mxL myL energyL rhoR mxR myR energyR
    |real (fluxAt f i) - Equations.Rusanov.interfaceFlux (real f.alpha)
      (vec ⟨rhoL, mxL, myL, energyL⟩) (vec ⟨rhoR, mxR, myR, energyR⟩) i| ≤
      outwardFluxErrorBound rhoL mxL myL energyL rhoR mxR myR energyR i := by
  obtain ⟨hl, hr, hc⟩ := outwardFlux_parts h
  obtain ⟨hci, hv⟩ := hc i
  have e := component_reference_residual hci (outwardSide_flux_residual hl i)
    (outwardSide_flux_residual hr i)
  dsimp only
  rw [hv]
  simpa only [real_stateAt, Equations.Rusanov.interfaceFlux, outwardFluxErrorBound]
    using e

end Examples.Euler.Reference
