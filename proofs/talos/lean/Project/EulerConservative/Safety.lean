import Project.EulerConservative.Guard

namespace Project.EulerConservative.Safety
open Project.ProofKit.F64Order

/-- The twelve rounded intermediates, in source evaluation order. -/
def intermediateWords (rho momentum energy : UInt64) : List UInt64 :=
  let velocity := Wasm.IEEE64.div momentum rho
  let transport := Wasm.IEEE64.mul momentum velocity
  let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 transport
  let internal := Wasm.IEEE64.sub energy halfKinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let pressureOverDensity := Wasm.IEEE64.div pressure rho
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 pressureOverDensity
  let soundSpeed := Wasm.IEEE64.sqrt radicand
  let speed := Wasm.IEEE64.add (Model.absBits velocity) soundSpeed
  let momentumFlux := Wasm.IEEE64.add transport pressure
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul velocity enthalpy
  [velocity, transport, halfKinetic, internal, pressure, pressureOverDensity,
    radicand, soundSpeed, speed, momentumFlux, enthalpy, energyFlux]

private theorem finite_of_guard {word : UInt64} (h : Model.finiteBits word = true) :
    CodeLib.IEEE64.Finite word := (finiteBits_iff word).mp h

private theorem finite_of_positive {word : UInt64} (h : Model.positiveBits word = true) :
    CodeLib.IEEE64.Finite word := (positiveBits_spec word h).1

/-- Acceptance entails the input guard; no numerical-operation premise is assumed. -/
theorem accepted_inputGuard (rho momentum energy : UInt64)
    (h : (Model.sideCheckedBits rho momentum energy).status = 0) :
    Model.stateGuard rho momentum energy = true := by
  unfold Model.sideCheckedBits at h
  split at h
  · assumption
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

/-- Every rounded intermediate in an accepted side is finite. -/
theorem accepted_intermediates_finite (rho momentum energy : UInt64)
    (h : (Model.sideCheckedBits rho momentum energy).status = 0) :
    ∀ word ∈ intermediateWords rho momentum energy, CodeLib.IEEE64.Finite word := by
  unfold Model.sideCheckedBits at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hfirst
      split at h
      · rename_i hsecond
        split at h
        · rename_i hthird
          obtain ⟨hfirst3, hi⟩ := Bool.and_eq_true_iff.mp hfirst
          obtain ⟨hfirst2, hk⟩ := Bool.and_eq_true_iff.mp hfirst3
          obtain ⟨hu, ht⟩ := Bool.and_eq_true_iff.mp hfirst2
          obtain ⟨hsecond2, hr⟩ := Bool.and_eq_true_iff.mp hsecond
          obtain ⟨hp, hpr⟩ := Bool.and_eq_true_iff.mp hsecond2
          obtain ⟨hthird4, heFlux⟩ := Bool.and_eq_true_iff.mp hthird
          obtain ⟨hthird3, he⟩ := Bool.and_eq_true_iff.mp hthird4
          obtain ⟨hthird2, hmFlux⟩ := Bool.and_eq_true_iff.mp hthird3
          obtain ⟨hc, hs⟩ := Bool.and_eq_true_iff.mp hthird2
          simp only [intermediateWords, List.forall_mem_cons]
          exact ⟨finite_of_guard hu, finite_of_guard ht, finite_of_guard hk,
            finite_of_positive hi, finite_of_positive hp, finite_of_positive hpr,
            finite_of_positive hr, finite_of_positive hc, finite_of_positive hs,
            finite_of_guard hmFlux, finite_of_guard he, finite_of_guard heFlux,
            List.forall_mem_nil _⟩
        · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
      · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

/-- An accepted side starts from a physically admissible conservative state. -/
theorem accepted_admissible (rho momentum energy : UInt64)
    (h : (Model.sideCheckedBits rho momentum energy).status = 0) :
    Project.EulerRusanov.RealConservative.Admissible
      (Guard.decodedState rho momentum energy) :=
  Guard.stateGuard_admissible rho momentum energy (accepted_inputGuard rho momentum energy h)

#print axioms accepted_inputGuard
#print axioms accepted_intermediates_finite
#print axioms accepted_admissible
end Project.EulerConservative.Safety
