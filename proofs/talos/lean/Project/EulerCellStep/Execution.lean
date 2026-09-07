import Project.EulerCellStep.Update

namespace Project.EulerCellStep.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64) : List Wasm.Value :=
  let out := Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy, .i64 out.momentum, .i64 out.density, .i64 out.status]

theorem cellCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64) :
    TerminatesWith env m 25 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 momentum, .i64 rho, .i64 energyL, .i64 momentumL, .i64 rhoL, .i64 ratio]
      (fun final values => final = initial ∧ values = resultValues ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR) := by
  let left := Project.EulerDynamicFlux.Model.fluxCheckedBits rhoL momentumL energyL rho momentum energy
  let right := Project.EulerDynamicFlux.Model.fluxCheckedBits rho momentum energy rhoR momentumR energyR
  have leftCall := Project.EulerDynamicFlux.Execution.fluxCheckedBits_exact_in_module
    layout.toLayout env initial rhoL momentumL energyL rho momentum energy
  change TerminatesWith env m 16 initial [.i64 energy, .i64 momentum, .i64 rho, .i64 energyL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.alpha, .i64 left.energy, .i64 left.momentum, .i64 left.mass, .i64 left.status]) at leftCall
  have rightCall := Project.EulerDynamicFlux.Execution.fluxCheckedBits_exact_in_module
    layout.toLayout env initial rho momentum energy rhoR momentumR energyR
  change TerminatesWith env m 16 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 momentum, .i64 rho]
    (fun final values => final = initial ∧ values = [.i64 right.alpha, .i64 right.energy, .i64 right.momentum, .i64 right.mass, .i64 right.status]) at rightCall
  let nextDensity := Model.updateCheckedBits ratio rho left.mass right.mass
  have nextDensityCall := updateCheckedBits_exact_in_module layout env initial ratio rho left.mass right.mass
  change TerminatesWith env m 19 initial [.i64 right.mass, .i64 left.mass, .i64 rho, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextDensity.value, .i64 nextDensity.status]) at nextDensityCall
  let nextMomentum := Model.updateCheckedBits ratio momentum left.momentum right.momentum
  have nextMomentumCall := updateCheckedBits_exact_in_module layout env initial ratio momentum left.momentum right.momentum
  change TerminatesWith env m 19 initial [.i64 right.momentum, .i64 left.momentum, .i64 momentum, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextMomentum.value, .i64 nextMomentum.status]) at nextMomentumCall
  let nextEnergy := Model.updateCheckedBits ratio energy left.energy right.energy
  have nextEnergyCall := updateCheckedBits_exact_in_module layout env initial ratio energy left.energy right.energy
  change TerminatesWith env m 19 initial [.i64 right.energy, .i64 left.energy, .i64 energy, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextEnergy.value, .i64 nextEnergy.status]) at nextEnergyCall
  let nextSide := Project.EulerConservative.Model.sideCheckedBits nextDensity.value nextMomentum.value nextEnergy.value
  have nextSideCall := Project.EulerConservative.Execution.sideCheckedBits_exact_in_module
    layout.toLayout.toHelperLayout layout.side env initial nextDensity.value nextMomentum.value nextEnergy.value
  change TerminatesWith env m 5 initial [.i64 nextEnergy.value, .i64 nextMomentum.value, .i64 nextDensity.value]
    (fun final values => final = initial ∧ values = [.i64 nextSide.energyFlux, .i64 nextSide.momentumFlux, .i64 nextSide.massFlux, .i64 nextSide.speed, .i64 nextSide.pressure, .i64 nextSide.velocity, .i64 nextSide.status]) at nextSideCall
  refine TerminatesWith.of_wp_entry_for (f := func25Def)
    (by simpa [layout.noImports] using layout.cell) ?_ (by simp [layout.noImports])
  change wp m func25 _ initial (func25Def.toLocals [.i64 ratio, .i64 rhoL, .i64 momentumL, .i64 energyL, .i64 rho, .i64 momentum, .i64 energy, .i64 rhoR, .i64 momentumR, .i64 energyR]) env
  unfold func25
  wp_run [func25Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (Project.EulerConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial ratio) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hp : Project.EulerConservative.Model.positiveBits ratio
  · dynamic_peel
    refine wp_call_tw (rejectedCell_exact layout env initial) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, *]
  · dynamic_peel
    refine wp_call_tw (leftCall) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    by_cases hl : left.status = 0
    · dynamic_peel
      refine wp_call_tw (rightCall) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      by_cases hr : right.status = 0
      · dynamic_peel
        by_cases hspeed : left.alpha ≤ right.alpha
        · dynamic_peel
          let courant := Wasm.IEEE64.mul ratio right.alpha
          refine wp_call_tw (Project.EulerConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial courant) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          cases hc : Project.EulerConservative.Model.positiveBits courant
          · dynamic_peel
            refine wp_call_tw (rejectedCell_exact layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, courant, *]
          · by_cases hceiling : Wasm.IEEE64.mul ratio right.alpha ≤ 0x3FE0000000000000
            · dynamic_peel
              refine wp_call_tw (nextDensityCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              refine wp_call_tw (nextMomentumCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              refine wp_call_tw (nextEnergyCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              by_cases hu0 : nextDensity.status = 0
              · dynamic_peel
                by_cases hu1 : nextMomentum.status = 0
                · dynamic_peel
                  by_cases hu2 : nextEnergy.status = 0
                  · dynamic_peel
                    refine wp_call_tw (nextSideCall) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    by_cases hs : nextSide.status = 0
                    · dynamic_peel
                      simp [resultValues, Model.cellCheckedBits, left, right, nextDensity, nextMomentum, nextEnergy, nextSide, courant, *]
                    · dynamic_peel
                      refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      dynamic_peel
                      simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, nextEnergy, nextSide, courant, *]
                  · dynamic_peel
                    refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    dynamic_peel
                    simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, nextEnergy, courant, *]
                · dynamic_peel
                  refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  dynamic_peel
                  simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, courant, *]
              · dynamic_peel
                refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                dynamic_peel
                simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, courant, *]
            · dynamic_peel
              refine wp_call_tw (rejectedCell_exact layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, courant, *]
        · dynamic_peel
          let courant := Wasm.IEEE64.mul ratio left.alpha
          refine wp_call_tw (Project.EulerConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial courant) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          cases hc : Project.EulerConservative.Model.positiveBits courant
          · dynamic_peel
            refine wp_call_tw (rejectedCell_exact layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, courant, *]
          · by_cases hceiling : Wasm.IEEE64.mul ratio left.alpha ≤ 0x3FE0000000000000
            · dynamic_peel
              refine wp_call_tw (nextDensityCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              refine wp_call_tw (nextMomentumCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              refine wp_call_tw (nextEnergyCall) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              by_cases hu0 : nextDensity.status = 0
              · dynamic_peel
                by_cases hu1 : nextMomentum.status = 0
                · dynamic_peel
                  by_cases hu2 : nextEnergy.status = 0
                  · dynamic_peel
                    refine wp_call_tw (nextSideCall) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    by_cases hs : nextSide.status = 0
                    · dynamic_peel
                      simp [resultValues, Model.cellCheckedBits, left, right, nextDensity, nextMomentum, nextEnergy, nextSide, courant, *]
                    · dynamic_peel
                      refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      dynamic_peel
                      simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, nextEnergy, nextSide, courant, *]
                  · dynamic_peel
                    refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    dynamic_peel
                    simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, nextEnergy, courant, *]
                · dynamic_peel
                  refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  dynamic_peel
                  simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, nextMomentum, courant, *]
              · dynamic_peel
                refine wp_call_tw (rejectedCell_exact layout env initial) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                dynamic_peel
                simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, nextDensity, courant, *]
            · dynamic_peel
              refine wp_call_tw (rejectedCell_exact layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, courant, *]
      · dynamic_peel
        refine wp_call_tw (rejectedCell_exact layout env initial) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, right, *]
    · dynamic_peel
      refine wp_call_tw (rejectedCell_exact layout env initial) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      dynamic_peel
      simp [resultValues, Model.cellCheckedBits, Model.rejectedCell, left, *]

#print axioms cellCheckedBits_exact_in_module
end Project.EulerCellStep.Execution
