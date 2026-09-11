import Project.Euler2DCellStep.Helpers

namespace Project.Euler2DCellStep.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) : List Wasm.Value :=
  let out := Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy, .i64 out.transverse, .i64 out.momentum, .i64 out.density, .i64 out.status]

macro "cell_guard" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (by_cases hcheck : $checkCond
     case neg =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       dynamic_peel
       simp_all +zetaDelta [resultValues, Model.cellCheckedBits, Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

macro "cell_bool" checkedCall:term "when" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (refine wp_call_tw $checkedCall ?_
     rintro st values ⟨hst, hvalues⟩
     subst st
     subst values
     cases hcheck : $checkCond
     case false =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       dynamic_peel
       simp_all +zetaDelta [resultValues, Model.cellCheckedBits, Model.rejectedCell, -UInt64.not_le]
     all_goals dynamic_peel))

theorem cellCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) :
    TerminatesWith env m 35 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 transverse, .i64 momentum, .i64 rho, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL, .i64 ratio]
      (fun final values => final = initial ∧ values = resultValues ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR) := by
  let left := Project.Euler2DDynamicFlux.Model.fluxCheckedBits rhoL momentumL transverseL energyL rho momentum transverse energy
  have leftCall := Project.Euler2DDynamicFlux.Execution.fluxCheckedBits_exact_in_module
    layout.toLayout env initial rhoL momentumL transverseL energyL rho momentum transverse energy
  change TerminatesWith env m 25 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.alpha, .i64 left.energy, .i64 left.transverse, .i64 left.momentum, .i64 left.mass, .i64 left.status]) at leftCall
  let right := Project.Euler2DDynamicFlux.Model.fluxCheckedBits rho momentum transverse energy rhoR momentumR transverseR energyR
  have rightCall := Project.Euler2DDynamicFlux.Execution.fluxCheckedBits_exact_in_module
    layout.toLayout env initial rho momentum transverse energy rhoR momentumR transverseR energyR
  change TerminatesWith env m 25 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
    (fun final values => final = initial ∧ values = [.i64 right.alpha, .i64 right.energy, .i64 right.transverse, .i64 right.momentum, .i64 right.mass, .i64 right.status]) at rightCall
  let nextDensity := Model.updateCheckedBits ratio rho left.mass right.mass
  have nextDensityCall := updateCheckedBits_exact_in_module layout env initial ratio rho left.mass right.mass
  change TerminatesWith env m 28 initial [.i64 right.mass, .i64 left.mass, .i64 rho, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextDensity.value, .i64 nextDensity.status]) at nextDensityCall
  let nextMomentum := Model.updateCheckedBits ratio momentum left.momentum right.momentum
  have nextMomentumCall := updateCheckedBits_exact_in_module layout env initial ratio momentum left.momentum right.momentum
  change TerminatesWith env m 28 initial [.i64 right.momentum, .i64 left.momentum, .i64 momentum, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextMomentum.value, .i64 nextMomentum.status]) at nextMomentumCall
  let nextTransverse := Model.updateCheckedBits ratio transverse left.transverse right.transverse
  have nextTransverseCall := updateCheckedBits_exact_in_module layout env initial ratio transverse left.transverse right.transverse
  change TerminatesWith env m 28 initial [.i64 right.transverse, .i64 left.transverse, .i64 transverse, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextTransverse.value, .i64 nextTransverse.status]) at nextTransverseCall
  let nextEnergy := Model.updateCheckedBits ratio energy left.energy right.energy
  have nextEnergyCall := updateCheckedBits_exact_in_module layout env initial ratio energy left.energy right.energy
  change TerminatesWith env m 28 initial [.i64 right.energy, .i64 left.energy, .i64 energy, .i64 ratio]
    (fun final values => final = initial ∧ values = [.i64 nextEnergy.value, .i64 nextEnergy.status]) at nextEnergyCall
  let nextSide := Project.Euler2DConservative.Model.sideCheckedBits nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
  have nextSideCall := Project.Euler2DConservative.Execution.sideCheckedBits_exact_in_module
    layout.toLayout.toHelperLayout layout.side env initial nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
  change TerminatesWith env m 13 initial [.i64 nextEnergy.value, .i64 nextTransverse.value, .i64 nextMomentum.value, .i64 nextDensity.value]
    (fun final values => final = initial ∧ values = [.i64 nextSide.energyFlux, .i64 nextSide.transverseFlux, .i64 nextSide.momentumFlux, .i64 nextSide.massFlux, .i64 nextSide.speed, .i64 nextSide.pressure, .i64 nextSide.velocity, .i64 nextSide.status]) at nextSideCall
  refine TerminatesWith.of_wp_entry_for (f := func35Def)
    (by simpa [layout.noImports] using layout.cell) ?_ (by simp [layout.noImports])
  change wp m func35 _ initial (func35Def.toLocals [.i64 ratio, .i64 rhoL, .i64 momentumL, .i64 transverseL, .i64 energyL, .i64 rho, .i64 momentum, .i64 transverse, .i64 energy, .i64 rhoR, .i64 momentumR, .i64 transverseR, .i64 energyR]) env
  unfold func35
  wp_run [func35Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  cell_bool (Project.Euler2DConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial ratio)
    when (Project.Euler2DConservative.Model.positiveBits ratio) reject (rejectedCell_exact layout env initial)
  refine wp_call_tw leftCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  cell_guard (left.status = 0) reject (rejectedCell_exact layout env initial)
  refine wp_call_tw rightCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  cell_guard (right.status = 0) reject (rejectedCell_exact layout env initial)
  by_cases hspeed : left.alpha ≤ right.alpha
  · dynamic_peel
    let courant := Wasm.IEEE64.mul ratio right.alpha
    cell_bool (Project.Euler2DConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial courant)
      when (Project.Euler2DConservative.Model.positiveBits courant) reject (rejectedCell_exact layout env initial)
    cell_guard (Wasm.IEEE64.mul ratio right.alpha ≤ 0x3FE0000000000000) reject (rejectedCell_exact layout env initial)
    refine wp_call_tw nextDensityCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextMomentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextTransverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextEnergyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    cell_guard (nextDensity.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextMomentum.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextTransverse.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextEnergy.status = 0) reject (rejectedCell_exact layout env initial)
    refine wp_call_tw nextSideCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    cell_guard (nextSide.status = 0) reject (rejectedCell_exact layout env initial)
    simp_all +zetaDelta [resultValues, Model.cellCheckedBits, Model.rejectedCell, -UInt64.not_le]
  · dynamic_peel
    let courant := Wasm.IEEE64.mul ratio left.alpha
    cell_bool (Project.Euler2DConservative.Execution.positiveBits_exact layout.toLayout.toHelperLayout env initial courant)
      when (Project.Euler2DConservative.Model.positiveBits courant) reject (rejectedCell_exact layout env initial)
    cell_guard (Wasm.IEEE64.mul ratio left.alpha ≤ 0x3FE0000000000000) reject (rejectedCell_exact layout env initial)
    refine wp_call_tw nextDensityCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextMomentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextTransverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    refine wp_call_tw nextEnergyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    cell_guard (nextDensity.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextMomentum.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextTransverse.status = 0) reject (rejectedCell_exact layout env initial)
    cell_guard (nextEnergy.status = 0) reject (rejectedCell_exact layout env initial)
    refine wp_call_tw nextSideCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    cell_guard (nextSide.status = 0) reject (rejectedCell_exact layout env initial)
    simp_all +zetaDelta [resultValues, Model.cellCheckedBits, Model.rejectedCell, -UInt64.not_le]

#print axioms cellCheckedBits_exact_in_module
end Project.Euler2DCellStep.Execution
