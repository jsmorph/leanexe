import Project.EulerRiemann.ExecutionSide
import Project.EulerRiemann.ExecutionScalar
import Project.Euler2DDynamicFlux.Execution

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem rejectedFlux_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 46 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func46Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func46 _ initial (func46Def.toLocals []) env
  unfold func46
  wp_run
  simp [func46Def, List.set]

theorem flux_exact
    (env : HostEnv Unit) (initial : Store Unit) (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 47 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = Project.Euler2DDynamicFlux.Execution.resultValues rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR) := by
  let left := Project.Euler2DConservative.Model.sideCheckedBits rhoL momentumL transverseL energyL
  have leftCall := side_exact env initial rhoL momentumL transverseL energyL
  change TerminatesWith env Project.EulerRiemann.«module» 15 initial [.i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.energyFlux, .i64 left.transverseFlux, .i64 left.momentumFlux, .i64 left.massFlux, .i64 left.speed, .i64 left.pressure, .i64 left.velocity, .i64 left.status]) at leftCall
  let right := Project.Euler2DConservative.Model.sideCheckedBits rhoR momentumR transverseR energyR
  have rightCall := side_exact env initial rhoR momentumR transverseR energyR
  change TerminatesWith env Project.EulerRiemann.«module» 15 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR]
    (fun final values => final = initial ∧ values = [.i64 right.energyFlux, .i64 right.transverseFlux, .i64 right.momentumFlux, .i64 right.massFlux, .i64 right.speed, .i64 right.pressure, .i64 right.velocity, .i64 right.status]) at rightCall
  refine TerminatesWith.of_wp_entry_for (f := func47Def)
    rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func47 _ initial (func47Def.toLocals [.i64 rhoL, .i64 momentumL, .i64 transverseL, .i64 energyL, .i64 rhoR, .i64 momentumR, .i64 transverseR, .i64 energyR]) env
  unfold func47
  wp_run [func47Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw leftCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  flux_guard (left.status = 0) reject (rejectedFlux_exact env initial)
  refine wp_call_tw rightCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  flux_guard (right.status = 0) reject (rejectedFlux_exact env initial)
  let alpha := if left.speed ≤ right.speed then right.speed else left.speed
  by_cases hspeed : left.speed ≤ right.speed
  all_goals
    dynamic_peel
    let mass := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
    have massCall := component_exact env initial alpha left.massFlux right.massFlux rhoL rhoR
    change TerminatesWith env Project.EulerRiemann.«module» 39 initial [.i64 rhoR, .i64 rhoL, .i64 right.massFlux, .i64 left.massFlux, .i64 alpha]
      (fun final values => final = initial ∧ values = [.i64 mass.value, .i64 mass.status]) at massCall
    simp only [alpha, hspeed, ite_true, ite_false] at massCall
    refine wp_call_tw massCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let momentum := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.momentumFlux right.momentumFlux momentumL momentumR
    have momentumCall := component_exact env initial alpha left.momentumFlux right.momentumFlux momentumL momentumR
    change TerminatesWith env Project.EulerRiemann.«module» 39 initial [.i64 momentumR, .i64 momentumL, .i64 right.momentumFlux, .i64 left.momentumFlux, .i64 alpha]
      (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
    simp only [alpha, hspeed, ite_true, ite_false] at momentumCall
    refine wp_call_tw momentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let transverse := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.transverseFlux right.transverseFlux transverseL transverseR
    have transverseCall := component_exact env initial alpha left.transverseFlux right.transverseFlux transverseL transverseR
    change TerminatesWith env Project.EulerRiemann.«module» 39 initial [.i64 transverseR, .i64 transverseL, .i64 right.transverseFlux, .i64 left.transverseFlux, .i64 alpha]
      (fun final values => final = initial ∧ values = [.i64 transverse.value, .i64 transverse.status]) at transverseCall
    simp only [alpha, hspeed, ite_true, ite_false] at transverseCall
    refine wp_call_tw transverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let energy := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
    have energyCall := component_exact env initial alpha left.energyFlux right.energyFlux energyL energyR
    change TerminatesWith env Project.EulerRiemann.«module» 39 initial [.i64 energyR, .i64 energyL, .i64 right.energyFlux, .i64 left.energyFlux, .i64 alpha]
      (fun final values => final = initial ∧ values = [.i64 energy.value, .i64 energy.status]) at energyCall
    simp only [alpha, hspeed, ite_true, ite_false] at energyCall
    refine wp_call_tw energyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    flux_guard (mass.status = 0) reject (rejectedFlux_exact env initial)
    flux_guard (momentum.status = 0) reject (rejectedFlux_exact env initial)
    flux_guard (transverse.status = 0) reject (rejectedFlux_exact env initial)
    flux_guard (energy.status = 0) reject (rejectedFlux_exact env initial)
    simp_all +zetaDelta [Project.Euler2DDynamicFlux.Execution.resultValues, Project.Euler2DDynamicFlux.Model.fluxCheckedBits, Project.Euler2DDynamicFlux.Model.rejectedFlux, -UInt64.not_le]

#print axioms rejectedFlux_exact
#print axioms flux_exact

end Project.EulerRiemann.Execution
