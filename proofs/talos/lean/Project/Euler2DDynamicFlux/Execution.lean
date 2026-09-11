import Project.Euler2DDynamicFlux.Helpers

namespace Project.Euler2DDynamicFlux.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) : List Wasm.Value :=
  let out := Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR
  [.i64 out.alpha, .i64 out.energy, .i64 out.transverse, .i64 out.momentum, .i64 out.mass, .i64 out.status]

/-- Split each status guard, finishing rejection before continuing the successful path. -/
macro "flux_guard" checkCond:term "reject" rejection:term : tactic =>
  `(tactic|
    (by_cases hcheck : $checkCond
     case neg =>
       dynamic_peel
       refine wp_call_tw $rejection ?_
       rintro st values ⟨hst, hvalues⟩
       subst st
       subst values
       dynamic_peel
       simp_all +zetaDelta [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, -UInt64.not_le]
     all_goals dynamic_peel))

theorem fluxCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) :
    TerminatesWith env m 25 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR) := by
  let left := Project.Euler2DConservative.Model.sideCheckedBits rhoL momentumL transverseL energyL
  have leftCall := Project.Euler2DConservative.Execution.sideCheckedBits_exact_in_module
    layout.toHelperLayout layout.side env initial rhoL momentumL transverseL energyL
  change TerminatesWith env m 13 initial [.i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.energyFlux, .i64 left.transverseFlux, .i64 left.momentumFlux, .i64 left.massFlux, .i64 left.speed, .i64 left.pressure, .i64 left.velocity, .i64 left.status]) at leftCall
  let right := Project.Euler2DConservative.Model.sideCheckedBits rhoR momentumR transverseR energyR
  have rightCall := Project.Euler2DConservative.Execution.sideCheckedBits_exact_in_module
    layout.toHelperLayout layout.side env initial rhoR momentumR transverseR energyR
  change TerminatesWith env m 13 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR]
    (fun final values => final = initial ∧ values = [.i64 right.energyFlux, .i64 right.transverseFlux, .i64 right.momentumFlux, .i64 right.massFlux, .i64 right.speed, .i64 right.pressure, .i64 right.velocity, .i64 right.status]) at rightCall
  refine TerminatesWith.of_wp_entry_for (f := func25Def)
    (by simpa [layout.noImports] using layout.flux) ?_ (by simp [layout.noImports])
  change wp m func25 _ initial (func25Def.toLocals [.i64 rhoL, .i64 momentumL, .i64 transverseL, .i64 energyL, .i64 rhoR, .i64 momentumR, .i64 transverseR, .i64 energyR]) env
  unfold func25
  wp_run [func25Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw leftCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  flux_guard (left.status = 0) reject (rejectedFlux_exact layout env initial)
  refine wp_call_tw rightCall ?_
  rintro st values ⟨hst, hvalues⟩
  subst st
  subst values
  flux_guard (right.status = 0) reject (rejectedFlux_exact layout env initial)
  by_cases hspeed : left.speed ≤ right.speed
  · dynamic_peel
    let mass := Model.componentCheckedBits right.speed left.massFlux right.massFlux rhoL rhoR
    have massCall := componentCheckedBits_exact_in_module
      layout env initial right.speed left.massFlux right.massFlux rhoL rhoR
    change TerminatesWith env m 17 initial [.i64 rhoR, .i64 rhoL, .i64 right.massFlux, .i64 left.massFlux, .i64 right.speed]
      (fun final values => final = initial ∧ values = [.i64 mass.value, .i64 mass.status]) at massCall
    refine wp_call_tw massCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let momentum := Model.componentCheckedBits right.speed left.momentumFlux right.momentumFlux momentumL momentumR
    have momentumCall := componentCheckedBits_exact_in_module
      layout env initial right.speed left.momentumFlux right.momentumFlux momentumL momentumR
    change TerminatesWith env m 17 initial [.i64 momentumR, .i64 momentumL, .i64 right.momentumFlux, .i64 left.momentumFlux, .i64 right.speed]
      (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
    refine wp_call_tw momentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let transverse := Model.componentCheckedBits right.speed left.transverseFlux right.transverseFlux transverseL transverseR
    have transverseCall := componentCheckedBits_exact_in_module
      layout env initial right.speed left.transverseFlux right.transverseFlux transverseL transverseR
    change TerminatesWith env m 17 initial [.i64 transverseR, .i64 transverseL, .i64 right.transverseFlux, .i64 left.transverseFlux, .i64 right.speed]
      (fun final values => final = initial ∧ values = [.i64 transverse.value, .i64 transverse.status]) at transverseCall
    refine wp_call_tw transverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let energy := Model.componentCheckedBits right.speed left.energyFlux right.energyFlux energyL energyR
    have energyCall := componentCheckedBits_exact_in_module
      layout env initial right.speed left.energyFlux right.energyFlux energyL energyR
    change TerminatesWith env m 17 initial [.i64 energyR, .i64 energyL, .i64 right.energyFlux, .i64 left.energyFlux, .i64 right.speed]
      (fun final values => final = initial ∧ values = [.i64 energy.value, .i64 energy.status]) at energyCall
    refine wp_call_tw energyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    flux_guard (mass.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (momentum.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (transverse.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (energy.status = 0) reject (rejectedFlux_exact layout env initial)
    simp_all +zetaDelta [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, -UInt64.not_le]
  · dynamic_peel
    let mass := Model.componentCheckedBits left.speed left.massFlux right.massFlux rhoL rhoR
    have massCall := componentCheckedBits_exact_in_module
      layout env initial left.speed left.massFlux right.massFlux rhoL rhoR
    change TerminatesWith env m 17 initial [.i64 rhoR, .i64 rhoL, .i64 right.massFlux, .i64 left.massFlux, .i64 left.speed]
      (fun final values => final = initial ∧ values = [.i64 mass.value, .i64 mass.status]) at massCall
    refine wp_call_tw massCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let momentum := Model.componentCheckedBits left.speed left.momentumFlux right.momentumFlux momentumL momentumR
    have momentumCall := componentCheckedBits_exact_in_module
      layout env initial left.speed left.momentumFlux right.momentumFlux momentumL momentumR
    change TerminatesWith env m 17 initial [.i64 momentumR, .i64 momentumL, .i64 right.momentumFlux, .i64 left.momentumFlux, .i64 left.speed]
      (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
    refine wp_call_tw momentumCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let transverse := Model.componentCheckedBits left.speed left.transverseFlux right.transverseFlux transverseL transverseR
    have transverseCall := componentCheckedBits_exact_in_module
      layout env initial left.speed left.transverseFlux right.transverseFlux transverseL transverseR
    change TerminatesWith env m 17 initial [.i64 transverseR, .i64 transverseL, .i64 right.transverseFlux, .i64 left.transverseFlux, .i64 left.speed]
      (fun final values => final = initial ∧ values = [.i64 transverse.value, .i64 transverse.status]) at transverseCall
    refine wp_call_tw transverseCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    let energy := Model.componentCheckedBits left.speed left.energyFlux right.energyFlux energyL energyR
    have energyCall := componentCheckedBits_exact_in_module
      layout env initial left.speed left.energyFlux right.energyFlux energyL energyR
    change TerminatesWith env m 17 initial [.i64 energyR, .i64 energyL, .i64 right.energyFlux, .i64 left.energyFlux, .i64 left.speed]
      (fun final values => final = initial ∧ values = [.i64 energy.value, .i64 energy.status]) at energyCall
    refine wp_call_tw energyCall ?_
    rintro st values ⟨hst, hvalues⟩
    subst st
    subst values
    dynamic_peel
    flux_guard (mass.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (momentum.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (transverse.status = 0) reject (rejectedFlux_exact layout env initial)
    flux_guard (energy.status = 0) reject (rejectedFlux_exact layout env initial)
    simp_all +zetaDelta [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, -UInt64.not_le]

#print axioms fluxCheckedBits_exact_in_module
end Project.Euler2DDynamicFlux.Execution
