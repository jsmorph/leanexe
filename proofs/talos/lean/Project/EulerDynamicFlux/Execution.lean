import Project.EulerDynamicFlux.Component

namespace Project.EulerDynamicFlux.Execution
open Wasm
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def resultValues (rhoL momentumL energyL rhoR momentumR energyR : UInt64) : List Wasm.Value :=
  let out := Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR
  [.i64 out.alpha, .i64 out.energy, .i64 out.momentum, .i64 out.mass, .i64 out.status]

theorem fluxCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (rhoL momentumL energyL rhoR momentumR energyR : UInt64) :
    TerminatesWith env m 16 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL energyL rhoR momentumR energyR) := by
  let left := Project.EulerConservative.Model.sideCheckedBits rhoL momentumL energyL
  let right := Project.EulerConservative.Model.sideCheckedBits rhoR momentumR energyR
  have leftCall := Project.EulerConservative.Execution.sideCheckedBits_exact_in_module
    layout.toHelperLayout layout.side env initial rhoL momentumL energyL
  change TerminatesWith env m 5 initial [.i64 energyL, .i64 momentumL, .i64 rhoL]
    (fun final values => final = initial ∧ values = [.i64 left.energyFlux, .i64 left.momentumFlux, .i64 left.massFlux, .i64 left.speed, .i64 left.pressure, .i64 left.velocity, .i64 left.status]) at leftCall
  have rightCall := Project.EulerConservative.Execution.sideCheckedBits_exact_in_module
    layout.toHelperLayout layout.side env initial rhoR momentumR energyR
  change TerminatesWith env m 5 initial [.i64 energyR, .i64 momentumR, .i64 rhoR]
    (fun final values => final = initial ∧ values = [.i64 right.energyFlux, .i64 right.momentumFlux, .i64 right.massFlux, .i64 right.speed, .i64 right.pressure, .i64 right.velocity, .i64 right.status]) at rightCall
  refine TerminatesWith.of_wp_entry_for (f := func16Def)
    (by simpa [layout.noImports] using layout.flux) ?_ (by simp [layout.noImports])
  change wp m func16 _ initial (func16Def.toLocals [.i64 rhoL, .i64 momentumL, .i64 energyL, .i64 rhoR, .i64 momentumR, .i64 energyR]) env
  unfold func16
  wp_run [func16Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
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
      by_cases hspeed : left.speed ≤ right.speed
      · dynamic_peel
        let mass := Model.componentCheckedBits right.speed left.massFlux right.massFlux rhoL rhoR
        have massCall := componentCheckedBits_exact_in_module layout env initial
          right.speed left.massFlux right.massFlux rhoL rhoR
        change TerminatesWith env m 9 initial [.i64 rhoR, .i64 rhoL, .i64 right.massFlux, .i64 left.massFlux, .i64 right.speed]
          (fun final values => final = initial ∧ values = [.i64 mass.value, .i64 mass.status]) at massCall
        refine wp_call_tw (massCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        let momentum := Model.componentCheckedBits right.speed left.momentumFlux right.momentumFlux momentumL momentumR
        have momentumCall := componentCheckedBits_exact_in_module layout env initial
          right.speed left.momentumFlux right.momentumFlux momentumL momentumR
        change TerminatesWith env m 9 initial [.i64 momentumR, .i64 momentumL, .i64 right.momentumFlux, .i64 left.momentumFlux, .i64 right.speed]
          (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
        refine wp_call_tw (momentumCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        let energy := Model.componentCheckedBits right.speed left.energyFlux right.energyFlux energyL energyR
        have energyCall := componentCheckedBits_exact_in_module layout env initial
          right.speed left.energyFlux right.energyFlux energyL energyR
        change TerminatesWith env m 9 initial [.i64 energyR, .i64 energyL, .i64 right.energyFlux, .i64 left.energyFlux, .i64 right.speed]
          (fun final values => final = initial ∧ values = [.i64 energy.value, .i64 energy.status]) at energyCall
        refine wp_call_tw (energyCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        by_cases h0 : mass.status = 0
        · dynamic_peel
          by_cases h1 : momentum.status = 0
          · dynamic_peel
            by_cases h2 : energy.status = 0
            · dynamic_peel
              simp [resultValues, Model.fluxCheckedBits, left, right, mass, momentum, energy, *]
            · dynamic_peel
              refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, momentum, energy, *]
          · dynamic_peel
            refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, momentum, *]
        · dynamic_peel
          refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          dynamic_peel
          simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, *]
      · dynamic_peel
        let mass := Model.componentCheckedBits left.speed left.massFlux right.massFlux rhoL rhoR
        have massCall := componentCheckedBits_exact_in_module layout env initial
          left.speed left.massFlux right.massFlux rhoL rhoR
        change TerminatesWith env m 9 initial [.i64 rhoR, .i64 rhoL, .i64 right.massFlux, .i64 left.massFlux, .i64 left.speed]
          (fun final values => final = initial ∧ values = [.i64 mass.value, .i64 mass.status]) at massCall
        refine wp_call_tw (massCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        let momentum := Model.componentCheckedBits left.speed left.momentumFlux right.momentumFlux momentumL momentumR
        have momentumCall := componentCheckedBits_exact_in_module layout env initial
          left.speed left.momentumFlux right.momentumFlux momentumL momentumR
        change TerminatesWith env m 9 initial [.i64 momentumR, .i64 momentumL, .i64 right.momentumFlux, .i64 left.momentumFlux, .i64 left.speed]
          (fun final values => final = initial ∧ values = [.i64 momentum.value, .i64 momentum.status]) at momentumCall
        refine wp_call_tw (momentumCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        let energy := Model.componentCheckedBits left.speed left.energyFlux right.energyFlux energyL energyR
        have energyCall := componentCheckedBits_exact_in_module layout env initial
          left.speed left.energyFlux right.energyFlux energyL energyR
        change TerminatesWith env m 9 initial [.i64 energyR, .i64 energyL, .i64 right.energyFlux, .i64 left.energyFlux, .i64 left.speed]
          (fun final values => final = initial ∧ values = [.i64 energy.value, .i64 energy.status]) at energyCall
        refine wp_call_tw (energyCall) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        by_cases h0 : mass.status = 0
        · dynamic_peel
          by_cases h1 : momentum.status = 0
          · dynamic_peel
            by_cases h2 : energy.status = 0
            · dynamic_peel
              simp [resultValues, Model.fluxCheckedBits, left, right, mass, momentum, energy, *]
            · dynamic_peel
              refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, momentum, energy, *]
          · dynamic_peel
            refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, momentum, *]
        · dynamic_peel
          refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          dynamic_peel
          simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, mass, *]
    · dynamic_peel
      refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      dynamic_peel
      simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, right, *]
  · dynamic_peel
    refine wp_call_tw (rejectedFlux_exact layout env initial) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    simp [resultValues, Model.fluxCheckedBits, Model.rejectedFlux, left, *]

#print axioms fluxCheckedBits_exact_in_module
end Project.EulerDynamicFlux.Execution
