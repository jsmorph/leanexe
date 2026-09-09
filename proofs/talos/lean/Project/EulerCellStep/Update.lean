import Project.EulerCellStep.Helpers

namespace Project.EulerCellStep.Execution
open Wasm
open Project.EulerConservative.Execution (positiveBits_exact_core finiteBits_exact_core)
open Project.EulerDynamicFlux.Execution (rejectedComponent_exact_core)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def updateValues (ratio state fluxL fluxR : UInt64) : List Wasm.Value :=
  let out := Model.updateCheckedBits ratio state fluxL fluxR
  [.i64 out.value, .i64 out.status]

theorem updateCheckedBits_exact_in_module_core {m : Wasm.Module}
    (layout : Project.EulerDynamicFlux.Execution.ComponentLayout m)
    (index : Nat) (typeIdx : Option Nat)
    (hUpdate : m.funcs[index]? = some { func19Def with typeIdx := typeIdx })
    (env : HostEnv Unit) (initial : Store Unit) (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env m index initial [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧ values = updateValues ratio state fluxL fluxR) := by
  let difference := Wasm.IEEE64.sub fluxR fluxL
  let increment := Wasm.IEEE64.mul ratio difference
  let value := Wasm.IEEE64.sub state increment
  refine TerminatesWith.of_wp_entry_for (f := { func19Def with typeIdx := typeIdx })
    (by simpa [layout.noImports] using hUpdate) ?_ (by simp [layout.noImports])
  change wp m func19 _ initial (func19Def.toLocals [.i64 ratio, .i64 state, .i64 fluxL, .i64 fluxR]) env
  unfold func19
  wp_run [func19Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (positiveBits_exact_core layout.toScalarLayout env initial ratio) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases h0 : Project.EulerConservative.Model.positiveBits ratio
  · dynamic_peel
    refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, *]
  · dynamic_peel
    refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial state) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases h1 : Project.EulerConservative.Model.finiteBits state
    · dynamic_peel
      refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      dynamic_peel
      simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, *]
    · dynamic_peel
      refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial fluxL) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      cases h2 : Project.EulerConservative.Model.finiteBits fluxL
      · dynamic_peel
        refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, *]
      · dynamic_peel
        refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial fluxR) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        cases h3 : Project.EulerConservative.Model.finiteBits fluxR
        · dynamic_peel
          refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          dynamic_peel
          simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, *]
        · dynamic_peel
          refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial difference) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          cases h4 : Project.EulerConservative.Model.finiteBits difference
          · dynamic_peel
            refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, difference, *]
          · dynamic_peel
            refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial increment) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            cases h5 : Project.EulerConservative.Model.finiteBits increment
            · dynamic_peel
              refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, difference, increment, *]
            · dynamic_peel
              refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial value) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              cases h6 : Project.EulerConservative.Model.finiteBits value
              · dynamic_peel
                refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                dynamic_peel
                simp [updateValues, Model.updateCheckedBits, Project.EulerDynamicFlux.Model.rejectedComponent, difference, increment, value, *]
              · dynamic_peel
                simp [updateValues, Model.updateCheckedBits, difference, increment, value, *]

theorem updateCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env m 19 initial [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧ values = updateValues ratio state fluxL fluxR) :=
  updateCheckedBits_exact_in_module_core layout.toLayout.components 19 (some 19)
    layout.update env initial ratio state fluxL fluxR

#print axioms updateCheckedBits_exact_in_module_core
#print axioms updateCheckedBits_exact_in_module
end Project.EulerCellStep.Execution
