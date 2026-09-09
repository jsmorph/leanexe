import Project.EulerDynamicFlux.Helpers

namespace Project.EulerDynamicFlux.Execution
open Wasm
open Project.EulerConservative.Execution (positiveBits_exact_core finiteBits_exact_core)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def componentValues (alpha fluxL fluxR stateL stateR : UInt64) : List Wasm.Value :=
  let out := Model.componentCheckedBits alpha fluxL fluxR stateL stateR
  [.i64 out.value, .i64 out.status]

theorem componentCheckedBits_exact_in_module_core {m : Wasm.Module} (layout : ComponentLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env m 9 initial [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧ values = componentValues alpha fluxL fluxR stateL stateR) := by
  let sum := Wasm.IEEE64.add fluxL fluxR
  let mean := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let jump := Wasm.IEEE64.sub stateR stateL
  let viscosity := Wasm.IEEE64.mul alpha jump
  let halfViscosity := Wasm.IEEE64.mul 0x3FE0000000000000 viscosity
  let value := Wasm.IEEE64.sub mean halfViscosity
  refine TerminatesWith.of_wp_entry_for (f := func9Def)
    (by simpa [layout.noImports] using layout.component) ?_ (by simp [layout.noImports])
  change wp m func9 _ initial (func9Def.toLocals [.i64 alpha, .i64 fluxL, .i64 fluxR, .i64 stateL, .i64 stateR]) env
  unfold func9
  wp_run [func9Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (positiveBits_exact_core layout.toScalarLayout env initial alpha) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases h0 : Project.EulerConservative.Model.positiveBits alpha
  · dynamic_peel
    refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    dynamic_peel
    simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, *]
  · dynamic_peel
    refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial fluxL) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases h1 : Project.EulerConservative.Model.finiteBits fluxL
    · dynamic_peel
      refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      dynamic_peel
      simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, *]
    · dynamic_peel
      refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial fluxR) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      cases h2 : Project.EulerConservative.Model.finiteBits fluxR
      · dynamic_peel
        refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dynamic_peel
        simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, *]
      · dynamic_peel
        refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial stateL) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        cases h3 : Project.EulerConservative.Model.finiteBits stateL
        · dynamic_peel
          refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          dynamic_peel
          simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, *]
        · dynamic_peel
          refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial stateR) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          cases h4 : Project.EulerConservative.Model.finiteBits stateR
          · dynamic_peel
            refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            dynamic_peel
            simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, *]
          · dynamic_peel
            refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial sum) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            cases h5 : Project.EulerConservative.Model.finiteBits sum
            · dynamic_peel
              refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              dynamic_peel
              simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, *]
            · dynamic_peel
              refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial mean) ?_
              rintro st values ⟨hst, rfl⟩
              subst st
              cases h6 : Project.EulerConservative.Model.finiteBits mean
              · dynamic_peel
                refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                dynamic_peel
                simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, mean, *]
              · dynamic_peel
                refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial jump) ?_
                rintro st values ⟨hst, rfl⟩
                subst st
                cases h7 : Project.EulerConservative.Model.finiteBits jump
                · dynamic_peel
                  refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  dynamic_peel
                  simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, mean, jump, *]
                · dynamic_peel
                  refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial viscosity) ?_
                  rintro st values ⟨hst, rfl⟩
                  subst st
                  cases h8 : Project.EulerConservative.Model.finiteBits viscosity
                  · dynamic_peel
                    refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    dynamic_peel
                    simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, mean, jump, viscosity, *]
                  · dynamic_peel
                    refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial halfViscosity) ?_
                    rintro st values ⟨hst, rfl⟩
                    subst st
                    cases h9 : Project.EulerConservative.Model.finiteBits halfViscosity
                    · dynamic_peel
                      refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      dynamic_peel
                      simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, mean, jump, viscosity, halfViscosity, *]
                    · dynamic_peel
                      refine wp_call_tw (finiteBits_exact_core layout.toScalarLayout env initial value) ?_
                      rintro st values ⟨hst, rfl⟩
                      subst st
                      cases h10 : Project.EulerConservative.Model.finiteBits value
                      · dynamic_peel
                        refine wp_call_tw (rejectedComponent_exact_core layout env initial) ?_
                        rintro st values ⟨hst, rfl⟩
                        subst st
                        dynamic_peel
                        simp [componentValues, Model.componentCheckedBits, Model.rejectedComponent, sum, mean, jump, viscosity, halfViscosity, value, *]
                      · dynamic_peel
                        simp [componentValues, Model.componentCheckedBits, sum, mean, jump, viscosity, halfViscosity, value, *]

theorem componentCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env m 9 initial [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧ values = componentValues alpha fluxL fluxR stateL stateR) :=
  componentCheckedBits_exact_in_module_core layout.components env initial alpha fluxL fluxR stateL stateR

#print axioms componentCheckedBits_exact_in_module_core
#print axioms componentCheckedBits_exact_in_module
end Project.EulerDynamicFlux.Execution
