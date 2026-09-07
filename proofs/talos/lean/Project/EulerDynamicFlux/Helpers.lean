import Project.EulerDynamicFlux.Program
import Project.EulerDynamicFlux.Model
import Project.EulerConservative.Execution

namespace Project.EulerDynamicFlux.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Exact shared helpers and the dynamic-flux functions in a closed module. -/
structure Layout (m : Wasm.Module) extends Project.EulerConservative.Execution.HelperLayout m where
  side : m.funcs[5]? = some Project.EulerConservative.func5Def
  rejectedComponent : m.funcs[8]? = some func8Def
  component : m.funcs[9]? = some func9Def
  rejectedFlux : m.funcs[15]? = some func15Def
  flux : m.funcs[16]? = some func16Def

theorem concreteLayout : Layout Project.EulerDynamicFlux.«module» := by
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

macro "dynamic_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boolWord, Wasm.f64Add, Wasm.f64Sub, Wasm.f64Mul,
        List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        reduceIte, ite_true, ite_false, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [boolWord, *])

theorem rejectedComponent_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 8 initial []
      (fun final values => final = initial ∧ values = [.i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def)
    (by simpa [layout.noImports] using layout.rejectedComponent) ?_ (by simp [layout.noImports])
  change wp m func8 _ initial { params := [], locals := [.i64 0, .i64 0], values := [] } env
  unfold func8
  wp_run
  simp [func8Def]

theorem rejectedFlux_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 15 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def)
    (by simpa [layout.noImports] using layout.rejectedFlux) ?_ (by simp [layout.noImports])
  change wp m func15 _ initial
    { params := [], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
  unfold func15
  wp_run
  simp [func15Def]

#print axioms concreteLayout
#print axioms rejectedComponent_exact
#print axioms rejectedFlux_exact
end Project.EulerDynamicFlux.Execution
