import Project.Euler2DConservative.Program
import Project.Euler2DConservative.Model
import Project.EulerConservative.Helpers

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure HelperLayout (m : Wasm.Module) extends Project.EulerConservative.Execution.ScalarLayout m where
  state : m.funcs[3]? = some func3Def
  rejected : m.funcs[4]? = some func4Def

theorem concreteHelperLayout : HelperLayout Project.Euler2DConservative.«module» :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem absBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 1 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (Model.absBits word)]) :=
  Project.EulerConservative.Execution.absBits_exact_core layout.toScalarLayout env initial word

theorem positiveBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 0 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Model.positiveBits word))]) :=
  Project.EulerConservative.Execution.positiveBits_exact_core layout.toScalarLayout env initial word

theorem finiteBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 2 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Model.finiteBits word))]) :=
  Project.EulerConservative.Execution.finiteBits_exact_core layout.toScalarLayout env initial word

theorem rejectedSide_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 4 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def)
    (by simpa [layout.noImports] using layout.rejected) ?_ (by simp [layout.noImports])
  change wp m func4 _ initial (func4Def.toLocals []) env
  unfold func4
  wp_run
  simp [func4Def, List.set]

#print axioms concreteHelperLayout
#print axioms absBits_exact
#print axioms positiveBits_exact
#print axioms finiteBits_exact
#print axioms rejectedSide_exact
end Project.Euler2DConservative.Execution
