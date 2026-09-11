import Project.Euler2DConservative.Program
import Project.Euler2DConservative.Model
import Project.EulerConservative.Helpers

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure HelperLayout (m : Wasm.Module) extends Project.EulerConservative.Execution.ScalarLayout m where
  narrowState : m.funcs[3]? = some func3Def
  maxWord : m.funcs[4]? = some func4Def
  exponent : m.funcs[5]? = some func5Def
  topExponent : m.funcs[6]? = some func6Def
  normalizable : m.funcs[7]? = some func7Def
  residual : m.funcs[8]? = some func8Def
  normalized : m.funcs[9]? = some func9Def
  energy : m.funcs[10]? = some func10Def
  state : m.funcs[11]? = some func11Def
  rejected : m.funcs[12]? = some func12Def

theorem concreteHelperLayout : HelperLayout Project.Euler2DConservative.«module» :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    TerminatesWith env m 12 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func12Def)
    (by simpa [layout.noImports] using layout.rejected) ?_ (by simp [layout.noImports])
  change wp m func12 _ initial (func12Def.toLocals []) env
  unfold func12
  wp_run
  simp [func12Def, List.set]

#print axioms concreteHelperLayout
#print axioms absBits_exact
#print axioms positiveBits_exact
#print axioms finiteBits_exact
#print axioms rejectedSide_exact
end Project.Euler2DConservative.Execution
