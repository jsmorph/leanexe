import Project.EulerConservative.Program
import Project.EulerConservative.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

namespace Project.EulerConservative.Execution
open Wasm
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The checked side's helper block can be embedded in a larger closed module. -/
structure HelperLayout (m : Wasm.Module) : Prop where
  noImports : m.imports = []
  positive : m.funcs[0]? = some func0Def
  abs : m.funcs[1]? = some func1Def
  finite : m.funcs[2]? = some func2Def
  state : m.funcs[3]? = some func3Def
  rejected : m.funcs[4]? = some func4Def

def boolWord (b : Bool) : UInt64 := if b then 1 else 0

theorem absBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 1 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (Model.absBits word)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def)
    (by simpa [layout.noImports] using layout.abs) ?_ (by simp [layout.noImports])
  change wp m func1 _ initial { params := [.i64 word], locals := [.i64 0], values := [] } env
  unfold func1
  wp_run
  simp [Model.absBits, func1Def]

theorem positiveBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 0 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Model.positiveBits word))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def)
    (by simpa [layout.noImports] using layout.positive) ?_ (by simp [layout.noImports])
  change wp m func0 _ initial { params := [.i64 word], locals := [.i64 0], values := [] } env
  unfold func0
  by_cases hlo : (0 : UInt64) < word <;> by_cases hhi : word < (0x7FF0000000000000 : UInt64)
  all_goals
    repeat
      first
      | wp_run [hlo, hhi]
      | refine wp_iff_cons rfl ?_
        simp [hlo, hhi]
    simp [hlo, hhi, boolWord, Model.positiveBits, func0Def]

theorem finiteBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env m 2 initial [.i64 word]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Model.finiteBits word))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def)
    (by simpa [layout.noImports] using layout.finite) ?_ (by simp [layout.noImports])
  change wp m func2 _ initial
    { params := [.i64 word], locals := [.i64 0, .i64 0], values := [] } env
  unfold func2
  wp_run
  refine wp_call_tw (absBits_exact layout env initial word) ?_
  rintro final values ⟨rfl, rfl⟩
  by_cases hfinite : Model.absBits word < (0x7FF0000000000000 : UInt64)
  all_goals
    repeat
      first
      | wp_run [hfinite]
      | refine wp_iff_cons rfl ?_
        simp
    simp [hfinite, boolWord, Model.finiteBits, func2Def]

theorem rejectedSide_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env m 4 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def)
    (by simpa [layout.noImports] using layout.rejected) ?_ (by simp [layout.noImports])
  change wp m func4 _ initial
    { params := [], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
  unfold func4
  wp_run
  simp [func4Def]

#print axioms absBits_exact
#print axioms positiveBits_exact
#print axioms finiteBits_exact
#print axioms rejectedSide_exact
end Project.EulerConservative.Execution
