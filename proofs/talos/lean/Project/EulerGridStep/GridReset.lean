import Project.EulerGridStep.Helpers
import Project.EulerGridStep.GridEntryReady

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Reset changes only the six allocator globals; payload memory is preserved. -/
def gridResetStore (initial : Store Unit) : Store Unit :=
  { initial with globals := { globals :=
    (((((initial.globals.globals.set 0 (.i64 4096)).set 1 (.i64 0)).set 2 (.i64 0)).set 3 (.i64 0)).set 4 (.i64 0)).set 5 (.i64 0) } }

theorem grid_reset_exact {m : Wasm.Module} (hNoImports : m.imports.length = 0)
    (hReset : m.funcs[38]? = some func38Def) (env : HostEnv Unit) (initial : Store Unit)
    (hGlobals : 6 ≤ initial.globals.globals.length) :
    TerminatesWith env m 38 initial []
      (fun final values => final = gridResetStore initial ∧ values = []) := by
  refine TerminatesWith.of_wp_entry_for (f := func38Def)
    (by simpa [hNoImports] using hReset) ?_ (by simp [hNoImports])
  change wp m func38 _ initial (func38Def.toLocals []) env
  wp_run [func38, func38Def, List.set, List.length_set, hGlobals]
  simp [gridResetStore,
    List.getElem?_eq_getElem (by omega : 0 < initial.globals.globals.length),
    List.getElem?_eq_getElem (by omega : 1 < initial.globals.globals.length),
    List.getElem?_eq_getElem (by omega : 2 < initial.globals.globals.length),
    List.getElem?_eq_getElem (by omega : 3 < initial.globals.globals.length),
    List.getElem?_eq_getElem (by omega : 4 < initial.globals.globals.length),
    List.getElem?_eq_getElem (by omega : 5 < initial.globals.globals.length)]

theorem grid_reset_ready (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hPages : initial.mem.pages ≤ 65536)
    (hGlobals : 6 ≤ initial.globals.globals.length)
    (hBudget : 4096 + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ initial.mem.pages * 65536)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot 4096 (1 + 6 * (input.size / 3)) slot) (1 + 6 * (input.size / 3)) pointer input.size) :
    GridEntryReady (gridResetStore initial) pointer input 4096 0 0 0 := by
  refine ⟨hInput, hPages, hBudget, ?_, ?_, ?_, ?_, ?_, hSeparate⟩
  all_goals simp (discharger := omega) [gridResetStore, List.getElem?_set, arenaHeap] <;> omega

#print axioms grid_reset_exact
#print axioms grid_reset_ready
end Project.EulerGridStep.Execution
