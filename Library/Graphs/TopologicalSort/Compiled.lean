import Library.Graphs.TopologicalSort.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of topological sorting.  `topoSort_call` states the call of the
export from the generated `compiled.topoSort.trapFree`: from a ready store with room for the
generated bound, the call returns `topoSort xs` without a trap.  `topoSort_spec` of the proof states
what that result is on a well-formed input: a topological order, or the empty array when none
exists. -/

namespace Library.Graphs.TopologicalSort

open Wasm LeanExe.Pipeline

verified_compile compiled := [countPredecessors, initialQueue, process, topoSort]

theorem topoSort_export :
    ({ name := "topoSort", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `topoSort`, called from a ready store with room for
`compiled.topoSort.bound xs` bytes, returns without a trap the owned array `topoSort xs` and leaves
a ready store. -/
theorem topoSort_call :
    Verified.Call compiled.module compiled.tables 5 topoSort
      (fun x heap store => heap.Within store compiled.module (compiled.topoSort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.topoSort.bound x) :=
  Verified.ImplementsTables.call (.ofA compiled.topoSort.trapFree) compiled.tables nofun

#print axioms topoSort_call
#print axioms topoSort_spec

end Library.Graphs.TopologicalSort
