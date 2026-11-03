import Library.Graphs.Dijkstra.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of the shortest walk lengths from one vertex by Dijkstra's
algorithm.  By the compiler's rules, which the verified compiler's manual states, the compiler
translates the tail recursions of `siftUp` and `siftDown` and the loops of `relax` and `dijkstra`
into loops, so no theorem of the module has a call-depth premise, and `relax` updates the tentative
lengths and the heap's two arrays in place, since the loop owns them, so the generated
`compiled.relax.bound_eq` states a bound of 0.  The caller lends `first`, `heads`, and `lens`.  For
a source below `n` the module builds the tentative lengths and the done flags, each of `n` words,
and the heap's keys and vertices, each of `first[n]` words, and otherwise it builds the result of
`n` words.  `dijkstra_call` states the call of the export from the generated
`compiled.dijkstra.trapFree`: it returns the array of the Lean function `dijkstra`, and
`dijkstra_spec` of the proof states that, for a graph in the request's form, that array holds the
least walk lengths. -/

namespace Library.Graphs.Dijkstra

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [swap, addSat, siftUp, siftDown, relax, dijkstra]

theorem dijkstra_export :
    ({ name := "dijkstra", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 7, the export `dijkstra`, called with a count `n`, a source `s`, and three lent
arrays from a ready store with room for `compiled.dijkstra.bound` bytes, returns without a trap the
owned array `dijkstra n s first heads lens` and leaves a ready store. -/
theorem dijkstra_call :
    Verified.Call compiled.module compiled.tables 7
      (fun x => dijkstra x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.dijkstra.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.dijkstra.bound x) :=
  Verified.ImplementsTables.call (.ofA compiled.dijkstra.trapFree) compiled.tables nofun

/-- The generated bound: for a source below `n`, two blocks of `n` words and two blocks of
`first[n]` words, and otherwise one block of `n` words. -/
theorem dijkstra_bound (n s : UInt64) (first heads lens : Array UInt64) :
    compiled.dijkstra.bound (n, s, first, heads, lens) =
      if s < n then
        2 * Verified.blockCost n.toNat + 2 * Verified.blockCost first[n.toNat]!.toNat
      else Verified.blockCost n.toNat := by
  rw [compiled.dijkstra.bound_eq]
  split <;> omega

#print axioms dijkstra_call
#print axioms dijkstra_spec
#print axioms dijkstra_bound

end Library.Graphs.Dijkstra
