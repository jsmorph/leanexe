import Library.Graphs.UnionFind.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of equivalence classes.  By the compiler's rules, which the
verified compiler's manual states, the compiler translates the tail recursion of `root` and the
loops of `forest` and `classes` into loops, so no theorem of the module has a call-depth premise,
and `merge` updates the parent links in their array, which is owned at its last use.  The module
builds three arrays of `n` words: the parent links, the least element recorded at each root, and
the result.  `classes_call` states the call of the export from the generated
`compiled.classes.trapFree`: it returns the array of the Lean function `classes`.  `classes_spec` of
the proof states that, for arrays of fewer than `2^64` words, which every array in memory is, that
array labels each element below `n` with the least element of its class. -/

namespace Library.Graphs.UnionFind

open Wasm LeanExe.Pipeline

verified_compile compiled := [root, merge, forest, classes]

theorem classes_export :
    ({ name := "classes", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `classes`, called with a count `n` and two lent arrays from a ready
store with room for `compiled.classes.bound` bytes, returns without a trap the owned array
`classes n js ks` and leaves a ready store. -/
theorem classes_call :
    Verified.Call compiled.module compiled.tables 5 (fun x => classes x.1 x.2.1 x.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.classes.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.classes.bound x) :=
  Verified.ImplementsTables.call (.ofA compiled.classes.trapFree) compiled.tables nofun

/-- The generated bound is three blocks of `n` words. -/
theorem classes_bound (n : UInt64) (js ks : Array UInt64) :
    compiled.classes.bound (n, js, ks) = 3 * Verified.blockCost n.toNat := by
  rw [compiled.classes.bound_eq, compiled.forest.bound_eq]
  omega

#print axioms classes_call
#print axioms classes_spec

end Library.Graphs.UnionFind
