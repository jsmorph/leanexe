import Library.Graphs.WeightedUnionFind.Proof
import Verified.Reflect.Command
import Verified.Call

/-! The verified compiler's module of equivalence classes with path compression and union by size.
By the compiler's rules, which the verified compiler's manual states, the compiler translates the
tail recursions of `root` and `compress` and the loops of `forest` and `classes` into loops, so no
theorem of the module has a call-depth premise, and `unite` updates the parent links and the sizes
in their arrays, which are owned at their last use.  The module builds four arrays of `n` words: the
parent links, the sizes, the least element recorded at each root, and the result.  `classes_call`
states the call of the export from the generated `compiled.classes.trapFree`: it returns the array
of the Lean function `classes`.  `classes_spec` of the proof states that, for arrays of fewer than
`2^64` words, which every array that the representation of a call holds has, that array labels each
element below `n` with the least element of its class, and no theorem combines the two. -/

namespace Library.Graphs.WeightedUnionFind

open Wasm LeanExe.Pipeline
open Library.Graphs.UnionFind (root)

verified_compile compiled := [root, compress, unite, forest, classes]

theorem classes_export :
    ({ name := "classes", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 6, the export `classes`, called with a count `n` and two lent arrays from a ready
store with room for `compiled.classes.bound` bytes, returns without a trap the owned array
`classes n js ks` and leaves a ready store. -/
theorem classes_call :
    Verified.Call compiled.module compiled.tables 6 (fun x => classes x.1 x.2.1 x.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.classes.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.classes.bound x) :=
  Verified.ImplementsTables.call (.ofA compiled.classes.trapFree) compiled.tables nofun

/-- The generated bound is four blocks of `n` words. -/
theorem classes_bound (n : UInt64) (js ks : Array UInt64) :
    compiled.classes.bound (n, js, ks) = 4 * Verified.blockCost n.toNat := by
  rw [compiled.classes.bound_eq, compiled.forest.bound_eq]
  omega

#print axioms classes_call
#print axioms classes_spec

end Library.Graphs.WeightedUnionFind
