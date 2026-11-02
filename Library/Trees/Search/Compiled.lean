import Library.Trees.Search.Proof
import Library.Trees.WordTree.Reflected
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of tree search and insertion.  The compiler translates the tail
recursions of `search`, `ascend`, and `descend` into loops, so no theorem of the module has a
call-depth premise.  `search` borrows its tree, and `insert` consumes its tree, which the caller
hands over as `Moved KeyTree`.  By the compiler's ownership rules, each step of `descend` and
`ascend` rebuilds the node that it takes apart in that node's block, and the generated bound charges
only the new node's block of 72 bytes, but no theorem relates the blocks of the result to those of
the argument.  `search_implements` and `insert_implements` compose the generated `trapFree` theorems
with `search_eq` and `insert_eq`. -/

namespace Library.Trees.Search

open Wasm LeanExe.Pipeline
open Library.Trees.WordTree

verified_compile compiled := [search, ascend, descend, insert]

theorem search_export :
    ({ name := "search", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem insert_export :
    ({ name := "insert", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `search`, called with a key `x` and a borrowed tree `t`, from a heap
with room for `compiled.search.bound`, returns without a trap whether Algorithm T's search
succeeds, and raises `top` by at most the bound. -/
theorem search_implements :
    ImplementsA false compiled.module 2 (fun x : UInt64 × KeyTree => (algorithmT x.1 x.2).1)
      (fun x heap store => heap.Within store compiled.module (compiled.search.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.search.bound x) :=
  Verified.implementsA_congr compiled.search.trapFree fun _ _ _ x _ => search_eq x.1 x.2

/-- Function 5, the export `insert`, called with a key `x` and a tree `t` that the caller hands
over, from a heap with room for `compiled.insert.bound`, returns without a trap the owned tree of
Algorithm T, and raises `top` by at most the bound. -/
theorem insert_implements :
    ImplementsA false compiled.module 5
      (fun x : UInt64 × Moved KeyTree => (algorithmT x.1 x.2.val).2)
      (fun x heap store => heap.Within store compiled.module (compiled.insert.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.insert.bound x) :=
  Verified.implementsA_congr compiled.insert.trapFree fun _ _ _ x _ => insert_eq x.1 x.2.val

theorem search_bound (x : UInt64) (t : KeyTree) : compiled.search.bound (x, t) = 0 := by
  rw [compiled.search.bound_eq]
  convert Verified.Tail.costAt_zero compiled.search.step _ _ using 2
  funext state
  rcases state with ⟨_, p⟩
  cases p <;> rfl

theorem ascend_bound (x : UInt64) (path t : KeyTree) :
    compiled.ascend.bound (x, { val := path }, { val := t }) = 0 := by
  rw [compiled.ascend.bound_eq]
  convert Verified.Tail.costAt_zero compiled.ascend.step _ _ using 2
  funext state
  rcases state with ⟨_, p, _⟩
  cases p <;> rfl

/-- The generated bound of `descend` is 72 bytes, one node's block, when the search fails and 0
when it succeeds. -/
theorem descend_bound (x : UInt64) (path t : KeyTree) :
    compiled.descend.bound (x, { val := path }, { val := t }) =
      if (algorithmT x t).1 then 0 else 72 := by
  induction t generalizing path with
  | leaf =>
    rw [compiled.descend.bound_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.descend.wellFounded h)]
    simp [compiled.descend.step, ascend_bound, algorithmT]
  | node l k r ihl ihr =>
    rw [compiled.descend.bound_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.descend.wellFounded h)]
    by_cases h : x < k
    · have hs : compiled.descend.step (x, path, .node l k r) = .inl (x, .node path k r, l) := by
        simp [compiled.descend.step, h]
      rw [hs, Sum.elim_inl, ← compiled.descend.bound_eq, ihl]
      simp [h, algorithmT]
    · by_cases h' : k < x
      · have hs : compiled.descend.step (x, path, .node l k r) = .inl (x, .node l k path, r) := by
          simp [compiled.descend.step, h, h']
        rw [hs, Sum.elim_inl, ← compiled.descend.bound_eq, ihr]
        simp [h, h', algorithmT]
      · simp [compiled.descend.step, h, h', algorithmT, ascend_bound]

/-- The generated bound of `insert`, by which a call can raise `top`, is 72 bytes, one node's
block, when the search fails and 0 when it succeeds. -/
theorem insert_bound (x : UInt64) (t : KeyTree) :
    compiled.insert.bound (x, { val := t }) = if (algorithmT x t).1 then 0 else 72 := by
  rw [compiled.insert.bound_eq, descend_bound]

#print axioms search_implements
#print axioms insert_implements
#print axioms insert_bound

end Library.Trees.Search
