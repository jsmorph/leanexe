import Library.Trees.Avl.Proof
import Library.Trees.Avl.Reflected
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of balanced tree search and insertion.  By the compiler's rules,
which the verified compiler's manual states, the compiler translates the tail recursions of
`search`, `ascend`, and `descend` into loops, so no theorem of the module has a call-depth premise.
`search` borrows its tree, and `insert` consumes its tree, which the caller hands over as
`Moved AvlTree`.  The generated bound charges no block for a node that a step or a rotation
rebuilds from a node it takes apart, and 80 bytes for the new node, but no theorem relates the
blocks of the result to those of the argument.  `search_implements` and `insert_implements`
compose the generated `trapFree` theorems with `search_eq` and `insert_eq`. -/

namespace Library.Trees.Avl

open Wasm LeanExe.Pipeline

set_option maxHeartbeats 1000000 in
verified_compile compiled := [search, rotateRight, rotateLeft, ascend, descend, insert]

theorem search_export :
    ({ name := "search", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem insert_export :
    ({ name := "insert", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `search`, called with a key `x` and a borrowed tree `t`, from a heap with
the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.search.bound`,
returns without a trap whether Algorithm A's search succeeds, and raises `top` by at most the
bound. -/
theorem search_implements :
    ImplementsA false compiled.module 2 (fun x : UInt64 × AvlTree => searchA x.1 x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.search.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.search.bound x) :=
  Verified.implementsA_congr compiled.search.trapFree fun _ _ _ x _ => search_eq x.1 x.2

/-- Function 7, the export `insert`, called with a key `x` and a tree `t` that the caller hands
over, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for
`compiled.insert.bound`, returns without a trap the owned tree of Algorithm A, and raises `top` by
at most the bound. -/
theorem insert_implements :
    ImplementsA false compiled.module 7
      (fun x : UInt64 × Moved AvlTree => (algorithmA x.1 x.2.val).2)
      (fun x heap store => heap.Within store compiled.module (compiled.insert.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.insert.bound x) :=
  Verified.implementsA_congr compiled.insert.trapFree fun _ _ _ x _ => insert_eq x.1 x.2.val

theorem search_bound (x : UInt64) (t : AvlTree) : compiled.search.bound (x, t) = 0 := by
  rw [compiled.search.bound_eq]
  convert Verified.Tail.costAt_zero compiled.search.step _ _ using 2
  funext state
  rcases state with ⟨_, p⟩
  cases p <;> rfl

theorem rotateRight_bound (s : AvlTree) : compiled.rotateRight.bound { val := s } = 0 := by
  rw [compiled.rotateRight.bound_eq]
  rcases s with _ | ⟨t, _, _, _⟩
  · rfl
  · rcases t with _ | ⟨_, _, _, tr⟩
    · rfl
    · dsimp only
      split
      · rfl
      · cases tr <;> rfl

theorem rotateLeft_bound (s : AvlTree) : compiled.rotateLeft.bound { val := s } = 0 := by
  rw [compiled.rotateLeft.bound_eq]
  rcases s with _ | ⟨_, _, _, t⟩
  · rfl
  · rcases t with _ | ⟨tl, _, _, _⟩
    · rfl
    · dsimp only
      split
      · rfl
      · cases tl <;> rfl

theorem ascend_bound (x : UInt64) (grew : Bool) (path t : AvlTree) :
    compiled.ascend.bound (x, grew, { val := path }, { val := t }) = 0 := by
  rw [compiled.ascend.bound_eq]
  convert Verified.Tail.costAt_zero compiled.ascend.step _ _ using 2
  funext state
  rcases state with ⟨_, _, p, _⟩
  cases p
  · rfl
  · simp [rotateRight_bound, rotateLeft_bound]

/-- The generated bound of `descend` is 80 bytes, one node's block, when the search fails and 0
when it succeeds. -/
theorem descend_bound (x : UInt64) (path t : AvlTree) :
    compiled.descend.bound (x, { val := path }, { val := t }) =
      if searchA x t then 0 else 80 := by
  induction t generalizing path with
  | leaf =>
    rw [compiled.descend.bound_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.descend.wellFounded h)]
    simp [compiled.descend.step, ascend_bound, searchA]
  | node l k b r ihl ihr =>
    rw [compiled.descend.bound_eq, Verified.Tail.costAt_rank_eq _ _
      (fun _ _ h => Verified.Tail.rank_lt compiled.descend.wellFounded h)]
    by_cases h : x < k
    · have hs : compiled.descend.step (x, path, .node l k b r) =
          .inl (x, .node path k b r, l) := by
        simp [compiled.descend.step, h]
      rw [hs, Sum.elim_inl, ← compiled.descend.bound_eq, ihl]
      simp [h, searchA]
    · by_cases h' : k < x
      · have hs : compiled.descend.step (x, path, .node l k b r) =
            .inl (x, .node l k b path, r) := by
          simp [compiled.descend.step, h, h']
        rw [hs, Sum.elim_inl, ← compiled.descend.bound_eq, ihr]
        simp [h, h', searchA]
      · simp [compiled.descend.step, h, h', searchA, ascend_bound]

/-- The generated bound of `insert`, by which a call can raise `top`, is 80 bytes, one node's
block, when the search fails and 0 when it succeeds. -/
theorem insert_bound (x : UInt64) (t : AvlTree) :
    compiled.insert.bound (x, { val := t }) = if searchA x t then 0 else 80 := by
  rw [compiled.insert.bound_eq, descend_bound]

#print axioms search_implements
#print axioms insert_implements
#print axioms insert_bound

end Library.Trees.Avl
