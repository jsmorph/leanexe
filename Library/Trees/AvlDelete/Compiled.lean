import Library.Trees.AvlDelete.Proof
import Library.Trees.Avl.Reflected
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of deletion from a balanced tree.  By the compiler's rules, which
the verified compiler's manual states, the compiler translates the tail recursions of `ascendDel`,
`ascendMin`, `minDel`, and `descendDel` into loops, so no theorem of the module has a call-depth
premise.  `delete` consumes its tree, which the caller moves as `Moved AvlTree`.  The
generated bound charges no block, since every node that a step or a rotation builds is rebuilt
from a node that it destructures, but no theorem relates the blocks of the result to those of the
argument.  `delete_implements` composes the generated `trapFree` theorem with `delete_eq`. -/

namespace Library.Trees.AvlDelete

open Wasm LeanExe.Pipeline
open Library.Trees.Avl (AvlTree)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [isLeaf, shrinkLeft, shrinkRight, ascendDel, ascendMin, minDel,
  descendDel, delete]

theorem delete_export :
    ({ name := "delete", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 9, the export `delete`, called with a key `x` and a tree `t` that the caller moves,
from a heap that satisfies the allocator invariant within a memory cap of at most 65,535 pages,
with the tree's blocks apart from the memory that the call reads and room for
`compiled.delete.bound`, returns without a trap the owned tree of `deleteA`, and raises `top` by at
most the bound. -/
theorem delete_implements :
    ImplementsA false compiled.module 9
      (fun x : UInt64 × Moved AvlTree => (deleteA x.1 x.2.val).2)
      (fun x heap store => heap.Within store compiled.module (compiled.delete.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.delete.bound x) :=
  Verified.implementsA_congr compiled.delete.trapFree fun _ _ _ x _ => delete_eq x.1 x.2.val

theorem isLeaf_bound (t : AvlTree) : compiled.isLeaf.bound t = 0 := by
  rw [compiled.isLeaf.bound_eq]
  cases t <;> rfl

theorem shrinkLeft_bound (s : AvlTree) : compiled.shrinkLeft.bound { val := s } = 0 := by
  rw [compiled.shrinkLeft.bound_eq]
  rcases s with _ | ⟨_, _, _, c⟩
  · rfl
  · dsimp only
    split_ifs
    · rfl
    · rfl
    · rcases c with _ | ⟨cl, _, _, _⟩
      · rfl
      · dsimp only
        split_ifs
        · rfl
        · rfl
        · cases cl <;> rfl

theorem shrinkRight_bound (s : AvlTree) : compiled.shrinkRight.bound { val := s } = 0 := by
  rw [compiled.shrinkRight.bound_eq]
  rcases s with _ | ⟨a, _, _, _⟩
  · rfl
  · dsimp only
    split_ifs
    · rfl
    · rfl
    · rcases a with _ | ⟨_, _, _, ar⟩
      · rfl
      · dsimp only
        split_ifs
        · rfl
        · rfl
        · cases ar <;> rfl

theorem ascendDel_bound (x : UInt64) (shrunk : Bool) (path t : AvlTree) :
    compiled.ascendDel.bound (x, shrunk, { val := path }, { val := t }) = 0 := by
  rw [compiled.ascendDel.bound_eq]
  convert Verified.Tail.costAt_zero compiled.ascendDel.step _ _ using 2
  funext state
  rcases state with ⟨_, _, p, _⟩
  cases p
  · rfl
  · simp [shrinkLeft_bound, shrinkRight_bound]

theorem ascendMin_bound (x s : UInt64) (shrunk : Bool) (found inner t : AvlTree) :
    compiled.ascendMin.bound (x, s, shrunk, { val := found }, { val := inner }, { val := t }) =
      0 := by
  rw [compiled.ascendMin.bound_eq]
  convert Verified.Tail.costAt_zero compiled.ascendMin.step _ _ using 2
  funext state
  rcases state with ⟨_, _, _, f, i, _⟩
  cases i
  · cases f
    · rfl
    · simp [shrinkRight_bound, ascendDel_bound]
  · simp [shrinkLeft_bound]

theorem minDel_bound (x : UInt64) (found inner t : AvlTree) :
    compiled.minDel.bound (x, { val := found }, { val := inner }, { val := t }) = 0 := by
  rw [compiled.minDel.bound_eq]
  convert Verified.Tail.costAt_zero compiled.minDel.step _ _ using 2
  funext state
  rcases state with ⟨_, _, _, t⟩
  cases t <;> simp [ascendMin_bound, isLeaf_bound]

theorem descendDel_bound (x : UInt64) (path t : AvlTree) :
    compiled.descendDel.bound (x, { val := path }, { val := t }) = 0 := by
  rw [compiled.descendDel.bound_eq]
  convert Verified.Tail.costAt_zero compiled.descendDel.step _ _ using 2
  funext state
  rcases state with ⟨_, _, t⟩
  cases t <;> simp [ascendDel_bound, minDel_bound, isLeaf_bound]

/-- The generated bound of `delete` is 0, so a call does not raise `top`. -/
theorem delete_bound (x : UInt64) (t : AvlTree) : compiled.delete.bound (x, { val := t }) = 0 := by
  rw [compiled.delete.bound_eq, descendDel_bound]

#print axioms delete_implements
#print axioms delete_bound

end Library.Trees.AvlDelete
