import Project.Smalltalk.Traversal
import Project.Smalltalk.Loops
import Init.Data.List.TakeDrop

namespace Project.Smalltalk.CallChain
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
open Project.Smalltalk.Traversal Project.Smalltalk.Loops

def next (s : Array UInt64) (target : UInt64) (st : UInt64 × Bool) : UInt64 × Bool :=
  (if kind s st.1 == 5 then field s st.1 4 else 0,
    st.2 || (st.1 != 0 && st.1 == target))

theorem onChain_eq (s : Array UInt64) (target : UInt64) :
    onChain s target = (applyN (next s target) (read s 14).toNat (read s 2, false)).2 := by
  exact congrArg Prod.snd (loop_constant (next s target) (read s 14) (read s 2, false))

theorem visit_path {s : Array UInt64} {head : UInt64} {nodes : List UInt64}
    (path : Path s 5 4 head nodes) (target : UInt64) (flag : Bool) (n : Nat) :
    (applyN (next s target) n (head, flag)).2 = (flag || decide (target ∈ nodes.take n)) := by
  induction n generalizing head nodes flag with
  | zero => simp [applyN]
  | succ n ih =>
    rw [applyN]
    cases path with
    | nil =>
      simp only [next, kind, BEq.rfl, Bool.true_or, ite_true]
      simpa using ih Path.nil flag
    | @cons head tail rest tag link path =>
      have nonzero : head ≠ 0 := by
        intro zero
        rw [zero] at tag
        simp [kind] at tag
      simp only [next, tag, BEq.rfl, ite_true, link]
      rw [ih path]
      have nonzeroBool : (head != 0) = true := bne_iff_ne.mpr nonzero
      have sameBool : (head == target) = decide (target = head) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, decide_eq_true_eq]
        exact eq_comm
      simp only [List.take_succ_cons, List.mem_cons, Bool.decide_or,
        nonzeroBool, Bool.true_and, sameBool, Bool.or_assoc]

/-- The concrete bounded call-chain scan reports exactly membership in the
represented caller chain, provided that chain fits within capacity. -/
theorem onChain_correct {s : Array UInt64} {nodes : List UInt64}
    (path : Path s 5 4 (read s 2) nodes) (bound : nodes.length ≤ (read s 14).toNat)
    (target : UInt64) : onChain s target = decide (target ∈ nodes) := by
  rw [onChain_eq, visit_path path, List.take_of_length_le bound]
  rfl

end Project.Smalltalk.CallChain
