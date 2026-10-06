import Project.Smalltalk.CallChain

namespace Project.Smalltalk.Home
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
open Project.Smalltalk.Traversal Project.Smalltalk.Loops

def eligible (p s : Array UInt64) (a : UInt64) : Bool :=
  field s a 2 != 0 && methodAt p (field s a 2) 1 != 0

def firstHome (p s : Array UInt64) : List UInt64 → UInt64
  | [] => 0
  | a :: rest => if eligible p s a then a else firstHome p s rest

def next (p s : Array UInt64) (st : UInt64 × UInt64) : UInt64 × UInt64 :=
  let a := st.1
  let m := if kind s a == 5 then field s a 2 else 0
  let found := a != 0 && m != 0 && methodAt p m 1 != 0
  (if st.2 != 0 || found || a == 0 then 0 else field s a 5,
    if st.2 != 0 then st.2 else if found then a else 0)

theorem home_eq (p s : Array UInt64) (act : UInt64) :
    home p s act = (applyN (next p s) (read s 14).toNat (act, 0)).2 :=
  congrArg Prod.snd (loop_constant (next p s) (read s 14) (act, 0))

theorem found_stays (p s : Array UInt64) (a result : UInt64) (nonzero : result ≠ 0) (n : Nat) :
    (applyN (next p s) n (a, result)).2 = result := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have found : (result != 0) = true := bne_iff_ne.mpr nonzero
    simp only [applyN, next, found, Bool.true_or, ite_true]
    exact ih 0

theorem home_path {p s : Array UInt64} {head : UInt64} {nodes : List UInt64}
    (path : Path s 5 5 head nodes) (n : Nat) (bound : nodes.length ≤ n) :
    (applyN (next p s) n (head, 0)).2 = firstHome p s nodes := by
  induction n generalizing head nodes with
  | zero =>
    have empty : nodes = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst nodes
    cases path
    rfl
  | succ n ih =>
    rw [applyN]
    cases path with
    | nil =>
      simp only [next, kind, BEq.rfl, Bool.true_or, ite_true, bne_self_eq_false,
        Bool.false_and, Bool.false_or, firstHome]
      exact ih Path.nil (by simp)
    | @cons head tail rest tag link path =>
      have nonzero : head ≠ 0 := by
        intro zero
        rw [zero] at tag
        simp [kind] at tag
      by_cases hit : eligible p s head = true
      · have found : (head != 0 && field s head 2 != 0 && methodAt p (field s head 2) 1 != 0) = true := by
          simpa [nonzero, eligible] using hit
        simp only [next, tag, BEq.rfl, ite_true, bne_self_eq_false, Bool.false_or, found,
          Bool.true_or, firstHome, hit]
        exact found_stays p s 0 head nonzero n
      · have miss : eligible p s head = false := Bool.eq_false_iff.mpr hit
        have found : (head != 0 && field s head 2 != 0 && methodAt p (field s head 2) 1 != 0) = false := by
          simpa [nonzero, eligible] using miss
        simp only [next, tag, BEq.rfl, ite_true, bne_self_eq_false, Bool.false_or, found,
          Bool.false_or, beq_iff_eq, nonzero, ite_false, link, firstHome, miss]
        exact ih path (by simp only [List.length_cons] at bound; omega)

/-- Home is the first enclosing activation whose method identifier and
selector are nonzero. This search does not test whether that frame is live. -/
theorem home_correct {p s : Array UInt64} {act : UInt64} {nodes : List UInt64}
    (path : Path s 5 5 act nodes) (bound : nodes.length ≤ (read s 14).toNat) :
    home p s act = firstHome p s nodes := by
  rw [home_eq]
  exact home_path path _ bound

end Project.Smalltalk.Home
