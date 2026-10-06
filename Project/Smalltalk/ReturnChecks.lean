import Project.Smalltalk.Home
import Project.Smalltalk.Frame

namespace Project.Smalltalk.ReturnChecks
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
open Project.Smalltalk.Traversal Project.Smalltalk.CallChain

def selected (p s : Array UInt64) (nonlocal : UInt64) : UInt64 :=
  if nonlocal = 0 then read s 2 else home p s (read s 2)

theorem ret_eq (p s : Array UInt64) (nonlocal : UInt64) :
    ret p s nonlocal =
      if kind s (field s (read s 2) 7) != 7 then fail s 4 else
      if kind s (selected p s nonlocal) != 5 || field s (selected p s nonlocal) 3 == dead ||
          !onChain s (selected p s nonlocal) then fail s 7 else
      returnReserved s (selected p s nonlocal) (field s (selected p s nonlocal) 4)
        (field s (field s (read s 2) 7) 2) := by
  simp only [ret, selected, beq_iff_eq]
  rfl

theorem ret_underflow (p s : Array UInt64) (nonlocal : UInt64)
    (empty : kind s (field s (read s 2) 7) ≠ 7) : ret p s nonlocal = fail s 4 := by
  rw [ret_eq]
  have test : (kind s (field s (read s 2) 7) != 7) = true := bne_iff_ne.mpr empty
  rw [test]
  rfl

theorem ret_dead (p s : Array UInt64) (nonlocal : UInt64)
    (stack : kind s (field s (read s 2) 7) = 7)
    (deadHome : field s (selected p s nonlocal) 3 = dead) : ret p s nonlocal = fail s 7 := by
  rw [ret_eq]
  have test : (kind s (field s (read s 2) 7) != 7) = false := bne_eq_false_iff_eq.mpr stack
  simp only [test, Bool.false_eq_true, ite_false, deadHome, BEq.rfl, Bool.or_true, Bool.true_or, ite_true]

theorem ret_absent {p s : Array UInt64} {nodes : List UInt64}
    (path : Path s 5 4 (read s 2) nodes) (bound : nodes.length ≤ (read s 14).toNat)
    (nonlocal : UInt64) (stack : kind s (field s (read s 2) 7) = 7)
    (absent : selected p s nonlocal ∉ nodes) : ret p s nonlocal = fail s 7 := by
  have inactive : onChain s (selected p s nonlocal) = false := by
    rw [onChain_correct path bound]
    exact decide_eq_false absent
  rw [ret_eq]
  have test : (kind s (field s (read s 2) 7) != 7) = false := bne_eq_false_iff_eq.mpr stack
  simp only [test, Bool.false_eq_true, ite_false, inactive, Bool.not_false, Bool.or_true, ite_true]

theorem ret_accepted {p s : Array UInt64} {nodes : List UInt64}
    (path : Path s 5 4 (read s 2) nodes) (bound : nodes.length ≤ (read s 14).toNat)
    (nonlocal : UInt64) (stack : kind s (field s (read s 2) 7) = 7)
    (tag : kind s (selected p s nonlocal) = 5)
    (live : field s (selected p s nonlocal) 3 ≠ dead)
    (member : selected p s nonlocal ∈ nodes) :
    ret p s nonlocal = returnReserved s (selected p s nonlocal)
      (field s (selected p s nonlocal) 4) (field s (field s (read s 2) 7) 2) := by
  have active : onChain s (selected p s nonlocal) = true := by
    rw [onChain_correct path bound]
    exact decide_eq_true member
  rw [ret_eq]
  have test : (kind s (field s (read s 2) 7) != 7) = false := bne_eq_false_iff_eq.mpr stack
  have pc : (field s (selected p s nonlocal) 3 == dead) = false := beq_eq_false_iff_ne.mpr live
  simp only [test, Bool.false_eq_true, ite_false, tag, bne_self_eq_false, pc, Bool.false_or,
    active, Bool.not_true, Bool.false_eq_true, ite_false]

end Project.Smalltalk.ReturnChecks
