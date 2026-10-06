import Project.Smalltalk.Frame
import Project.Smalltalk.Loops

namespace Project.Smalltalk.Execution
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

theorem step_stopped (p s : Array UInt64) (stopped : read s 0 ≠ 0) : step p s = s := by
  simp only [step, bne_iff_ne]
  exact ite_eq_left stopped

def iterate (p : Array UInt64) : Nat → Array UInt64 → Array UInt64
  | 0, s => s
  | n + 1, s => iterate p n (step p s)

theorem iterate_stopped (p s : Array UInt64) (stopped : read s 0 ≠ 0) (n : Nat) : iterate p n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, step_stopped p s stopped, ih]

theorem run_go_eq (p s : Array UInt64) (i : UInt64) (n : Nat) :
    (LeanExe.repeatWhile.go (fun st : UInt64 × Array UInt64 => read st.2 0 == 0)
      (fun st => runNext p st.2 st.1) n (i, s)).2 = iterate p n s := by
  induction n generalizing s i with
  | zero => rfl
  | succ n ih =>
    by_cases running : read s 0 = 0
    · simp only [LeanExe.repeatWhile.go, beq_iff_eq, running, ite_true]
      exact ih (step p s) (i + 1)
    · simp only [LeanExe.repeatWhile.go, beq_iff_eq, running, ite_false]
      exact (iterate_stopped p s running (n + 1)).symm

/-- The fuelled run performs exactly the stated number of VM steps, treating
finished and error states as absorbing. This does not specify a step's meaning. -/
theorem run_eq_iterate (p s : Array UInt64) (fuel : UInt64) : run p s fuel = iterate p fuel.toNat s :=
  run_go_eq p s 0 fuel.toNat

theorem iterate_add (p s : Array UInt64) (a b : Nat) :
    iterate p (a + b) s = iterate p b (iterate p a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, iterate]
  | succ a ih =>
    rw [Nat.succ_add, iterate, ih]
    rfl

theorem run_resume (p s : Array UInt64) (a b : UInt64)
    (noWrap : a.toNat + b.toNat < 18446744073709551616) :
    run p (run p s a) b = run p s (a + b) := by
  rw [run_eq_iterate, run_eq_iterate, run_eq_iterate, UInt64.toNat_add,
    Nat.mod_eq_of_lt noWrap, iterate_add]

theorem run_stopped (p s : Array UInt64) (stopped : read s 0 ≠ 0) (fuel : UInt64) : run p s fuel = s := by
  rw [run_eq_iterate, iterate_stopped p s stopped]

end Project.Smalltalk.Execution
