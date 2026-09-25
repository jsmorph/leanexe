import LeanExe.IR.ScalarSemantics
import LeanExe.Source.ScalarRangeExit

namespace LeanExe.IR

/-- Finite range execution with an early-exit step. On done, the body places
the control index at the bound; on yield, it advances by one. In either case
the produced accumulator is preserved, and no step follows done. -/
theorem bounded_while_exit_execution (condition : Cond) (body : Stmt)
    (step : Nat → UInt64 → ForInStep UInt64) (bound : Nat)
    (Inv : Nat → UInt64 → ScalarStore → Prop)
    (stop : ∀ value store, Inv bound value store → condition.ScalarEval store false store)
    (advance : ∀ index, index < bound → ∀ value store, Inv index value store →
      ∃ afterCondition afterBody,
        condition.ScalarEval store true afterCondition ∧
        body.ScalarEval afterCondition afterBody ∧
        match step index value with
        | .done next => Inv bound next afterBody
        | .yield next => Inv (index + 1) next afterBody)
    (remaining index : Nat) (endIndex : index + remaining = bound)
    (value : UInt64) (store : ScalarStore) (initial : Inv index value store) :
    ∃ finalStore, (Stmt.while condition body).ScalarEval store finalStore ∧
      Inv bound (LeanExe.Source.Scalar.Range.Exit.iterate step remaining index value) finalStore := by
  induction remaining generalizing index value store with
  | zero =>
    have same : index = bound := by omega
    subst index
    exact ⟨store, .whileFalse (stop value store initial), initial⟩
  | succ remaining ih =>
    obtain ⟨afterCondition, afterBody, tested, stepped, next⟩ :=
      advance index (by omega) value store initial
    cases result : step index value with
    | done nextValue =>
      simp only [result] at next
      refine ⟨afterBody, .whileTrue tested stepped (.whileFalse (stop nextValue afterBody next)), ?_⟩
      simpa [LeanExe.Source.Scalar.Range.Exit.iterate, result] using next
    | yield nextValue =>
      simp only [result] at next
      obtain ⟨finalStore, rest, final⟩ := ih (index + 1) (by omega) nextValue afterBody next
      refine ⟨finalStore, .whileTrue tested stepped rest, ?_⟩
      simpa [LeanExe.Source.Scalar.Range.Exit.iterate, result] using final

end LeanExe.IR
