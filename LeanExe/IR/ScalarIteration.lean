import LeanExe.IR.ScalarSemantics
import LeanExe.Source.ScalarRange

namespace LeanExe.IR

/-- A finite ascending loop executes exactly the source range iteration. The
invariant supplies the compiler's local-slot correspondence; no execution-fuel
bound or per-program result certificate appears in the conclusion. -/
theorem bounded_while_execution (condition : Cond) (body : Stmt)
    (step : Nat → UInt64 → UInt64) (bound : Nat)
    (Inv : Nat → UInt64 → ScalarStore → Prop)
    (stop : ∀ value store, Inv bound value store → condition.ScalarEval store false store)
    (advance : ∀ index, index < bound → ∀ value store, Inv index value store →
      ∃ afterCondition afterBody,
        condition.ScalarEval store true afterCondition ∧
        body.ScalarEval afterCondition afterBody ∧
        Inv (index + 1) (step index value) afterBody)
    (remaining index : Nat) (endIndex : index + remaining = bound)
    (value : UInt64) (store : ScalarStore) (initial : Inv index value store) :
    ∃ finalStore, (Stmt.while condition body).ScalarEval store finalStore ∧
      Inv bound (LeanExe.Source.Scalar.Range.iterate step remaining index value) finalStore := by
  induction remaining generalizing index value store with
  | zero =>
    have same : index = bound := by omega
    subst index
    exact ⟨store, .whileFalse (stop value store initial), initial⟩
  | succ remaining ih =>
    obtain ⟨afterCondition, afterBody, tested, stepped, next⟩ :=
      advance index (by omega) value store initial
    obtain ⟨finalStore, rest, result⟩ :=
      ih (index + 1) (by omega) (step index value) afterBody next
    exact ⟨finalStore, .whileTrue tested stepped rest, result⟩

end LeanExe.IR
