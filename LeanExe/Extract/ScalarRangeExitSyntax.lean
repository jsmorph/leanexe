import LeanExe.Source.ScalarRangeExitSyntax
import LeanExe.Extract.ScalarRangeCount

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

structure ScalarRangeExitView where
  indexType : Range.Exit.IndexType
  first : Range.Exit.First
  count : Range.Exit.Count
  initial : Lean.Expr
  indexName : Lean.Name
  accumulatorName : Lean.Name
  indexBi : Lean.BinderInfo
  accumulatorBi : Lean.BinderInfo
  body : Lean.Expr

def ScalarRangeExitView.source (view : ScalarRangeExitView) : Lean.Expr :=
  Range.Exit.call view.indexType view.first view.count view.initial view.indexName view.accumulatorName
    view.indexBi view.accumulatorBi view.body

/-- Admit only the original standard range head and concrete unit-step range.
The Expr equality instance checks complete syntax and instance evidence. -/
def scalarRangeExit? : Lean.Expr → Option ScalarRangeExitView
  | .app (.app (.app head
      (.app (.app (.app (.app (.const ``Std.Legacy.Range.mk []) start) stop) step) positive)) initial)
      (.lam indexName indexType
        (.lam accumulatorName (.const ``UInt64 []) body accumulatorBi) indexBi) =>
      if exactSyntax : indexType.consumeMData = .const ``Nat [] ∧ head = Range.Exit.head indexType ∧ step = Range.natLiteral 1 ∧
          positive = .const ``Nat.zero_lt_one [] then
        do
          let first ← scalarRangeFirst? start
          let count ← scalarRangeCount? stop
          pure { indexType := ⟨indexType, exactSyntax.1⟩, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
      else none
  | _ => none

theorem scalarRangeExit_accepts (view : ScalarRangeExitView) :
    scalarRangeExit? view.source = some view := by
  rcases view with ⟨⟨indexType, isNat⟩, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body⟩
  have firstAccepted : scalarRangeFirst? (Range.natLiteral first.number) = some first := scalarRangeFirst_accepts first
  simp [ScalarRangeExitView.source, Range.Exit.call, Range.Exit.Count.range, Lean.mkAppN, Lean.mkApp, scalarRangeExit?, isNat, scalarRangeCount_accepts, firstAccepted]

theorem scalarRangeExit_sound {source : Lean.Expr} {view : ScalarRangeExitView}
    (matched : scalarRangeExit? source = some view) : source = view.source := by
  unfold scalarRangeExit? at matched
  split at matched
  · split at matched
    · rename_i exactSyntax
      obtain ⟨isNat, rfl, rfl, rfl⟩ := exactSyntax
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at matched
      obtain ⟨first, recognizedFirst, count, recognized, rfl⟩ := matched
      have sameFirst := scalarRangeFirst_sound recognizedFirst
      have same := scalarRangeCount_sound recognized
      subst_vars
      rfl
    · contradiction
  · contradiction

end LeanExe.Extract.Core
