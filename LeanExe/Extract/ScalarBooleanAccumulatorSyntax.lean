import LeanExe.Source.ScalarBooleanAccumulatorSyntax
import LeanExe.Extract.ScalarRangeStrideSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

structure ScalarBooleanAccumulatorView where
  indexType : Range.Exit.IndexType
  stride : Range.Exit.Stride
  first : Range.Exit.Count
  count : Range.Exit.Count
  initial : Lean.Expr
  indexName : Lean.Name
  accumulatorName : Lean.Name
  indexBi : Lean.BinderInfo
  accumulatorBi : Lean.BinderInfo
  body : Lean.Expr

def ScalarBooleanAccumulatorView.source (view : ScalarBooleanAccumulatorView) : Lean.Expr :=
  BooleanAccumulator.call view.indexType view.stride view.first view.count view.initial view.indexName view.accumulatorName
    view.indexBi view.accumulatorBi view.body

/-- Admit only the original standard range head and range with a checked positive literal stride.
The Expr equality instance checks complete syntax and instance evidence. -/
def scalarBooleanAccumulator? : Lean.Expr → Option ScalarBooleanAccumulatorView
  | .app (.app (.app head
      (.app (.app (.app (.app (.const ``Std.Legacy.Range.mk []) start) stop) step) positive)) initial)
      (.lam indexName indexType
        (.lam accumulatorName (.const ``Bool []) body accumulatorBi) indexBi) =>
      if exactSyntax : indexType.consumeMData = .const ``Nat [] ∧ head = BooleanAccumulator.head indexType then
        do
          let stride ← scalarRangeStride? step positive
          let first ← scalarRangeCount? start
          let count ← scalarRangeCount? stop
          pure { indexType := ⟨indexType, exactSyntax.1⟩, stride, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
      else none
  | _ => none

theorem scalarBooleanAccumulator_accepts (view : ScalarBooleanAccumulatorView) :
    scalarBooleanAccumulator? view.source = some view := by
  rcases view with ⟨⟨indexType, isNat⟩, stride, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body⟩
  have strideAccepted : scalarRangeStride? (Range.natLiteral stride.number) stride.evidence = some stride := scalarRangeStride_accepts stride
  simp [ScalarBooleanAccumulatorView.source, BooleanAccumulator.call, Range.Exit.Count.range, Lean.mkAppN, Lean.mkApp, scalarBooleanAccumulator?, isNat, scalarRangeCount_accepts, strideAccepted]

theorem scalarBooleanAccumulator_sound {source : Lean.Expr} {view : ScalarBooleanAccumulatorView}
    (matched : scalarBooleanAccumulator? source = some view) : source = view.source := by
  unfold scalarBooleanAccumulator? at matched
  split at matched
  · split at matched
    · rename_i exactSyntax
      obtain ⟨isNat, rfl⟩ := exactSyntax
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at matched
      obtain ⟨stride, recognizedStride, first, recognizedFirst, count, recognized, rfl⟩ := matched
      obtain ⟨sameStride, sameEvidence⟩ := scalarRangeStride_sound recognizedStride
      have sameFirst := scalarRangeCount_sound recognizedFirst
      have same := scalarRangeCount_sound recognized
      subst_vars
      rfl
    · contradiction
  · contradiction

end LeanExe.Extract.Core
