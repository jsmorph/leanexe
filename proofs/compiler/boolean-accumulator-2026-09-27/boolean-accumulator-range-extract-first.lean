import LeanExe.Source.ScalarBooleanAccumulator
import LeanExe.Extract.ScalarBooleanAccumulatorSyntax
import LeanExe.Extract.ScalarBooleanStep
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Extract.ScalarRangeExitInvariant

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanAccumulatorBinding (slot : Nat) : ScalarBinding :=
  .boolean (guardWord (lowerComparison .bne (.local slot) (.u64 0)))

/-- Boolean states reuse the word loop after normalizing the accumulator read. -/
def extractScalarBooleanAccumulatorWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan := do
  let view ← scalarBooleanAccumulator? source
  let first ← extractScalarExprWith locals view.first.scalar
  let count ← extractScalarExprWith locals view.count.scalar
  let initial ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) view.initial)
  let code ← extractBooleanStepWith
    (booleanAccumulatorBinding slot ::
      .natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1)))) :: locals) view.body
  pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count),
    initial, step := code.value, done := code.done, result := .local slot }

theorem extractScalarBooleanAccumulatorWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarBooleanAccumulatorView) :
    extractScalarBooleanAccumulatorWith locals slot view.source = (do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) view.initial)
      let code ← extractBooleanStepWith
        (booleanAccumulatorBinding slot ::
          .natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1)))) :: locals) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count),
        initial, step := code.value, done := code.done, result := .local slot }) := by
  simp [extractScalarBooleanAccumulatorWith, scalarBooleanAccumulator_accepts]

theorem extractScalarBooleanAccumulatorWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanAccumulatorWith locals slot source = some plan) :
    BooleanAccumulator.Supported (locals.map ScalarBinding.kind) source := by
  simp only [extractScalarBooleanAccumulatorWith, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨view, parsed, first, hf, count, hc, initial, hi, code, hs, rfl⟩ := compiled
  rw [scalarBooleanAccumulator_sound parsed]
  exact .range view.indexType view.stride
    (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hf))
    (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hc))
    (extractScalarExprWith_supported hi)
    (by simpa [booleanAccumulatorBinding, ScalarBinding.kind] using extractBooleanStepWith_supported hs)

theorem extractScalarBooleanAccumulatorWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanAccumulator.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types) (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanAccumulatorWith locals slot source = some plan := by
  cases supported with
  | range indexType stride first count initial step =>
    change ∃ plan, extractScalarBooleanAccumulatorWith locals slot
      ({ indexType, stride, first := _, count := _, initial := _, indexName := _, accumulatorName := _,
        indexBi := _, accumulatorBi := _, body := _ } : ScalarBooleanAccumulatorView).source = some plan
    rw [extractScalarBooleanAccumulatorWith_call]
    obtain ⟨firstIR, hf⟩ := extractScalarExprWith_accepts first.scalar locals typed total
    obtain ⟨countIR, hc⟩ := extractScalarExprWith_accepts count.scalar locals typed total
    obtain ⟨initialIR, hi⟩ := extractScalarExprWith_accepts initial locals typed total
    obtain ⟨code, hs⟩ := extractBooleanStepWith_accepts step
      (booleanAccumulatorBinding slot ::
        .natural (scalarRangeOffset firstIR (scalarRangeScale stride.number (.local (slot + 1)))) :: locals)
      (by simp [booleanAccumulatorBinding, ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨_, by simp [hf, hc, hi, hs]⟩

theorem extractScalarBooleanAccumulatorWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanAccumulatorWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  have expression {locals : List ScalarBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith locals source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled bindings
  simp only [extractScalarBooleanAccumulatorWith, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨view, parsed, first, hf, count, hc, initial, hi, code, hs, rfl⟩ := compiled
  have both := extractBooleanStepWith_invariant P literal binary choice hs (by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact choice .bne (.local slot) (.u64 0) (.u64 1) (.u64 0)
        accumulator (literal 0) (literal 1) (literal 0)
    rcases List.mem_cons.mp member with rfl | member
    · exact scalarRangeOffset_holds P binary (expression hf bindings)
        (scalarRangeScale_holds P literal binary view.stride.number index)
    · exact bindings binding member)
  exact ⟨scalarRangeTrips_holds P literal binary choice view.stride.number
    (scalarRangeDistance_holds P literal binary choice (expression hf bindings) (expression hc bindings)),
    expression hi bindings, both.1, both.2, accumulator⟩

end LeanExe.Extract.Core
