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
  pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }

theorem extractScalarBooleanAccumulatorWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarBooleanAccumulatorView) :
    extractScalarBooleanAccumulatorWith locals slot view.source = (do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) view.initial)
      let code ← extractBooleanStepWith
        (booleanAccumulatorBinding slot ::
          .natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1)))) :: locals) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }) := by
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
      ({ indexType, stride, first := _, count := _, initial := _, indexName := _, accumulatorName := _, indexBi := _, accumulatorBi := _, body := _ } : ScalarBooleanAccumulatorView).source = some plan
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
    exact ⟨{ count := scalarRangeTrips stride.number (scalarRangeDistance firstIR countIR), initial := initialIR, step := code.value, done := code.done, result := .local slot },
      by simp [hf, hc, hi, hs]⟩

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

theorem extractScalarBooleanAccumulatorWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} {values : List Value} {saved : List UInt64}
    (compiled : extractScalarBooleanAccumulatorWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved) :
    ∃ flag, BooleanAccumulator.Eval source values flag ∧ plan.Meaning saved flag.toUInt64 := by
  classical
  simp only [extractScalarBooleanAccumulatorWith, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨view, parsed, firstIR, ef, countIR, ec, initialIR, ei, code, es, rfl⟩ := compiled
  rw [scalarBooleanAccumulator_sound parsed]
  obtain ⟨begin, sf⟩ := (extractScalarExprWith_supported ef).evaluates values typed
  obtain ⟨stop, sc⟩ := (extractScalarExprWith_supported ec).evaluates values typed
  obtain ⟨encoded, si⟩ := (extractScalarExprWith_supported ei).evaluates values typed
  obtain ⟨start, rfl⟩ := si.booleanConversion_result
  have supported := extractBooleanStepWith_supported es
  have total (index : Nat) (accumulator : Bool) :=
    supported.evaluates (.boolean accumulator :: .natural index :: values)
      (by simp [booleanAccumulatorBinding, ScalarBinding.kind, Value.kind, typed])
  let f := fun index accumulator => (total index accumulator).choose
  have distanceSmall : stop.toNat - begin.toNat < UInt64.size :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) stop.toNat_lt_size
  let countNat := Range.Exit.trips (stop.toNat - begin.toNat) view.stride.number
  let bound := UInt64.ofNat countNat
  have boundNat : bound.toNat = countNat :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Range.Exit.trips_le view.stride.positive) distanceSmall)
  let shifted := fun index accumulator => f (begin.toNat + view.stride.number * index) accumulator
  let wordStep := fun index (accumulator : UInt64) => BooleanAccumulator.encodeStep (shifted index (accumulator != 0))
  refine ⟨BooleanAccumulator.iterate shifted countNat 0 start,
    .range view.indexType view.stride (.of_scalar sf) (.of_scalar sc) si
      (fun index accumulator => (total index accumulator).choose_spec),
    bound, start.toUInt64, wordStep, ?_, ?_, ?_, ?_⟩
  · have lowered := scalarRangeTrips_correct view.stride.positive view.stride.fits
      (scalarRangeDistance_correct
        (extractScalarExprWith_correct sf ef (bindings 0 0 0 0))
        (extractScalarExprWith_correct sc ec (bindings 0 0 0 0)))
    simpa only [UInt64.toNat_ofNat_of_lt' distanceSmall] using lowered
  · exact extractScalarExprWith_correct si ei (bindings 0 0 bound 0)
  · intro index _below accumulator exitFlag
    apply extractBooleanStepWith_correct ((total (begin.toNat + view.stride.number * index) (accumulator != 0)).choose_spec) es
    apply ScalarBindingsMatch.cons
    · apply ScalarBindingsMatch.cons (bindings accumulator index bound exitFlag)
      exact scalarRangeOffset_correct (view.stride.number * index)
        (extractScalarExprWith_correct sf ef (bindings accumulator index bound exitFlag))
        (scalarRangeScale_correct view.stride.number index
          (.local (LeanExe.IR.rangeExitStore_index saved accumulator index bound exitFlag)))
    · exact guardWord_correct (lowerComparison_correct .bne
        (.local (LeanExe.IR.rangeExitStore_value saved accumulator index bound exitFlag)) .const)
  · intro exitFlag
    have encoded := BooleanAccumulator.iterate_encode shifted countNat 0 start
    change (LeanExe.IR.Expr.local saved.length).ScalarEval
      (LeanExe.IR.rangeExitStore saved (Range.Exit.iterate wordStep bound.toNat 0 start.toUInt64) bound.toNat bound exitFlag)
      (BooleanAccumulator.iterate shifted countNat 0 start).toUInt64 _
    rw [boundNat, encoded]
    exact .local (LeanExe.IR.rangeExitStore_value _ _ _ _ _)

end LeanExe.Extract.Core
