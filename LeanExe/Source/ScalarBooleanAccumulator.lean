import LeanExe.Source.ScalarBooleanAccumulatorSyntax
import LeanExe.Source.ScalarBooleanStep
import LeanExe.Source.ScalarRangeCount

namespace LeanExe.Source.Scalar.BooleanAccumulator

/-- A native Boolean range retains its bounds, positive stride and step scope. -/
inductive Eval : Lean.Expr → List Value → Bool → Prop where
  | range (indexType : IndexType) (stride : Stride) {stepFn : Nat → Bool → ForInStep Bool}
      (first : Range.Exit.Count.Eval firstExpr values begin) (count : Range.Exit.Count.Eval countExpr values stop)
      (initial : EvalWith (.app (.const ``Bool.toUInt64 []) initialExpr) values (Bool.toUInt64 start))
      (step : ∀ index accumulator, BooleanStep.Eval body
        (.boolean accumulator :: .natural index :: values) (stepFn index accumulator)) :
      Eval (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
        values (iterate (fun index accumulator => stepFn (begin + stride.number * index) accumulator)
          (Range.Exit.trips (stop - begin) stride.number) 0 start)

inductive Supported : List BindingKind → Lean.Expr → Prop where
  | range (indexType : IndexType) (stride : Stride)
      (first : Range.Exit.Count.Supported types firstExpr) (count : Range.Exit.Count.Supported types countExpr)
      (initial : SupportedWith types (.app (.const ``Bool.toUInt64 []) initialExpr))
      (step : BooleanStep.Supported (.boolean :: .natural :: types) body) :
      Supported types (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ flag, Eval source values flag := by
  classical
  cases supported with
  | range indexType stride first count initial step =>
    obtain ⟨begin, firstEval⟩ := first.scalar.evaluates values typed
    obtain ⟨stop, countEval⟩ := count.scalar.evaluates values typed
    obtain ⟨encoded, initialEval⟩ := initial.evaluates values typed
    obtain ⟨start, rfl⟩ := initialEval.booleanConversion_result
    have total := fun index accumulator => step.evaluates (.boolean accumulator :: .natural index :: values)
      (by simp [Value.kind, typed])
    let f := fun index accumulator => (total index accumulator).choose
    exact ⟨_, .range indexType stride (.of_scalar firstEval) (.of_scalar countEval) initialEval
      (fun index accumulator => (total index accumulator).choose_spec)⟩

end LeanExe.Source.Scalar.BooleanAccumulator
