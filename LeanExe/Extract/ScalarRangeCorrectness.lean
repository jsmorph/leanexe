import LeanExe.Extract.ScalarRange
import LeanExe.IR.ScalarRangeSlots

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar
open LeanExe.IR (rangeStore)

/-- Captured lexical values are independent of the three fresh loop locals. -/
def RangeBindingsMatch (locals : List ScalarBinding) (values : List Value)
    (saved : List UInt64) : Prop :=
  ∀ accumulator index stop, ScalarBindingsMatch locals values (rangeStore saved accumulator index stop)

theorem RangeBindingsMatch.bind {locals : List ScalarBinding} {values : List Value}
    {saved : List UInt64} {source : Lean.Expr} {target : LeanExe.IR.Expr} {value : UInt64}
    (bindings : RangeBindingsMatch locals values saved) (semantics : EvalWith source values value)
    (compiled : extractScalarExprWith locals source = some target) :
    RangeBindingsMatch (.word target :: locals) (.word value :: values) saved := by
  intro accumulator index stop
  exact (bindings accumulator index stop).cons
    (extractScalarExprWith_correct semantics compiled (bindings accumulator index stop))

private theorem total_word_cons {locals : List ScalarBinding}
    (total : ∀ binding ∈ locals, binding.Total) (expression : LeanExe.IR.Expr) :
    ∀ binding ∈ ScalarBinding.word expression :: locals, binding.Total := by
  intro binding member
  rcases List.mem_cons.mp member with rfl | member
  · trivial
  · exact total binding member

/-- Internal loop computation facts, derived from extraction below. These are
not inputs to the public source compiler correctness theorem. -/
def ScalarRangePlan.Meaning (plan : ScalarRangePlan) (saved : List UInt64) (value : UInt64) : Prop :=
  ∃ (stop start : UInt64) (step : Nat → UInt64 → UInt64),
    plan.count.ScalarEval (rangeStore saved 0 0 0) stop (rangeStore saved 0 0 0) ∧
    plan.initial.ScalarEval (rangeStore saved 0 0 stop) start (rangeStore saved 0 0 stop) ∧
    (∀ index, index < stop.toNat → ∀ accumulator,
      plan.step.ScalarEval (rangeStore saved accumulator index stop) (step index accumulator)
        (rangeStore saved accumulator index stop)) ∧
    plan.result.ScalarEval (rangeStore saved (Range.iterate step stop.toNat 0 start) stop.toNat stop) value
      (rangeStore saved (Range.iterate step stop.toNat 0 start) stop.toNat stop)

theorem scalarRange_correct_of_supported {types : List BindingKind} {source : Lean.Expr}
    (supported : RangeSupportedWith types source) (saved : List UInt64)
    {locals : List ScalarBinding} {plan : ScalarRangePlan} {values : List Value}
    (compiled : extractScalarRangeWith locals saved.length source = some plan)
    (localsTyped : locals.map ScalarBinding.kind = types) (valuesTyped : values.map Value.kind = types)
    (bindings : RangeBindingsMatch locals values saved)
    (totalBindings : ∀ binding ∈ locals, binding.Total) :
    ∃ value, EvalWith source values value ∧ plan.Meaning saved value := by
  classical
  induction supported generalizing locals plan values with
  | @range types count initial body scalar indexName accumulatorName indexBi accumulatorBi hc hi hy hs =>
    change extractScalarRangeWith locals saved.length
      ({ count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body } : ScalarRangeView).source = some plan at compiled
    rw [extractScalarRangeWith_call] at compiled
    rw [scalarYield_accepts hy] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨countIR, ec, initialIR, ei, _, rfl, stepIR, es, rfl⟩ := compiled
    obtain ⟨stop, sc⟩ := hc.evaluates values valuesTyped
    obtain ⟨start, si⟩ := hi.evaluates values valuesTyped
    have total (index : Nat) (accumulator : UInt64) :=
      hs.evaluates (.word accumulator :: .natural index :: values) (by simp [Value.kind, valuesTyped])
    let f := fun index accumulator => (total index accumulator).choose
    refine ⟨Range.iterate f stop.toNat 0 start,
      .range sc si hy (fun index accumulator => (total index accumulator).choose_spec),
      stop, start, f, ?_, ?_, ?_, ?_⟩
    · exact extractScalarExprWith_correct sc ec (bindings 0 0 0)
    · exact extractScalarExprWith_correct si ei (bindings 0 0 stop)
    · intro index below accumulator
      apply extractScalarExprWith_correct ((total index accumulator).choose_spec) es
      apply ScalarBindingsMatch.cons
      · apply ScalarBindingsMatch.cons (bindings accumulator index stop)
        exact LeanExe.IR.Expr.ScalarEval.local (LeanExe.IR.rangeStore_index saved accumulator index stop)
      · exact LeanExe.IR.Expr.ScalarEval.local (LeanExe.IR.rangeStore_value saved accumulator index stop)
    · exact .local (LeanExe.IR.rangeStore_value _ _ _ _)
  | letE sourceValue _ ih =>
    rw [extractScalarRangeWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih hp (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .letE hx hy, result⟩
  | idRun type _ ih =>
    rw [extractScalarRangeWith_idRun] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idRun type hv, result⟩
  | idPure type _ ih =>
    rw [extractScalarRangeWith_idPure] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idPure type hv, result⟩
  | bindRight input output sourceValue _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts sourceValue locals localsTyped totalBindings
    rw [extractScalarRangeWith_idBind, hb] at compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih compiled (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .idBind input output hx hy, result⟩
  | bindLeft input output sourceValue sourceBody ih =>
    rw [extractScalarRangeWith_idBind, rangeSupported_excludes_pure sourceValue] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, resultIR, hr, rfl⟩ := compiled
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      ih hb localsTyped valuesTyped bindings totalBindings
    obtain ⟨y, hy⟩ := sourceBody.evaluates (.word x :: values) (by simp [Value.kind, valuesTyped])
    refine ⟨y, .idBind input output hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.iterate step stop.toNat 0 start) stop.toNat stop).cons resultEval)
  | metadata _ ih =>
    rw [extractScalarRangeWith_metadata] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .metadata hv, result⟩

/-- The semantic loop facts follow from successful extraction of the original
source, for every matching captured environment. -/
theorem extractScalarRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangePlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, EvalWith source values value ∧ plan.Meaning saved value :=
  scalarRange_correct_of_supported (extractScalarRangeWith_supported compiled) saved
    compiled rfl typed bindings total

/-- The extracted setup, dynamic loop, result assignment and scalar ABI execute
with the source value. All iteration premises were derived by the extractor. -/
theorem ScalarRangePlan.Meaning.func_correct {plan : ScalarRangePlan} {args : List UInt64}
    {value : UInt64} (meaning : plan.Meaning args value)
    (name : Lean.Name) (exportName : Option String) :
    (plan.func name exportName args.length).ScalarEval args value := by
  obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := meaning
  have countWrite : (rangeStore args 0 0 0).write (args.length + 2) stop =
      some (rangeStore args 0 0 stop) := by
    simpa [rangeStore] using LeanExe.IR.write_suffix args [0, 0, 0] 2 stop (by simp)
  have loopEval := LeanExe.IR.range_while_execution args start stop plan.step step stepEval
  have bodyEval : plan.body args.length |>.ScalarEval (rangeStore args 0 0 0)
      (rangeStore args value stop.toNat stop) := by
    exact .seq (.assign countEval countWrite)
      (.seq (.assign initialEval (LeanExe.IR.rangeStore_write_value args 0 start 0 stop))
        (.seq (.assign .const (LeanExe.IR.rangeStore_write_index args start 0 0 stop))
          (.seq loopEval (.assign resultEval (LeanExe.IR.rangeStore_write_value args _ value stop.toNat stop)))))
  refine .run (afterBody := rangeStore args value stop.toNat stop)
    (afterResult := rangeStore args value stop.toNat stop) rfl (by simp [ScalarRangePlan.func]) ?_ rfl ?_
  · simpa [ScalarRangePlan.func, rangeStore] using bodyEval
  · exact .local (LeanExe.IR.rangeStore_value args value stop.toNat stop)

end LeanExe.Extract.Core
