import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarStepCorrectness

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar
open LeanExe.IR (rangeExitStore)

/-- Captured lexical values are independent of the four fresh loop locals. -/
def RangeExitBindingsMatch (locals : List ScalarBinding) (values : List Value)
    (saved : List UInt64) : Prop :=
  ∀ accumulator index stop flag, ScalarBindingsMatch locals values (rangeExitStore saved accumulator index stop flag)

theorem RangeExitBindingsMatch.bind {locals : List ScalarBinding} {values : List Value}
    {saved : List UInt64} {source : Lean.Expr} {target : LeanExe.IR.Expr} {value : UInt64}
    (bindings : RangeExitBindingsMatch locals values saved) (semantics : EvalWith source values value)
    (compiled : extractScalarExprWith locals source = some target) :
    RangeExitBindingsMatch (.word target :: locals) (.word value :: values) saved := by
  intro accumulator index stop flag
  exact (bindings accumulator index stop flag).cons
    (extractScalarExprWith_correct semantics compiled (bindings accumulator index stop flag))

private theorem total_word_cons {locals : List ScalarBinding}
    (total : ∀ binding ∈ locals, binding.Total) (expression : LeanExe.IR.Expr) :
    ∀ binding ∈ ScalarBinding.word expression :: locals, binding.Total := by
  intro binding member
  rcases List.mem_cons.mp member with rfl | member
  · trivial
  · exact total binding member

theorem ScalarBindingsMatch.step {locals : List ScalarBinding} {values : List Value}
    {store : LeanExe.IR.ScalarStore} (bindings : ScalarBindingsMatch locals values store) :
    ScalarStepBindingsMatch (locals.map ScalarStepBinding.scalar) (values.map Step.Value.scalar) store := by
  intro index binding value hb hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hb hv
  obtain ⟨originalBinding, foundBinding, rfl⟩ := hb
  obtain ⟨originalValue, foundValue, rfl⟩ := hv
  exact bindings index originalBinding originalValue foundBinding foundValue

/-- Internal computation facts derived from whole-range extraction. Step code
is valid for any flag, and the final scalar result cannot depend on that flag. -/
def ScalarRangeExitPlan.Meaning (plan : ScalarRangeExitPlan) (saved : List UInt64) (value : UInt64) : Prop :=
  ∃ (stop start : UInt64) (step : Nat → UInt64 → ForInStep UInt64),
    plan.count.ScalarEval (rangeExitStore saved 0 0 0 0) stop (rangeExitStore saved 0 0 0 0) ∧
    plan.initial.ScalarEval (rangeExitStore saved 0 0 stop 0) start (rangeExitStore saved 0 0 stop 0) ∧
    (∀ index, index < stop.toNat → ∀ accumulator flag,
      (ScalarStepCode.mk plan.step plan.done).Meaning
        (rangeExitStore saved accumulator index stop flag) (step index accumulator)) ∧
    (∀ flag, plan.result.ScalarEval
      (rangeExitStore saved (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop flag) value
      (rangeExitStore saved (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop flag))

theorem scalarRangeExit_correct_of_supported {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (saved : List UInt64)
    {locals : List ScalarBinding} {plan : ScalarRangeExitPlan} {values : List Value}
    (compiled : extractScalarRangeExitWith locals saved.length source = some plan)
    (localsTyped : locals.map ScalarBinding.kind = types) (valuesTyped : values.map Value.kind = types)
    (bindings : RangeExitBindingsMatch locals values saved)
    (totalBindings : ∀ binding ∈ locals, binding.Total) :
    ∃ value, Range.Exit.Eval source values value ∧ plan.Meaning saved value := by
  classical
  induction supported generalizing locals plan values with
  | @range types first count initial body indexName accumulatorName indexBi accumulatorBi indexType hf hc hi hs =>
    change extractScalarRangeExitWith locals saved.length
      ({ indexType, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body } : ScalarRangeExitView).source = some plan at compiled
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨firstIR, ef, countIR, ec, initialIR, ei, code, es, rfl⟩ := compiled
    obtain ⟨begin, sf⟩ := hf.scalar.evaluates values valuesTyped
    obtain ⟨stop, sc⟩ := hc.scalar.evaluates values valuesTyped
    obtain ⟨start, si⟩ := hi.evaluates values valuesTyped
    have total (index : Nat) (accumulator : UInt64) :=
      hs.evaluates (.scalar (.word accumulator) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (by simp [Step.Value.kind, Value.kind, List.map_map, Function.comp_def, ← valuesTyped])
    let f := fun index accumulator => (total index accumulator).choose
    let distance := UInt64.ofNat (stop.toNat - begin.toNat)
    have distanceNat : distance.toNat = stop.toNat - begin.toNat :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _) stop.toNat_lt_size)
    let shifted := fun index accumulator => f (begin.toNat + index) accumulator
    have same : Range.Exit.iterate shifted distance.toNat 0 start =
        Range.Exit.iterate f (stop.toNat - begin.toNat) begin.toNat start := by
      simpa only [distanceNat, Nat.add_zero] using
        Range.Exit.shift_iteration f begin.toNat (stop.toNat - begin.toNat) 0 start
    refine ⟨Range.Exit.iterate f (stop.toNat - begin.toNat) begin.toNat start,
      .range indexType (.of_scalar sf) (.of_scalar sc) si (fun index accumulator => (total index accumulator).choose_spec),
      distance, start, shifted, ?_, ?_, ?_, ?_⟩
    · exact scalarRangeDistance_correct
        (extractScalarExprWith_correct sf ef (bindings 0 0 0 0))
        (extractScalarExprWith_correct sc ec (bindings 0 0 0 0))
    · exact extractScalarExprWith_correct si ei (bindings 0 0 distance 0)
    · intro index below accumulator flag
      apply extractScalarStepWith_correct ((total (begin.toNat + index) accumulator).choose_spec) es
      apply ScalarStepBindingsMatch.cons
      · apply ScalarStepBindingsMatch.cons (bindings accumulator index distance flag).step
        exact scalarRangeOffset_correct index
          (extractScalarExprWith_correct sf ef (bindings accumulator index distance flag))
          (.local (LeanExe.IR.rangeExitStore_index saved accumulator index distance flag))
      · exact LeanExe.IR.Expr.ScalarEval.local (LeanExe.IR.rangeExitStore_value saved accumulator index distance flag)
    · intro flag
      change (LeanExe.IR.Expr.local saved.length).ScalarEval _ _ _
      rw [same]
      exact .local (LeanExe.IR.rangeExitStore_value _ _ _ _ _)
  | letE sourceValue _ ih =>
    rw [extractScalarRangeExitWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih hp (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .letE hx hy, result⟩
  | idRun _ ih =>
    rw [extractScalarRangeExitWith_idRun] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idRun hv, result⟩
  | idPure _ ih =>
    rw [extractScalarRangeExitWith_idPure] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idPure hv, result⟩
  | bindRight sourceValue _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts sourceValue locals localsTyped totalBindings
    rw [extractScalarRangeExitWith_idBind, hb] at compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih compiled (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .bindRight hx hy, result⟩
  | bindLeft sourceValue sourceBody ih =>
    rw [extractScalarRangeExitWith_idBind, rangeExitSupported_excludes_pure sourceValue] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, resultIR, hr, rfl⟩ := compiled
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      ih hb localsTyped valuesTyped bindings totalBindings
    obtain ⟨y, hy⟩ := sourceBody.evaluates (.word x :: values) (by simp [Value.kind, valuesTyped])
    refine ⟨y, .bindLeft hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro flag
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop flag).cons (resultEval flag))
  | metadata _ ih =>
    rw [extractScalarRangeExitWith_metadata] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .metadata hv, result⟩

/-- The semantic loop facts follow from successful extraction of the original
source, for every matching captured environment. -/
theorem extractScalarRangeExitWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarRangeExitWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, Range.Exit.Eval source values value ∧ plan.Meaning saved value :=
  scalarRangeExit_correct_of_supported (extractScalarRangeExitWith_supported compiled) saved
    compiled rfl typed bindings total

/-- The extracted setup, dynamic loop, result assignment and scalar ABI execute
with the source value. All iteration premises were derived by the extractor. -/
theorem ScalarRangeExitPlan.Meaning.func_correct {plan : ScalarRangeExitPlan} {args : List UInt64}
    {value : UInt64} (meaning : plan.Meaning args value)
    (name : Lean.Name) (exportName : Option String) :
    (plan.func name exportName args.length).ScalarEval args value := by
  obtain ⟨stop, start, step, countEval, initialEval, stepEval, resultEval⟩ := meaning
  have countWrite : (rangeExitStore args 0 0 0 0).write (args.length + 2) stop =
      some (rangeExitStore args 0 0 stop 0) := by
    simpa [rangeExitStore] using LeanExe.IR.write_suffix args [0, 0, 0, 0] 2 stop (by simp)
  obtain ⟨flag, loopEval⟩ := LeanExe.IR.rangeExit_while_execution args start stop 0 plan.step plan.done step
    (fun index below accumulator flag => (stepEval index below accumulator flag).2)
    (fun index below accumulator flag => (stepEval index below accumulator flag).1)
  have bodyEval : plan.body args.length |>.ScalarEval (rangeExitStore args 0 0 0 0)
      (rangeExitStore args value stop.toNat stop flag) := by
    exact .seq (.assign countEval countWrite)
      (.seq (.assign initialEval (LeanExe.IR.rangeExitStore_write_value args 0 start 0 stop 0))
        (.seq (.assign .const (LeanExe.IR.rangeExitStore_write_index args start 0 0 stop 0))
          (.seq (.assign .const (LeanExe.IR.rangeExitStore_write_flag args start 0 stop 0 0))
            (.seq loopEval (.assign (resultEval flag)
              (LeanExe.IR.rangeExitStore_write_value args _ value stop.toNat stop flag))))))
  refine .run (afterBody := rangeExitStore args value stop.toNat stop flag)
    (afterResult := rangeExitStore args value stop.toNat stop flag) rfl (by simp [ScalarRangeExitPlan.func]) ?_ rfl ?_
  · simpa [ScalarRangeExitPlan.func, rangeExitStore] using bodyEval
  · exact .local (LeanExe.IR.rangeExitStore_value args value stop.toNat stop flag)

end LeanExe.Extract.Core
