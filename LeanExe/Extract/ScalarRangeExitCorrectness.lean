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

private theorem total_boolean_cons {locals : List ScalarBinding}
    (total : ∀ binding ∈ locals, binding.Total) (expression : LeanExe.IR.Expr) :
    ∀ binding ∈ ScalarBinding.boolean expression :: locals, binding.Total := by
  intro binding member
  rcases List.mem_cons.mp member with rfl | member
  · trivial
  · exact total binding member

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
  | @range types first count initial body indexName accumulatorName indexBi accumulatorBi indexType stride hf hc hi hs =>
    change extractScalarRangeExitWith locals saved.length
      ({ indexType, stride, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body } : ScalarRangeExitView).source = some plan at compiled
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
    have distanceSmall : stop.toNat - begin.toNat < UInt64.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) stop.toNat_lt_size
    let countNat := Range.Exit.trips (stop.toNat - begin.toNat) stride.number
    let bound := UInt64.ofNat countNat
    have boundNat : bound.toNat = countNat :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Range.Exit.trips_le stride.positive) distanceSmall)
    let shifted := fun index accumulator => f (begin.toNat + stride.number * index) accumulator
    refine ⟨Range.Exit.iterate shifted countNat 0 start,
      .range indexType stride (.of_scalar sf) (.of_scalar sc) si (fun index accumulator => (total index accumulator).choose_spec),
      bound, start, shifted, ?_, ?_, ?_, ?_⟩
    · have lowered := scalarRangeTrips_correct stride.positive stride.fits
        (scalarRangeDistance_correct
          (extractScalarExprWith_correct sf ef (bindings 0 0 0 0))
          (extractScalarExprWith_correct sc ec (bindings 0 0 0 0)))
      simpa only [UInt64.toNat_ofNat_of_lt' distanceSmall] using lowered
    · exact extractScalarExprWith_correct si ei (bindings 0 0 bound 0)
    · intro index below accumulator flag
      apply extractScalarStepWith_correct ((total (begin.toNat + stride.number * index) accumulator).choose_spec) es
      apply ScalarStepBindingsMatch.cons
      · apply ScalarStepBindingsMatch.cons (bindings accumulator index bound flag).step
        exact scalarRangeOffset_correct (stride.number * index)
          (extractScalarExprWith_correct sf ef (bindings accumulator index bound flag))
          (scalarRangeScale_correct stride.number index
            (.local (LeanExe.IR.rangeExitStore_index saved accumulator index bound flag)))
      · exact LeanExe.IR.Expr.ScalarEval.local (LeanExe.IR.rangeExitStore_value saved accumulator index bound flag)
    · intro flag
      change (LeanExe.IR.Expr.local saved.length).ScalarEval _ _ _
      rw [boundNat]
      exact .local (LeanExe.IR.rangeExitStore_value _ _ _ _ _)
  | letBoolean expression variables arguments _ ih =>
    rw [extractScalarRangeExitWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values valuesTyped
    have total := fun operand member => (arguments operand member).evaluates values valuesTyped
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ expression.operands then (total operand member).choose else 0
    have meanings : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (total operand member).choose_spec
    have extended : RangeExitBindingsMatch (.boolean (guardWord c) :: locals)
        (.boolean (expression.denote native booleans) :: values) saved := by
      intro accumulator index stop flag
      apply (bindings accumulator index stop flag).cons
      exact guardWord_correct (extractBooleanLocalWith_correct expression _ native booleans hc
        (bindings accumulator index stop flag) hbooleans
        (fun operand member target found => extractScalarExprWith_correct (meanings operand member)
          found (bindings accumulator index stop flag)))
    obtain ⟨result, source, meaning⟩ := ih ht (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact totalBindings binding member)
    exact ⟨result, .letBoolean expression hbooleans meanings source, meaning⟩
  | idBindBoolean action type variables arguments _ ih =>
    rw [extractScalarRangeExitWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values valuesTyped
    have total := fun operand member => (arguments operand member).evaluates values valuesTyped
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ action.leaf.operands then (total operand member).choose else 0
    have meanings : ∀ operand, operand ∈ action.leaf.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (total operand member).choose_spec
    have extended : RangeExitBindingsMatch (.boolean (guardWord c) :: locals)
        (.boolean (action.leaf.denote native booleans) :: values) saved := by
      intro accumulator index stop flag
      apply (bindings accumulator index stop flag).cons
      exact guardWord_correct (extractBooleanLocalWith_correct action.leaf _ native booleans hc
        (bindings accumulator index stop flag) hbooleans
        (fun operand member target found => extractScalarExprWith_correct (meanings operand member)
          found (bindings accumulator index stop flag)))
    obtain ⟨result, source, meaning⟩ := ih ht (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) extended (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact totalBindings binding member)
    exact ⟨result, .idBindBoolean action type hbooleans meanings source, meaning⟩
  | letE sourceValue _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts sourceValue locals localsTyped totalBindings
    rw [extractScalarRangeExitWith_letE, hb] at compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih compiled (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .letE hx hy, result⟩
  | idRun type _ ih =>
    rw [extractScalarRangeExitWith_idRun] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idRun type hv, result⟩
  | idPure type _ ih =>
    rw [extractScalarRangeExitWith_idPure] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idPure type hv, result⟩
  | bindRight input output sourceValue _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts sourceValue locals localsTyped totalBindings
    rw [extractScalarRangeExitWith_idBind, hb] at compiled
    obtain ⟨x, hx⟩ := sourceValue.evaluates values valuesTyped
    obtain ⟨y, hy, result⟩ := ih compiled (by simp [ScalarBinding.kind, localsTyped])
      (by simp [Value.kind, valuesTyped]) (bindings.bind hx hb) (total_word_cons totalBindings bound)
    exact ⟨y, .bindRight input output hx hy, result⟩
  | bindLeft input output sourceValue sourceBody ih =>
    rw [extractScalarRangeExitWith_idBind, rangeExitSupported_excludes_pure sourceValue] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, resultIR, hr, rfl⟩ := compiled
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      ih hb localsTyped valuesTyped bindings totalBindings
    obtain ⟨y, hy⟩ := sourceBody.evaluates (.word x :: values) (by simp [Value.kind, valuesTyped])
    refine ⟨y, .bindLeft input output hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro flag
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop flag).cons (resultEval flag))
  | letFn type function _ ih =>
    rw [extractScalarRangeExitWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, hp⟩ := compiled
    have total (x : UInt64) := function.evaluates (.word x :: values)
      (by simp [Value.kind, valuesTyped])
    let f := fun x => (total x).choose
    obtain ⟨result, hs, hm⟩ := ih (values := .function false f :: values) hp
      (by simp [ScalarBinding.kind, localsTyped]) (by simp [Value.kind, valuesTyped]) (by
        intro accumulator index stop flag
        apply (bindings accumulator index stop flag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((total x).choose_spec) hc
          ((bindings accumulator index stop flag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          exact extractScalarExprWith_accepts function (.word argument :: locals)
            (by simp [ScalarBinding.kind, localsTyped]) (total_word_cons totalBindings argument)
        · exact totalBindings binding member)
    exact ⟨result, .letFn type (fun x => (total x).choose_spec) hs, hm⟩
  | letBooleanFn type function _ ih =>
    rw [extractScalarRangeExitWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, hp⟩ := compiled
    have total (x : Bool) := function.evaluates (.boolean x :: values)
      (by simp [Value.kind, valuesTyped])
    let f := fun x => (total x).choose
    obtain ⟨result, hs, hm⟩ := ih (values := .booleanFunction f :: values) hp
      (by simp [ScalarBinding.kind, localsTyped]) (by simp [Value.kind, valuesTyped]) (by
        intro accumulator index stop flag
        apply (bindings accumulator index stop flag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((total x).choose_spec) hc
          ((bindings accumulator index stop flag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          exact extractScalarExprWith_accepts function (.boolean argument :: locals)
            (by simp [ScalarBinding.kind, localsTyped]) (total_boolean_cons totalBindings argument)
        · exact totalBindings binding member)
    exact ⟨result, .letBooleanFn type (fun x => (total x).choose_spec) hs, hm⟩
  | letBinaryFn type function _ ih =>
    rw [extractScalarRangeExitWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, hp⟩ := compiled
    have total (x y : UInt64) := function.evaluates (.word y :: .word x :: values)
      (by simp [Value.kind, valuesTyped])
    let f := fun x y => (total x y).choose
    obtain ⟨result, hs, hm⟩ := ih (values := .binaryFunction f :: values) hp
      (by simp [ScalarBinding.kind, localsTyped]) (by simp [Value.kind, valuesTyped]) (by
        intro accumulator index stop flag
        apply (bindings accumulator index stop flag).cons
        intro first x second y target hx hy hc
        exact extractScalarExprWith_correct ((total x y).choose_spec) hc
          (((bindings accumulator index stop flag).cons (binding := .word first) (value := .word x) hx).cons
            (binding := .word second) (value := .word y) hy)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro first second
          exact extractScalarExprWith_accepts function (.word second :: .word first :: locals)
            (by simp [ScalarBinding.kind, localsTyped])
            (total_word_cons (total_word_cons totalBindings first) second)
        · exact totalBindings binding member)
    exact ⟨result, .letBinaryFn type (fun x y => (total x y).choose_spec) hs, hm⟩
  | letManyFn shape function _ ih =>
    rw [extractScalarRangeExitWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, hp⟩ := compiled
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates values valuesTyped
    obtain ⟨result, hs, hm⟩ := ih (values := .manyFunction shape.arity f :: values) hp
      (by simp [ScalarBinding.kind, localsTyped]) (by simp [Value.kind, valuesTyped]) (by
        intro accumulator index stop flag
        apply (bindings accumulator index stop flag).cons
        intro arguments native target len argumentsMeaning hc
        exact extractScalarExprWith_correct (meanings native (argumentsMeaning.length.symm.trans len)) hc
          ((bindings accumulator index stop flag).words argumentsMeaning.reverse)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro arguments len
          exact extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
            (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len, localsTyped])
            (scalarWords_total _ totalBindings)
        · exact totalBindings binding member)
    exact ⟨result, .letManyFn shape meanings hs, hm⟩
  | letUnitFn type unitForm function _ ih =>
    rw [extractScalarRangeExitWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, hp⟩ := compiled
    have total (x : UInt64) := function.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, valuesTyped])
    let f := fun x => (total x).choose
    obtain ⟨result, hs, hm⟩ := ih (values := .function true f :: values) hp
      (by simp [ScalarBinding.kind, localsTyped]) (by simp [Value.kind, valuesTyped]) (by
        intro accumulator index stop flag
        apply (bindings accumulator index stop flag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((total x).choose_spec) hc
          (((bindings accumulator index stop flag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts function (.word argument :: .unit :: locals)
            (by simp [ScalarBinding.kind, localsTyped])
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact totalBindings binding member
        · exact totalBindings binding member)
    exact ⟨result, .letUnitFn type unitForm (fun x => (total x).choose_spec) hs, hm⟩
  | letLeft sourceValue sourceBody ih =>
    rw [extractScalarRangeExitWith_letE, rangeExitSupported_excludes_pure sourceValue] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, resultIR, hr, rfl⟩ := compiled
    obtain ⟨x, hx, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
      ih hb localsTyped valuesTyped bindings totalBindings
    obtain ⟨y, hy⟩ := sourceBody.evaluates (.word x :: values) (by simp [Value.kind, valuesTyped])
    refine ⟨y, .letLeft hx hy, stop, start, step, countEval, initialEval, stepEval, ?_⟩
    intro flag
    exact extractScalarExprWith_correct hy hr
      ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop flag).cons (resultEval flag))
  | idLet _ ih =>
    rw [extractScalarRangeExitWith_idLet] at compiled
    obtain ⟨value, hv, result⟩ := ih compiled localsTyped valuesTyped bindings totalBindings
    exact ⟨value, .idLet hv, result⟩
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
