import LeanExe.Core.NativeLoopLocals

namespace LeanExe.Core.NativeRangeFunction

open LeanExe.Wasm.ScalarDescriptor (Expr Cond U64Op)
open LeanExe.Core.NativeLoopLocals

def rangeArguments (staticCount : Nat) : List Expr :=
  (List.range staticCount).map Expr.get ++ [.get staticCount, .get (staticCount + 2)]

def rangeCondition (staticCount : Nat) : Cond :=
  .ltU (.get (staticCount + 2)) (.get (staticCount + 1))

def rangeBody (staticCount iterationIndex : Nat) : Stmt :=
  .seq (.call staticCount iterationIndex (rangeArguments staticCount))
    (.assign (staticCount + 2) (.bin .add (.get (staticCount + 2)) (.const 1)))

/-- A bounded loop calls the compiled native iteration with the captured
arguments, accumulator, and current index. Its only local is the counter. -/
def rangeFunction (staticCount iterationIndex : Nat) : Function where
  params := staticCount + 2
  locals := 1
  body := .seq (.assign (staticCount + 2) (.const 0))
    (.loop (rangeCondition staticCount) (rangeBody staticCount iterationIndex))
  result := .get staticCount

private theorem prefix_arguments (saved suffix : Locals) :
    arguments ((List.range saved.length).map Expr.get) (saved ++ suffix) = some saved := by
  unfold arguments
  simp only [List.mapM_map, Function.comp_def, Expr.eval]
  induction saved with
  | nil => rfl
  | cons value saved induction =>
    simp [List.range_succ_eq_map, List.mapM_map, Function.comp_def, induction]

theorem rangeArguments_eval (saved : Locals) (accumulator limit : UInt64) (index : Nat) :
    arguments (rangeArguments saved.length) (layout saved accumulator limit index []) =
      some (saved ++ [accumulator, UInt64.ofNat index]) := by
  have capturedArguments :
      arguments ((List.range saved.length).map Expr.get)
          (layout saved accumulator limit index []) = some saved := by
    simpa only [layout, List.append_nil] using
      prefix_arguments saved [accumulator, limit, UInt64.ofNat index]
  unfold rangeArguments arguments
  rw [List.mapM_append]
  unfold arguments at capturedArguments
  rw [capturedArguments]
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, layout_accumulator, layout_counter,
    bind, pure, Option.bind]

theorem rangeCondition_eval (saved : Locals) (accumulator limit : UInt64)
    (index : Nat) (bound : index ≤ limit.toNat) :
    (rangeCondition saved.length).eval (layout saved accumulator limit index []) =
      some (decide (index < limit.toNat)) := by
  simpa only [rangeCondition, Cond.eval, Expr.eval, layout_counter, layout_limit,
    bind, pure, Option.bind] using
    congrArg some (NativeLoop.counter_lt limit index bound)

theorem rangeBody_eval
    {functions : Module} {effects : Effects σ} {iterationIndex : Nat}
    (saved : Locals) (accumulator limit value : UInt64) (index : Nat)
    {initial final : σ}
    (called : Invokes functions effects iterationIndex initial
      (saved ++ [accumulator, UInt64.ofNat index]) final value) :
    Eval functions effects (rangeBody saved.length iterationIndex) initial
      (layout saved accumulator limit index []) final
      (layout saved value limit (index + 1) []) := by
  obtain ⟨function, returned, found, arity, executed, output⟩ := called
  apply Eval.seq
  · exact .call found (rangeArguments_eval saved accumulator limit index) arity executed output
      (layout_write_accumulator saved accumulator limit value index [])
  · apply Eval.assign (value := UInt64.ofNat (index + 1))
    · simpa only [Expr.eval, layout_counter, U64Op.apply, bind, pure, Option.bind,
        HAdd.hAdd, Add.add, UInt64.ofNat_one] using
        congrArg some (NativeLoop.counter_succ index)
    · exact layout_write_counter saved value limit index (index + 1) []

/-- The generated range helper implements Lean's actual finite iterator. The
only external premise is correctness of the compiled native iteration helper. -/
theorem rangeFunction_correct
    {functions : Module} {effects : Effects σ} {rangeIndex iterationIndex : Nat}
    (saved : Locals) (accumulator limit : UInt64)
    (body : Nat → UInt64 → StateM σ UInt64)
    (found : functions[rangeIndex]? = some (rangeFunction saved.length iterationIndex))
    (iteration : ∀ index current initial, index < limit.toNat →
      Invokes functions effects iterationIndex initial
        (saved ++ [current, UInt64.ofNat index])
        (body index current initial).2 (body index current initial).1)
    (initial : σ) :
    Invokes functions effects rangeIndex initial (saved ++ [accumulator, limit])
      (NativeLoop.runRange body 0 limit.toNat accumulator initial).2
      (NativeLoop.runRange body 0 limit.toNat accumulator initial).1 := by
  let represented := fun index current locals => locals = layout saved current limit index []
  have guard : ∀ index current locals, index ≤ limit.toNat → represented index current locals →
      (rangeCondition saved.length).eval locals = some (decide (index < limit.toNat)) := by
    intro index current locals bound related
    subst locals
    exact rangeCondition_eval saved current limit index bound
  have advance : ∀ index current state locals, index < limit.toNat →
      represented index current locals →
      ∃ next, Eval functions effects (rangeBody saved.length iterationIndex) state locals
          (body index current state).2 next ∧
        represented (index + 1) (body index current state).1 next := by
    intro index current state locals below related
    subst locals
    exact ⟨_, rangeBody_eval saved current limit _ index (iteration index current state below), rfl⟩
  obtain ⟨result, executed, related⟩ := NativeLoop.range_eval body represented limit.toNat guard advance
    (start := 0) (count := limit.toNat) (by omega) accumulator initial
    (layout saved accumulator limit 0 []) rfl
  refine ⟨rangeFunction saved.length iterationIndex, result, found, ?_, ?_, ?_⟩
  · simp [rangeFunction]
  · have initialized : Eval functions effects (.assign (saved.length + 2) (.const 0)) initial
        (layout saved accumulator limit 0 []) initial (layout saved accumulator limit 0 []) :=
      .assign rfl (layout_write_counter saved accumulator limit 0 0 [])
    simpa [rangeFunction, layout, List.append_assoc] using Eval.seq initialized executed
  · change Expr.eval result (.get saved.length) = _
    rw [related]
    exact layout_accumulator saved _ limit limit.toNat []

theorem rangeFunction_state_correct
    {functions : Module} {effects : Effects σ} {rangeIndex iterationIndex : Nat}
    (saved : Locals) (accumulator limit : UInt64)
    (body : Nat → UInt64 → StateM σ UInt64)
    (found : functions[rangeIndex]? = some (rangeFunction saved.length iterationIndex))
    (iteration : ∀ index current initial, index < limit.toNat →
      Invokes functions effects iterationIndex initial
        (saved ++ [current, UInt64.ofNat index])
        (body index current initial).2 (body index current initial).1)
    (initial : σ) :
    let native := (forIn (List.range limit.toNat) accumulator fun index current => do
      return .yield (← body index current)) initial
    Invokes functions effects rangeIndex initial (saved ++ [accumulator, limit])
      native.2 native.1 := by
  simpa only [NativeLoop.runRange, List.range_eq_range'] using
    rangeFunction_correct saved accumulator limit body found iteration initial

theorem rangeFunction_pure_correct
    {functions : Module} {effects : Effects σ} {rangeIndex iterationIndex : Nat}
    (saved : Locals) (accumulator limit : UInt64) (body : Nat → UInt64 → UInt64)
    (found : functions[rangeIndex]? = some (rangeFunction saved.length iterationIndex))
    (iteration : ∀ index current initial, index < limit.toNat →
      Invokes functions effects iterationIndex initial
        (saved ++ [current, UInt64.ofNat index]) initial (body index current))
    (initial : σ) :
    Invokes functions effects rangeIndex initial (saved ++ [accumulator, limit]) initial
      (forIn (m := Id) (List.range limit.toNat) accumulator
        (fun index current => pure (.yield (body index current)))) := by
  have executed := rangeFunction_correct saved accumulator limit
    (fun index current => (pure (body index current) : StateM σ UInt64)) found iteration initial
  rw [NativeLoop.runRange_pure] at executed
  simpa only [List.range_eq_range'] using executed

end LeanExe.Core.NativeRangeFunction
