import LeanExe.IR.Correct

/-!
The rule lemma for the compiler's tail-recursion template.  The compiler turns a
definition whose recursive calls are all in tail position into
`while done = 0 do step`, with `result` in the first compiler variable, `done`
in the second, and the loop's value read from `result`.  `Func.tail_implements`
proves such a function correct from one obligation, `TailStep`, about a single
run of `step`.
-/

namespace LeanExe.IR

open Wasm LeanExe.Pipeline

/-- The IR state of the loop at arguments `args`, with `result` and `done` in the
first two compiler variables and `others` in the remaining variables and the
scratch locals. -/
def tailState [Scalar α] (args : α) (result done : UInt64) (others : List Value) : State :=
  { params := Scalar.values args, locals := .i64 result :: .i64 done :: others }

/-- One run of the loop body, from arguments `args` with `done = 0`, keeps the
store and either continues with arguments that have the same value of `f` and a
smaller measure, or stores `f args` and sets `done`.  `width` is the number of
locals after `result` and `done`. -/
def TailStep [Scalar α] (m : Module) (step : Stmt) (scratch width : Nat) (f : α → UInt64)
    (measure : α → Nat) : Prop :=
  ∀ (initial : Store Unit) (args : α) (result : UInt64) (others : List Value),
    others.length = width →
    Triple m step scratch
      (fun store state => store = initial ∧ state = tailState args result 0 others)
      (fun store state => store = initial ∧ ∃ result' others', others'.length = width ∧
        ((∃ args', state = tailState args' result' 0 others' ∧ f args' = f args ∧
            measure args' < measure args) ∨
          state = tailState args (f args) 1 others'))

theorem tailState_get_done [Scalar α] {args : α} {n : Nat}
    (hArity : (Scalar.values args).length = n) (result done : UInt64) (others : List Value) :
    (tailState args result done others).get (n + 1) = some (.i64 done) := by
  simp [tailState, State.get, hArity]

theorem tailState_get_result [Scalar α] {args : α} {n : Nat}
    (hArity : (Scalar.values args).length = n) (result done : UInt64) (others : List Value) :
    (tailState args result done others).get n = some (.i64 result) := by
  simp [tailState, State.get, hArity]

/-- A function compiled by the tail-recursion template implements `f` when each
run of the loop body satisfies `TailStep` for some measure.  The arguments must
be recoverable from their WASM values. -/
theorem Func.tail_implements [Scalar α] (funcs : List (Func × String)) (i : Nat) (func : Func)
    (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → UInt64)
    (measure : α → Nat) (step : Stmt)
    (arity : ∀ x : α, (Scalar.values x).length = func.params.length)
    (injective : ∀ x y : α, Scalar.values x = Scalar.values y → x = y)
    {k : Nat} (vars : func.vars = List.replicate (k + 2) .u64)
    (body : func.body = .while (.eq (.get (func.params.length + 1)) (.const 0)) step)
    (results : func.results = [⟨.u64, .get func.params.length⟩])
    (hStep : TailStep (compile funcs) step func.scratch (k + func.width) f measure) :
    Implements (compile funcs) (2 + i) f := by
  refine Func.implements funcs i func name hFunc f
    (fun _ _ _ x h => (Scalar.borrowed.mp h) ▸ arity x) fun x _ initial params _ h => ?_
  obtain rfl := Scalar.borrowed.mp h
  rw [body, results]
  let width := k + func.width
  let Inv : Store Unit → State → Prop := fun store state =>
    store = initial ∧ ∃ (args : α) (resultValue : UInt64) (others : List Value), others.length = width ∧
      ((state = tailState args resultValue 0 others ∧ f args = f x) ∨
        state = tailState args (f x) 1 others)
  let running : State → Prop := fun state =>
    ∃ (args : α) (resultValue : UInt64) (others : List Value),
      state = tailState args resultValue 0 others
  let stateMeasure : State → Nat := fun state => by
    classical
    exact if h : running state then measure (Classical.choose h) + 1 else 0
  have hRunning : ∀ (args : α) (resultValue : UInt64) (others : List Value),
      stateMeasure (tailState args resultValue 0 others) = measure args + 1 := by
    intro args resultValue others
    have h : running (tailState args resultValue 0 others) := ⟨args, resultValue, others, rfl⟩
    simp only [stateMeasure, dite_eq_left h]
    obtain ⟨resultValue', others', hEq⟩ := Classical.choose_spec h
    have hParams := congrArg State.params hEq
    simp only [tailState] at hParams
    have hArgs : Classical.choose h = args := (injective _ _ hParams).symm
    rw [hArgs]
  have hFinished : ∀ (args : α) (resultValue : UInt64) (others : List Value),
      stateMeasure (tailState args resultValue 1 others) = 0 := by
    intro args resultValue others
    have h : ¬ running (tailState args resultValue 1 others) := by
      rintro ⟨args', resultValue', others', hEq⟩
      have hLocals := congrArg State.locals hEq
      simp [tailState] at hLocals
    simp only [stateMeasure, dite_eq_right h]
  -- One run of the body from a running state restores the invariant with a smaller
  -- measure.
  have hIteration : ∀ (args : α) resultValue (others : List Value), others.length = width →
      f args = f x →
      Triple (compile funcs) step func.scratch
        (fun store state => store = initial ∧ state = tailState args resultValue 0 others)
        (fun store state => Inv store state ∧ stateMeasure state < measure args + 1) := by
    intro args resultValue others hLength hSame
    refine (hStep initial args resultValue others hLength).mono (fun _ _ h => h) ?_
    rintro store state ⟨rfl, resultValue', others', hLength', ⟨args', rfl, hSame', hLess⟩ | rfl⟩
    · refine ⟨⟨rfl, args', resultValue', others', hLength', Or.inl ⟨rfl, hSame'.trans hSame⟩⟩, ?_⟩
      rw [hRunning]
      omega
    · refine ⟨⟨rfl, args, f args, others', hLength', Or.inr (by rw [hSame])⟩, ?_⟩
      rw [hFinished]
      omega
  refine (Stmt.while_spec Inv (fun _ state => stateMeasure state) ?_ fun n => ?_).mono ?_ ?_
  · rintro store state ⟨-, args, resultValue, others, -, ⟨rfl, -⟩ | rfl⟩ <;>
      simp [Expr.eval, tailState_get_done (arity args)]
  · intro env store state values rest Q hTrap hPre hPost
    obtain ⟨before, ⟨rfl, args, resultValue, others, hLength, ⟨rfl, hSame⟩ | rfl⟩, hMeasure,
      hCondition⟩ := hPre
    · simp [Expr.eval, tailState_get_done (arity args)] at hCondition
      subst hCondition
      rw [hRunning] at hMeasure
      subst hMeasure
      exact hIteration args resultValue others hLength hSame env _ _ values rest Q hTrap ⟨rfl, rfl⟩ hPost
    · simp [Expr.eval, tailState_get_done (arity args)] at hCondition
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨rfl, x, 0, List.replicate width (.i64 0), by simp, Or.inl ⟨?_, rfl⟩⟩
    simp only [Func.state, Func.locals, tailState, width, vars, List.map_replicate,
      List.map_append, ScalarType.valueType, ValueType.zero, List.replicate_append_replicate]
    rw [show k + 2 + func.width = (k + func.width) + 1 + 1 by omega]
    rfl
  · rintro store state ⟨before, ⟨rfl, args, resultValue, others, -, ⟨rfl, -⟩ | rfl⟩, hCondition⟩
    · simp [Expr.eval, tailState_get_done (arity args)] at hCondition
    · simp [Expr.eval, tailState_get_done (arity args)] at hCondition
      subst hCondition
      exact ⟨rfl, [.i64 (f x)], tailState args (f x) 1 others, by
        simp [Expr.evalResults, Expr.eval, tailState_get_result (arity args)], rfl⟩

/-- A `while` rule whose measure is a ghost index in the invariant. -/
theorem Stmt.while_ghost {m : Module} {condition : Expr .bool} {body : Stmt} {scratch : Nat}
    (Inv : Nat → Store Unit → State → Prop)
    (hCondition : ∀ n store state, Inv n store state →
      ∃ result afterCondition,
        condition.eval store.mem scratch state = some (result, afterCondition))
    (hBody : ∀ n, Triple m body scratch
      (fun store state => ∃ before, Inv n store before ∧
        condition.eval store.mem scratch before = some (true, state))
      (fun store state => ∃ n' < n, Inv n' store state)) :
    Triple m (.while condition body) scratch (fun store state => ∃ n, Inv n store state)
      (fun store state => ∃ n before, Inv n store before ∧
        condition.eval store.mem scratch before = some (false, state)) := by
  classical
  refine (Stmt.while_spec (fun store state => ∃ n, Inv n store state)
    (fun store state => if h : ∃ n, Inv n store state then Nat.find h else 0)
    (fun store state ⟨n, h⟩ => hCondition n store state h) fun n => ?_).mono
    (fun _ _ h => h) fun _ _ ⟨before, ⟨k, h⟩, hc⟩ => ⟨k, before, h, hc⟩
  refine (hBody n).mono ?_ ?_
  · rintro store state ⟨before, hEx, hMeasure, hc⟩
    rw [dite_eq_left hEx] at hMeasure
    exact ⟨before, hMeasure ▸ Nat.find_spec hEx, hc⟩
  · rintro store state ⟨n', hLt, hInv⟩
    have hEx : ∃ n, Inv n store state := ⟨n', hInv⟩
    refine ⟨hEx, ?_⟩
    rw [dite_eq_left hEx]
    exact lt_of_le_of_lt (Nat.find_min' hEx hInv) hLt

/-- The IR state of the loop with parameter values `vs`, with `result` and `done` in the first
two compiler variables and `others` in the remaining locals. -/
def tailStateIn (vs : List Value) (result done : UInt64) (others : List Value) : State :=
  { params := vs, locals := .i64 result :: .i64 done :: others }

/-- `TailStep` for arguments that a fixed store represents: one run of the loop body from
parameter values `vs` that represent `args` as borrowed, with `done = 0`, keeps the store and
either continues with values that represent arguments with the same value of `f` and a
smaller measure, or keeps the parameters, stores `f args`, and sets `done`. -/
def TailStepIn [Represent α] (m : Module) (step : Stmt) (scratch width : Nat) (f : α → UInt64)
    (measure : α → Nat) : Prop :=
  ∀ (heap : Heap) (initial : Store Unit) (args : α) (vs : List Value) (result : UInt64)
    (others : List Value), heap.At initial → Represent.borrowed heap initial vs args →
    others.length = width →
    Triple m step scratch
      (fun store state => store = initial ∧ state = tailStateIn vs result 0 others)
      (fun store state => store = initial ∧ ∃ result' others', others'.length = width ∧
        ((∃ args' vs', Represent.borrowed heap initial vs' args' ∧
            state = tailStateIn vs' result' 0 others' ∧ f args' = f args ∧
            measure args' < measure args) ∨
          state = tailStateIn vs (f args) 1 others'))

/-- A function compiled by the tail-recursion template implements `f`, for arguments of any
represented type, when each run of the loop body satisfies `TailStepIn` for some measure. -/
theorem Func.tailIn_implements [Represent α] (funcs : List (Func × String)) (i : Nat)
    (func : Func) (name : String) (hFunc : funcs[i]? = some (func, name)) (f : α → UInt64)
    (measure : α → Nat) (step : Stmt)
    (arity : ∀ heap store params (x : α), Represent.borrowed heap store params x →
      params.length = func.params.length)
    {rest : List ScalarType} (vars : func.vars = .u64 :: .u64 :: rest)
    (body : func.body = .while (.eq (.get (func.params.length + 1)) (.const 0)) step)
    (results : func.results = [⟨.u64, .get func.params.length⟩])
    (hStep : TailStepIn (compile funcs) step func.scratch (rest.length + func.width) f
      measure) :
    Implements (compile funcs) (2 + i) f := by
  refine Func.implements funcs i func name hFunc f arity fun x heap initial params hHeap hArgs => ?_
  rw [body, results]
  let width := rest.length + func.width
  have hDone : ∀ (vs : List Value) (r d : UInt64) (others : List Value),
      vs.length = func.params.length →
      (tailStateIn vs r d others).get (func.params.length + 1) = some (.i64 d) := by
    intro vs r d others hLen
    simp [tailStateIn, State.get, hLen]
  let Inv : Nat → Store Unit → State → Prop := fun n store state =>
    store = initial ∧ ∃ (r : UInt64) (others : List Value), others.length = width ∧
      ((∃ (args : α) (vs : List Value), Represent.borrowed heap initial vs args ∧
          state = tailStateIn vs r 0 others ∧ f args = f x ∧ n = measure args + 1) ∨
        ∃ vs : List Value, vs.length = func.params.length ∧
          state = tailStateIn vs (f x) 1 others ∧ n = 0)
  refine (Stmt.while_ghost Inv ?_ fun n => ?_).mono ?_ ?_
  · rintro n store state ⟨-, r, others, -, ⟨args, vs, hB, rfl, -⟩ | ⟨vs, hLen, rfl, -⟩⟩
    · exact ⟨true, tailStateIn vs r 0 others, by
        simp [Expr.eval, hDone vs r 0 others (arity _ _ _ _ hB)]⟩
    · exact ⟨false, tailStateIn vs (f x) 1 others, by simp [Expr.eval, hDone vs (f x) 1 others hLen]⟩
  · apply Triple.of_forall
    rintro store state ⟨before, ⟨hStore, r, others, hLen, ⟨args, vs, hB, rfl, hSame, rfl⟩ |
      ⟨vs, hVs, rfl, rfl⟩⟩, hCondition⟩
    all_goals subst store
    · simp [Expr.eval, hDone vs r 0 others (arity _ _ _ _ hB)] at hCondition
      subst hCondition
      refine (hStep heap initial args vs r others hHeap hB hLen).mono (fun _ _ h => h) ?_
      rintro store' state' ⟨hStore', r', others', hLen', ⟨args', vs', hB', rfl, hSame', hLess⟩ | rfl⟩
      all_goals subst store'
      · exact ⟨measure args' + 1, by omega, rfl, r', others', hLen',
          Or.inl ⟨args', vs', hB', rfl, hSame'.trans hSame, rfl⟩⟩
      · exact ⟨0, by omega, rfl, f args, others', hLen',
          Or.inr ⟨vs, arity _ _ _ _ hB, by rw [hSame], rfl⟩⟩
    · simp [Expr.eval, hDone vs (f x) 1 others hVs] at hCondition
  · rintro store state ⟨hStore, rfl⟩
    subst store
    refine ⟨measure x + 1, rfl, 0,
      (rest.map ScalarType.valueType ++ List.replicate func.width ValueType.i64).map
        ValueType.zero,
      by simp [width], Or.inl ⟨x, params, hArgs, ?_, rfl, rfl⟩⟩
    simp [Func.state, Func.locals, tailStateIn, vars, ScalarType.valueType, ValueType.zero]
  · rintro store state ⟨n, before, ⟨hStore, r, others, -, ⟨args, vs, hB, rfl, -⟩ |
      ⟨vs, hVs, rfl, -⟩⟩, hCondition⟩
    all_goals subst store
    · simp [Expr.eval, hDone vs r 0 others (arity _ _ _ _ hB)] at hCondition
    · simp [Expr.eval, hDone vs (f x) 1 others hVs] at hCondition
      subst hCondition
      exact ⟨rfl, [.i64 (f x)], tailStateIn vs (f x) 1 others, by
        simp [Expr.evalResults, Expr.eval, tailStateIn, State.get, hVs], rfl⟩

end LeanExe.IR