import Project.IR.Correct

/-!
The rule lemma for the compiler's tail-recursion template.  The compiler turns a
definition whose recursive calls are all in tail position into
`while done = 0 do step`, with `result` in the first compiler variable, `done`
in the second, and the loop's value read from `result`.  `Func.tail_implements`
proves such a function correct from one obligation, `TailStep`, about a single
run of `step`.
-/

namespace Project.IR

open Wasm Project.Pipeline

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
    Implements (compile funcs) (3 + i) f (fun _ => 0) := by
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
  · intro env store state values rest Q hPre hPost
    obtain ⟨before, ⟨rfl, args, resultValue, others, hLength, ⟨rfl, hSame⟩ | rfl⟩, hMeasure,
      hCondition⟩ := hPre
    · simp [Expr.eval, tailState_get_done (arity args)] at hCondition
      subst hCondition
      rw [hRunning] at hMeasure
      subst hMeasure
      exact hIteration args resultValue others hLength hSame env _ _ values rest Q ⟨rfl, rfl⟩ hPost
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

end Project.IR
