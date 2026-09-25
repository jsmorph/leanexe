import LeanExe.Extract.ScalarRangeCorrectness
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Source.ScalarFunction

namespace LeanExe.Extract.Core

/-- Exact concrete scalar signature. Dependent/runtime non-scalar types are not
admitted by this path. -/
def scalarArity? : Lean.Expr → Option Nat
  | .const ``UInt64 [] => some 0
  | .forallE _ (.const ``UInt64 []) body _ => (scalarArity? body).map Nat.succ
  | .mdata _ body => scalarArity? body
  | _ => none

theorem scalarArity_accepts {type : Lean.Expr} {arity : Nat}
    (h : LeanExe.Source.Scalar.Arrow type arity) : scalarArity? type = some arity := by
  induction h with
  | result => rfl
  | arg _ ih => simp [scalarArity?, ih]
  | metadata _ ih => exact ih

def scalarFunc (name : Lean.Name) (exportName : Option String) (arity : Nat)
    (expression : LeanExe.IR.Expr) : LeanExe.IR.Func :=
  { sourceName := name
    exportName
    params := arity
    locals := arity + 1
    body := .assign arity expression
    results := [.local arity] }

/-- The scalar declaration case, using the existing IR and result-slot ABI. -/
def extractScalarFunc (name : Lean.Name) (exportName : Option String)
    (type value : Lean.Expr) : Option LeanExe.IR.Func := do
  let arity ← scalarArity? type
  let body ← collectLambdas value arity
  match extractScalarExpr (List.range arity).reverse body with
  | some expression => pure (scalarFunc name exportName arity expression)
  | none =>
      let locals := (List.range arity).reverse.map fun slot => ScalarBinding.word (.local slot)
      match extractScalarRangeWith locals arity body with
      | some plan => pure (plan.func name exportName arity)
      | none => do
          let plan ← extractScalarRangeExitWith locals arity body
          pure (plan.func name exportName arity)

/-- Successful extraction selects the pure expression case, a yielding range, or an early-exit range
loop; both retain the same concrete signature and source lambda binders. -/
theorem extractScalarFunc_cases {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    ∃ arity body, scalarArity? type = some arity ∧ collectLambdas source arity = some body ∧
      ((∃ expression, extractScalarExpr (List.range arity).reverse body = some expression ∧
          func = scalarFunc name exportName arity expression) ∨
        (∃ plan, extractScalarRangeWith
          ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (∃ plan, extractScalarRangeExitWith
          ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan ∧
          func = plan.func name exportName arity)) := by
  unfold extractScalarFunc at compiled
  simp only [bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨arity, ha, body, hb, compiled⟩ := compiled
  refine ⟨arity, body, ha, hb, ?_⟩
  cases pureCase : extractScalarExpr (List.range arity).reverse body with
  | some expression =>
    simp only [pureCase, pure, Option.some.injEq] at compiled
    exact .inl ⟨expression, rfl, compiled.symm⟩
  | none =>
    simp only [pureCase] at compiled
    cases rangeCase : extractScalarRangeWith
        ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body with
    | some plan =>
      simp only [rangeCase, pure, Option.some.injEq] at compiled
      exact .inr (.inl ⟨plan, rfl, compiled.symm⟩)
    | none =>
      simp only [rangeCase, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨plan, hp, same⟩ := compiled
      exact .inr (.inr ⟨plan, hp, same.symm⟩)

theorem extractScalarFunc_properties {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    func.exportName = exportName ∧ func.params ≤ func.locals ∧ func.results = [.local func.params] := by
  obtain ⟨arity, body, _, _, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, _, rfl⟩ | ⟨plan, _, rfl⟩ | ⟨plan, _, rfl⟩
  · simp [scalarFunc]
  · simp [ScalarRangePlan.func]
  · simp [ScalarRangeExitPlan.func]

theorem scalarArgumentLocals (args scratch : List UInt64) :
    ScalarLocalsMatch (List.range args.length).reverse args.reverse (args ++ scratch) := by
  intro index slot hslot
  have hi : index < args.length := by
    have := (List.getElem?_eq_some_iff.mp hslot).1
    simpa using this
  have hj : args.length - 1 - index < args.length := by omega
  rw [List.getElem?_reverse (by simpa using hi)] at hslot
  simp only [List.length_range] at hslot
  rw [List.getElem?_range hj] at hslot
  cases hslot
  rw [List.getElem?_append_left hj, List.getElem?_reverse hi]

theorem scalarFunc_correct {body : Lean.Expr} {arity : Nat} {expression : LeanExe.IR.Expr}
    (compiled : extractScalarExpr (List.range arity).reverse body = some expression)
    {args : List UInt64} (len : args.length = arity) {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval body args.reverse value)
    (name : Lean.Name) (exportName : Option String) :
    (scalarFunc name exportName arity expression).ScalarEval args value := by
  subst arity
  have heval := extractScalarExpr_correct semantics compiled (scalarArgumentLocals args [0])
  have hwrite : LeanExe.IR.ScalarStore.write (args ++ [0]) args.length value =
      some ((args ++ [0]).set args.length value) := by
    simp [LeanExe.IR.ScalarStore.write]
  refine .run (afterBody := (args ++ [0]).set args.length value)
    (afterResult := (args ++ [0]).set args.length value) rfl (by simp [scalarFunc]) ?_ rfl ?_
  · simpa [scalarFunc] using LeanExe.IR.Stmt.ScalarEval.assign heval hwrite
  · exact .local (LeanExe.IR.ScalarStore.read_write_same hwrite)

theorem extractScalarFunc_accepts {type value : Lean.Expr}
    (supported : LeanExe.Source.Scalar.DeclarationSupported type value)
    (name : Lean.Name) (exportName : Option String) :
    ∃ func, extractScalarFunc name exportName type value = some func := by
  obtain ⟨arity, body, signature, lambdas, supportedBody⟩ := supported
  rcases supportedBody with supportedBody | supportedBody | supportedBody
  ·
    obtain ⟨expression, compiled⟩ := extractScalarExpr_accepts supportedBody
      (List.range arity).reverse (by simp)
    exact ⟨scalarFunc name exportName arity expression,
      by simp [extractScalarFunc, scalarArity_accepts signature, lambdas, compiled]⟩
  ·
    let locals := (List.range arity).reverse.map fun slot => ScalarBinding.word (.local slot)
    obtain ⟨plan, compiled⟩ := extractScalarRangeWith_accepts supportedBody locals arity
      (by simp [locals, List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const'])
      (by intro binding member; obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member; trivial)
    have excluded := rangeSupported_excludes_pure supportedBody locals
    exact ⟨plan.func name exportName arity, by
      simp only [extractScalarFunc, scalarArity_accepts signature, lambdas, bind, Option.bind, extractScalarExpr]
      rw [excluded]
      rw [compiled]
      rfl⟩

  · let locals := (List.range arity).reverse.map fun slot => ScalarBinding.word (.local slot)
    obtain ⟨plan, compiled⟩ := extractScalarRangeExitWith_accepts supportedBody locals arity
      (by simp [locals, List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const'])
      (by intro binding member; obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member; trivial)
    have excluded := rangeExitSupported_excludes_pure supportedBody locals
    cases rangeCase : extractScalarRangeWith locals arity body with
    | some yielding =>
      exact ⟨yielding.func name exportName arity, by
        simp only [extractScalarFunc, scalarArity_accepts signature, lambdas, bind, Option.bind, extractScalarExpr]
        rw [excluded, rangeCase]
        rfl⟩
    | none =>
      exact ⟨plan.func name exportName arity, by
        simp only [extractScalarFunc, scalarArity_accepts signature, lambdas, bind, Option.bind, extractScalarExpr]
        rw [excluded, rangeCase, compiled]
        rfl⟩

/-- Actual argument locals match the source environment for any trailing locals. -/
theorem scalarArgumentBindings (args extra : List UInt64) :
    ScalarBindingsMatch ((List.range args.length).reverse.map fun slot => .word (.local slot))
      (args.reverse.map LeanExe.Source.Scalar.Value.word) (args ++ extra) := by
  intro index binding value he hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he hv
  obtain ⟨slot, hs, rfl⟩ := he
  obtain ⟨word, hw, rfl⟩ := hv
  exact LeanExe.IR.Expr.ScalarEval.local ((scalarArgumentLocals args extra _ _ hs).trans hw)

/-- Source value and loop facts for a successfully extracted range function. -/
theorem rangeFunc_meaning {body : Lean.Expr} {arity : Nat} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith
      ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan)
    {args : List UInt64} (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Eval body args.reverse value ∧ plan.Meaning args value := by
  subst arity
  apply extractScalarRangeWith_correct args (args.reverse.map LeanExe.Source.Scalar.Value.word) compiled
  · simp [List.map_map, Function.comp_def, LeanExe.Source.Scalar.Value.kind, ScalarBinding.kind, List.map_const']
  · intro accumulator index stop
    exact scalarArgumentBindings args [accumulator, UInt64.ofNat index, stop]
  · intro binding member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    trivial

/-- Source value and iteration facts for a successfully extracted early-exit range. -/
theorem rangeExitFunc_meaning {body : Lean.Expr} {arity : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith
      ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan)
    {args : List UInt64} (len : args.length = arity) :
    ∃ value, LeanExe.Source.Scalar.Range.Exit.Eval body
      (args.reverse.map LeanExe.Source.Scalar.Value.word) value ∧ plan.Meaning args value := by
  subst arity
  apply extractScalarRangeExitWith_correct args (args.reverse.map LeanExe.Source.Scalar.Value.word) compiled
  · simp [List.map_map, Function.comp_def, LeanExe.Source.Scalar.Value.kind, ScalarBinding.kind, List.map_const']
  · intro accumulator index stop flag
    exact scalarArgumentBindings args [accumulator, UInt64.ofNat index, stop, flag]
  · intro binding member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    trivial

/-- Every successful scalar declaration extraction preserves application of
the original source term on every argument list of the declared arity. -/
theorem extractScalarFunc_correct {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func)
    (args : List UInt64) (len : args.length = func.params) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ func.ScalarEval args value := by
  obtain ⟨arity, body, _, hb, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, he, rfl⟩ | ⟨plan, hp, rfl⟩ | ⟨plan, hp, rfl⟩
  · have hlen : args.length = arity := len
    have supported := extractScalarExpr_supported he
    obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp [hlen])
    refine ⟨value, ?_, scalarFunc_correct he hlen semantics name exportName⟩
    exact LeanExe.Source.Scalar.apply_of_collectLambdas args []
      (by simpa [hlen] using hb) (by simpa using semantics)
  · have hlen : args.length = arity := len
    obtain ⟨value, semantics, meaning⟩ := rangeFunc_meaning hp hlen
    refine ⟨value, ?_, ?_⟩
    · exact LeanExe.Source.Scalar.apply_of_collectLambdas args []
        (by simpa [hlen] using hb) (by simpa using semantics)
    · simpa [hlen] using meaning.func_correct name exportName

  · have hlen : args.length = arity := len
    obtain ⟨value, semantics, meaning⟩ := rangeExitFunc_meaning hp hlen
    refine ⟨value, ?_, ?_⟩
    · exact LeanExe.Source.Scalar.apply_exit_of_collectLambdas args []
        (by simpa [hlen] using hb) (by simpa using semantics)
    · simpa [hlen] using meaning.func_correct name exportName

end LeanExe.Extract.Core
