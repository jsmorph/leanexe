import LeanExe.Extract.ScalarRangeCorrectness
import LeanExe.Extract.ScalarRangeExitCorrectness
import LeanExe.Source.ScalarFunction

namespace LeanExe.Extract.Core

/-- Exact UInt64 parameters and either a UInt64 or Bool public result. -/
def scalarSignature? : Lean.Expr → Option (Nat × LeanExe.Source.Scalar.PublicResult)
  | .const ``UInt64 [] => some (0, .word)
  | .const ``Bool [] => some (0, .boolean)
  | .forallE _ (.const ``UInt64 []) body _ =>
      (scalarSignature? body).map fun signature => (signature.1 + 1, signature.2)
  | .mdata _ body => scalarSignature? body
  | _ => none

theorem scalarSignature_accepts {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (h : LeanExe.Source.Scalar.Arrow type arity result) :
    scalarSignature? type = some (arity, result) := by
  induction h with
  | result kind => cases kind <;> rfl
  | arg _ ih => simp [scalarSignature?, ih]
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
  let (arity, result) ← scalarSignature? type
  let body ← collectLambdas value arity
  match extractScalarExpr (List.range arity).reverse (result.encode body) with
  | some expression => pure (scalarFunc name exportName arity expression)
  | none =>
      match result with
      | .boolean => none
      | .word =>
          let locals := (List.range arity).reverse.map fun slot => ScalarBinding.word (.local slot)
          match extractScalarRangeWith locals arity body with
          | some plan => pure (plan.func name exportName arity)
          | none => do
              let plan ← extractScalarRangeExitWith locals arity body
              pure (plan.func name exportName arity)

/-- Successful extraction selects a pure expression or a word-valued range.
The original signature and lambda binders determine the result encoding. -/
theorem extractScalarFunc_cases {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    ∃ arity result body, scalarSignature? type = some (arity, result) ∧
      collectLambdas source arity = some body ∧
      ((∃ expression, extractScalarExpr (List.range arity).reverse (result.encode body) = some expression ∧
          func = scalarFunc name exportName arity expression) ∨
        (result = .word ∧ ∃ plan, extractScalarRangeWith
          ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan ∧
          func = plan.func name exportName arity) ∨
        (result = .word ∧ ∃ plan, extractScalarRangeExitWith
          ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body = some plan ∧
          func = plan.func name exportName arity)) := by
  unfold extractScalarFunc at compiled
  simp only [bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨⟨arity, result⟩, ha, body, hb, compiled⟩ := compiled
  refine ⟨arity, result, body, ha, hb, ?_⟩
  cases pureCase : extractScalarExpr (List.range arity).reverse (result.encode body) with
  | some expression =>
    simp only [pureCase, pure, Option.some.injEq] at compiled
    exact .inl ⟨expression, rfl, compiled.symm⟩
  | none =>
    simp only [pureCase] at compiled
    cases result with
    | boolean => contradiction
    | word =>
      cases rangeCase : extractScalarRangeWith
          ((List.range arity).reverse.map fun slot => .word (.local slot)) arity body with
      | some plan =>
        simp only [rangeCase, pure, Option.some.injEq] at compiled
        exact .inr (.inl ⟨rfl, plan, rfl, compiled.symm⟩)
      | none =>
        simp only [rangeCase, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
        obtain ⟨plan, hp, same⟩ := compiled
        exact .inr (.inr ⟨rfl, plan, hp, same.symm⟩)

theorem extractScalarFunc_properties {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func) :
    func.exportName = exportName ∧ func.params ≤ func.locals ∧ func.results = [.local func.params] := by
  obtain ⟨arity, result, body, _, _, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩ | ⟨rfl, plan, _, rfl⟩
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
  obtain ⟨arity, result, body, signature, lambdas, supportedBody⟩ := supported
  rcases supportedBody with supportedBody | ⟨rfl, supportedBody | supportedBody⟩
  ·
    obtain ⟨expression, compiled⟩ := extractScalarExpr_accepts supportedBody
      (List.range arity).reverse (by simp)
    exact ⟨scalarFunc name exportName arity expression,
      by simp [extractScalarFunc, scalarSignature_accepts signature, lambdas, compiled]⟩
  ·
    let locals := (List.range arity).reverse.map fun slot => ScalarBinding.word (.local slot)
    obtain ⟨plan, compiled⟩ := extractScalarRangeWith_accepts supportedBody locals arity
      (by simp [locals, List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const'])
      (by intro binding member; obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member; trivial)
    have excluded := rangeSupported_excludes_pure supportedBody locals
    exact ⟨plan.func name exportName arity, by
      simp only [extractScalarFunc, scalarSignature_accepts signature, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode, extractScalarExpr]
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
        simp only [extractScalarFunc, scalarSignature_accepts signature, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode, extractScalarExpr]
        rw [excluded, rangeCase]
        rfl⟩
    | none =>
      exact ⟨plan.func name exportName arity, by
        simp only [extractScalarFunc, scalarSignature_accepts signature, lambdas, bind, Option.bind, LeanExe.Source.Scalar.PublicResult.encode, extractScalarExpr]
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
  obtain ⟨arity, result, body, _, hb, cases⟩ := extractScalarFunc_cases compiled
  rcases cases with ⟨expression, he, rfl⟩ | ⟨rfl, plan, hp, rfl⟩ | ⟨rfl, plan, hp, rfl⟩
  · have hlen : args.length = arity := len
    have supported := extractScalarExpr_supported he
    obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp [hlen])
    refine ⟨value, ?_, scalarFunc_correct he hlen semantics name exportName⟩
    exact LeanExe.Source.Scalar.apply_encoded_of_collectLambdas result args []
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

/-- A public Bool result always uses the checked Boolean body conversion. -/
theorem extractScalarFunc_boolean_case {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func} {arity : Nat}
    (compiled : extractScalarFunc name exportName type source = some func)
    (signature : scalarSignature? type = some (arity, .boolean)) :
    ∃ body expression, collectLambdas source arity = some body ∧
      extractScalarExpr (List.range arity).reverse
        (.app (.const ``Bool.toUInt64 []) body) = some expression ∧
      func = scalarFunc name exportName arity expression := by
  obtain ⟨foundArity, result, body, parsed, lambdas, branches⟩ := extractScalarFunc_cases compiled
  have same := Option.some.inj (parsed.symm.trans signature)
  cases same
  rcases branches with ⟨expression, extracted, same⟩ | ⟨impossible, _⟩ | ⟨impossible, _⟩
  · exact ⟨body, expression, lambdas, extracted, same⟩
  · cases impossible
  · cases impossible

/-- Every admitted public Bool function returns the native flag encoded as zero
or one, for every argument list of the declared arity. -/
theorem extractScalarFunc_boolean_correct {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func} {arity : Nat}
    (compiled : extractScalarFunc name exportName type source = some func)
    (signature : scalarSignature? type = some (arity, .boolean))
    (args : List UInt64) (len : args.length = arity) :
    ∃ flag : Bool, LeanExe.Source.Scalar.Apply source [] args flag.toUInt64 ∧
      func.ScalarEval args flag.toUInt64 := by
  obtain ⟨body, expression, lambdas, extracted, rfl⟩ := extractScalarFunc_boolean_case compiled signature
  have supported := extractScalarExpr_supported extracted
  obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp [len])
  obtain ⟨flag, rfl⟩ := semantics.booleanConversion_result
  refine ⟨flag, ?_, scalarFunc_correct extracted len semantics name exportName⟩
  exact LeanExe.Source.Scalar.apply_boolean_of_collectLambdas args []
    (by simpa [len] using lambdas) (by simpa using semantics)

end LeanExe.Extract.Core
