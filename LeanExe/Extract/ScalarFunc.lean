import LeanExe.Extract.ScalarExpr
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
  let expression ← extractScalarExpr (List.range arity).reverse body
  pure (scalarFunc name exportName arity expression)

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
  obtain ⟨expression, compiled⟩ := extractScalarExpr_accepts supportedBody
    (List.range arity).reverse (by simp)
  exact ⟨scalarFunc name exportName arity expression,
    by simp [extractScalarFunc, scalarArity_accepts signature, lambdas, compiled]⟩

/-- Every successful scalar declaration extraction preserves application of
the original source term on every argument list of the declared arity. -/
theorem extractScalarFunc_correct {name : Lean.Name} {exportName : Option String}
    {type source : Lean.Expr} {func : LeanExe.IR.Func}
    (compiled : extractScalarFunc name exportName type source = some func)
    (args : List UInt64) (len : args.length = func.params) :
    ∃ value, LeanExe.Source.Scalar.Apply source [] args value ∧ func.ScalarEval args value := by
  cases hn : scalarArity? type with
  | none => simp [extractScalarFunc, hn] at compiled
  | some arity =>
    cases hb : collectLambdas source arity with
    | none => simp [extractScalarFunc, hn, hb] at compiled
    | some body =>
      cases he : extractScalarExpr (List.range arity).reverse body with
      | none => simp [extractScalarFunc, hn, hb, he] at compiled
      | some expression =>
        have hf : scalarFunc name exportName arity expression = func := by
          simpa [extractScalarFunc, hn, hb, he] using compiled
        subst func
        have hlen : args.length = arity := len
        have supported := extractScalarExpr_supported he
        obtain ⟨value, semantics⟩ := supported.evaluates args.reverse (by simp [hlen])
        refine ⟨value, ?_, scalarFunc_correct he hlen semantics name exportName⟩
        exact LeanExe.Source.Scalar.apply_of_collectLambdas args []
          (by simpa [hlen] using hb) (by simpa using semantics)

end LeanExe.Extract.Core
