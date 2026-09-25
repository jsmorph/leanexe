import LeanExe.Extract.ScalarFunc
namespace AnnotatedLetFailure
def annotatedLetShadow (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y
   let value : Id (Id UInt64) := Id.run value * 3
   let flag : Id Bool := Id.run (Id.run value) == y
   flag || x == 0).toUInt64 + y

end AnnotatedLetFailure
run_elab do
  let env ← Lean.getEnv
  let some info := env.find? `AnnotatedLetFailure.annotatedLetShadow | throwError "missing"
  Lean.logInfo m!"{info.value!}"
  Lean.logInfo m!"{repr info.value!}"
  let rec inspect : Lean.Expr → Lean.Elab.Term.TermElabM Unit
    | .app (.const ``Bool.toUInt64 []) value => do
      let some parsed := LeanExe.Extract.Core.booleanLocalOperands? value | throwError "Boolean parser rejected"
      Lean.logInfo m!"variables: {parsed.variables}"
      for operand in parsed.operands do
        let result := LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1), .word (.u64 2)] operand
        Lean.logInfo m!"operand accepted: {result.isSome}"
        if result.isNone then
          Lean.logInfo m!"{operand}"
          Lean.logInfo m!"{repr operand}"
    | .app a b => inspect a *> inspect b
    | .lam _ _ body _ => inspect body
    | _ => pure ()
  inspect info.value!
