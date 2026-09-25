import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.ScalarStepBindings
import LeanExe.Extract.ScalarStepSyntax
import LeanExe.Source.ScalarStep

namespace LeanExe.Extract.Core

/-- Compile a step to a value and an exit decision together. Distinct binding
kinds keep scalar-valued functions and step-valued continuations separate. -/
def extractScalarStepWith (locals : List ScalarStepBinding) : Lean.Expr → Option ScalarStepCode
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))))
      (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
      (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value) => do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      pure { value, done := .u64 0 }
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))))
      (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
      (.app (.app (.const ``ForInStep.done [.zero]) (.const ``UInt64 [])) value) => do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      pure { value, done := .u64 1 }
  | .letE _ (.const ``UInt64 []) value body _ => do
      let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      extractScalarStepWith (.scalar (.word bound) :: locals) body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) (.const ``UInt64 []))
        (.app (.const ``ForInStep [.zero]) (.const ``UInt64 []))) value)
      (.lam _ (.const ``UInt64 []) body _) => do
      let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      extractScalarStepWith (.scalar (.word bound) :: locals) body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match scalarStepResultType? type with
      | none => none
      | some _ =>
          match comparison? condition evidence with
          | none => none
          | some (op, left, right) => do
              let a ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) left
              let b ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) right
              let t ← extractScalarStepWith locals onTrue
              let e ← extractScalarStepWith locals onFalse
              pure { value := .ite (lowerComparison op a b) t.value e.value
                     done := .ite (lowerComparison op a b) t.done e.done }
  | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
      (.lam _ (.const ``UInt64 []) value _) body _ =>
      match scalarResultType? resultType with
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: locals.map ScalarStepBinding.toScalar) value
          let function := ScalarBinding.function false fun argument =>
            extractScalarExprWith (.word argument :: locals.map ScalarStepBinding.toScalar) value
          extractScalarStepWith (.scalar function :: locals) body
      | none =>
          match scalarStepResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: locals) value
              let function := ScalarStepBinding.function false fun argument =>
                extractScalarStepWith (.scalar (.word argument) :: locals) value
              extractScalarStepWith (function :: locals) body
  | .letE _ (.forallE _ (.const ``Unit [])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
      match scalarResultType? resultType with
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals.map ScalarStepBinding.toScalar) value
          let function := ScalarBinding.function true fun argument =>
            extractScalarExprWith (.word argument :: .unit :: locals.map ScalarStepBinding.toScalar) value
          extractScalarStepWith (.scalar function :: locals) body
      | none =>
          match scalarStepResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: .scalar .unit :: locals) value
              let function := ScalarStepBinding.function true fun argument =>
                extractScalarStepWith (.scalar (.word argument) :: .scalar .unit :: locals) value
              extractScalarStepWith (function :: locals) body
  | .app (.app (.bvar index) (.const ``Unit.unit [])) argument => do
      let function ← locals[index]?.bind (ScalarStepBinding.function? true)
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) argument
      function value
  | .app (.bvar index) argument => do
      let function ← locals[index]?.bind (ScalarStepBinding.function? false)
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) argument
      function value
  | .mdata _ body => extractScalarStepWith locals body
  | _ => none
termination_by source => sizeOf source

end LeanExe.Extract.Core
