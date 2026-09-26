import LeanExe.Extract.ScalarPredicateInput
import LeanExe.Extract.ScalarManyStepFunction
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
      type) body =>
      match scalarStepResultType? type with
      | none => none
      | some _ => extractScalarStepWith locals body
  | .letE _ (.const ``Bool []) value body _ =>
      match booleanLocalOperands? value with
      | none => none
      | some expression => do
          let c ← extractBooleanLocalWith (locals.map ScalarStepBinding.toScalar) expression
            (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
          extractScalarStepWith (.scalar (.boolean (guardWord c)) :: locals) body
  | .letE _ (.const ``UInt64 []) value body _ => do
      let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      extractScalarStepWith (.scalar (.word bound) :: locals) body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) (.const ``Bool []))
        type) value)
      (.lam _ (.const ``Bool []) body _) =>
      match scalarStepResultType? type with
      | none => none
      | some _ =>
          match booleanAction? value with
          | none => none
          | some action => do
              let c ← extractBooleanLocalWith (locals.map ScalarStepBinding.toScalar) action.leaf
                (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
              extractScalarStepWith (.scalar (.boolean (guardWord c)) :: locals) body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) (.const ``UInt64 []))
        type) value)
      (.lam _ (.const ``UInt64 []) body _) =>
      match scalarStepResultType? type with
      | none => none
      | some _ => do
          let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
          extractScalarStepWith (.scalar (.word bound) :: locals) body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match scalarStepResultType? type with
      | none => none
      | some _ =>
          match comparison? condition evidence with
          | none =>
              match compoundGuard? condition evidence with
              | none =>
                  match booleanLocalGuard? condition evidence with
                  | none => none
                  | some guard => do
                      let c ← extractBooleanLocalWith (locals.map ScalarStepBinding.toScalar) guard.value
                        (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
                      let t ← extractScalarStepWith locals onTrue
                      let e ← extractScalarStepWith locals onFalse
                      pure { value := .ite c t.value e.value, done := .ite c t.done e.done }
              | some guard => do
                  let c ← extractGuard guard.tree (fun operand _ =>
                    extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
                  let t ← extractScalarStepWith locals onTrue
                  let e ← extractScalarStepWith locals onFalse
                  pure { value := .ite c t.value e.value, done := .ite c t.done e.done }
          | some (op, left, right) => do
              let a ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) left
              let b ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) right
              let t ← extractScalarStepWith locals onTrue
              let e ← extractScalarStepWith locals onFalse
              pure { value := .ite (lowerComparison op a b) t.value e.value
                     done := .ite (lowerComparison op a b) t.done e.done }
  | .letE _ (.forallE firstTypeName (.const ``UInt64 [])
      (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) body _ =>
      match scalarResultType? resultType with
      | none =>
          match scalarStepResultType? resultType with
          | none =>
              match scalarManyFunction?
                  (.forallE firstTypeName (.const ``UInt64 [])
                    (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
                  (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
              | none =>
                  match _stepFunction : scalarManyStepFunction?
                      (.forallE firstTypeName (.const ``UInt64 [])
                        (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
                      (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
                  | none => none
                  | some shape => do
                      let _ ← extractScalarStepWith
                        (List.replicate shape.arity (.scalar (.word (.u64 0))) ++ locals) shape.body
                      let function := ScalarStepBinding.manyFunction shape.arity fun arguments =>
                        extractScalarStepWith
                          (arguments.reverse.map (fun argument => .scalar (.word argument)) ++ locals) shape.body
                      extractScalarStepWith (function :: locals) body
              | some shape => do
                  let _ ← extractScalarExprWith
                    (List.replicate shape.arity (.word (.u64 0)) ++ locals.map ScalarStepBinding.toScalar) shape.body
                  let function := ScalarBinding.manyFunction shape.arity fun arguments =>
                    extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals.map ScalarStepBinding.toScalar) shape.body
                  extractScalarStepWith (.scalar function :: locals) body
          | some _ => do
              let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: .scalar (.word (.u64 0)) :: locals) value
              let function := ScalarStepBinding.binaryFunction fun first second =>
                extractScalarStepWith (.scalar (.word second) :: .scalar (.word first) :: locals) value
              extractScalarStepWith (function :: locals) body
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals.map ScalarStepBinding.toScalar) value
          let function := ScalarBinding.binaryFunction fun first second =>
            extractScalarExprWith (.word second :: .word first :: locals.map ScalarStepBinding.toScalar) value
          extractScalarStepWith (.scalar function :: locals) body
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
          | none =>
              match booleanType? resultType with
              | none => none
              | some _ => do
                  let expression ← booleanLocalOperands? value
                  let _ ← extractBooleanLocalWith (.word (.u64 0) :: locals.map ScalarStepBinding.toScalar) expression
                    (fun operand _ => extractScalarExprWith (.word (.u64 0) :: locals.map ScalarStepBinding.toScalar) operand)
                  let function := ScalarBinding.predicateFunction fun argument => do
                    let condition ← extractBooleanLocalWith (.word argument :: locals.map ScalarStepBinding.toScalar) expression
                      (fun operand _ => extractScalarExprWith (.word argument :: locals.map ScalarStepBinding.toScalar) operand)
                    pure (guardWord condition)
                  extractScalarStepWith (.scalar function :: locals) body
          | some _ => do
              let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: locals) value
              let function := ScalarStepBinding.function false fun argument =>
                extractScalarStepWith (.scalar (.word argument) :: locals) value
              extractScalarStepWith (function :: locals) body
  | .letE _ (.forallE _ (.const ``Unit [])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _
  | .letE _ (.forallE _ (.const ``PUnit [.succ .zero])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``PUnit [.succ .zero]) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
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
  | .app (.app (.bvar index) (.const ``Unit.unit [])) argument
  | .app (.app (.bvar index) (.const ``PUnit.unit [.succ .zero])) argument => do
      let function ← locals[index]?.bind (ScalarStepBinding.function? true)
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) argument
      function value
  | .app (.app (.bvar index) first) second => do
      let function ← locals[index]?.bind ScalarStepBinding.binaryFunction?
      let a ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) first
      let b ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) second
      function a b
  | .app (.bvar index) argument =>
      match locals[index]?.bind (ScalarStepBinding.function? false) with
      | some function => do
          let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) argument
          function value
      | none =>
          match locals[index]?.bind ScalarStepBinding.booleanFunction? with
          | some function => do
              let expression ← booleanLocalOperands? argument
              let c ← extractBooleanLocalWith (locals.map ScalarStepBinding.toScalar) expression
                (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
              function (guardWord c)
          | none => do
              let function ← locals[index]?.bind ScalarStepBinding.resultFunction?
              let value ← extractScalarStepWith locals argument
              function value
  | .app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value => do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      pure { value, done := .u64 0 }
  | .app (.app (.const ``ForInStep.done [.zero]) (.const ``UInt64 [])) value => do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) value
      pure { value, done := .u64 1 }
  | .bvar index => locals[index]?.bind ScalarStepBinding.result?
  | .app (.app (.const ``Id.run [.zero]) type) body =>
      match scalarStepResultType? type with
      | none => none
      | some _ => extractScalarStepWith locals body
  | .letE _ (.forallE _ (.const ``Bool []) resultType _)
      (.lam _ (.const ``Bool []) value _) body _ =>
      match scalarResultType? resultType with
      | some _ => do
          let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals.map ScalarStepBinding.toScalar) value
          let function := ScalarBinding.booleanFunction fun argument =>
            extractScalarExprWith (.boolean argument :: locals.map ScalarStepBinding.toScalar) value
          extractScalarStepWith (.scalar function :: locals) body
      | none =>
          match scalarStepResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarStepWith (.scalar (.boolean (.u64 0)) :: locals) value
              let function := ScalarStepBinding.booleanFunction fun argument =>
                extractScalarStepWith (.scalar (.boolean argument) :: locals) value
              extractScalarStepWith (function :: locals) body
  | .letE name (.forallE typeName input output typeBi) (.lam paramName domain value paramBi) body nondep =>
      if input = domain then
        match scalarStepResultType? input, scalarStepResultType? output with
        | some _, some _ => do
            let _ ← extractScalarStepWith (.result ⟨.u64 0, .u64 0⟩ :: locals) value
            let function := ScalarStepBinding.resultFunction fun argument =>
              extractScalarStepWith (.result argument :: locals) value
            extractScalarStepWith (function :: locals) body
        | _, _ =>
            match _annotation : predicateInputTypes? input domain output with
            | none => none
            | some types => extractScalarStepWith locals
                (LeanExe.Source.Scalar.predicateInputExpr types.1 types.2
                  name typeName paramName typeBi paramBi value body nondep)
      else none
  | .letE name (.app (.const ``Id [.zero]) type) value body nondep =>
      extractScalarStepWith locals (.letE name type value body nondep)
  | .letE _ type value body _ =>
      match scalarStepResultType? type with
      | none => none
      | some _ => do
          let bound ← extractScalarStepWith locals value
          extractScalarStepWith (.result bound :: locals) body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      if input = domain then
        match scalarStepResultType? input, scalarStepResultType? output with
        | some _, some _ => do
            let bound ← extractScalarStepWith locals value
            extractScalarStepWith (.result bound :: locals) body
        | _, _ => none
      else none
  | .mdata _ body => extractScalarStepWith locals body
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
      condition) evidence) (.lam _ trueDomain onTrue _)) (.lam _ falseDomain onFalse _) =>
      match scalarStepResultType? type with
      | none => none
      | some _ =>
          match _guard : dependentGuard? condition evidence trueDomain falseDomain with
          | none =>
              match _booleanGuard : booleanLocalDependentGuard? condition evidence trueDomain falseDomain with
              | none => none
              | some guard => do
                  let c ← extractBooleanLocalWith (locals.map ScalarStepBinding.toScalar) guard.value
                    (fun operand _member => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
                  let t ← extractScalarStepWith (.scalar .unit :: locals) onTrue
                  let e ← extractScalarStepWith (.scalar .unit :: locals) onFalse
                  pure { value := .ite c t.value e.value, done := .ite c t.done e.done }
          | some guard => do
              let c ← extractGuard guard (fun operand _member => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
              let t ← extractScalarStepWith (.scalar .unit :: locals) onTrue
              let e ← extractScalarStepWith (.scalar .unit :: locals) onFalse
              pure { value := .ite c t.value e.value, done := .ite c t.done e.done }
  | .app (.app head first) second => do
      let call ← scalarManyCall? head first second
      let function ← locals[call.index]?.bind (ScalarStepBinding.manyFunction? call.arity)
      let arguments ← extractScalarArguments call.arguments
        (fun operand _ => extractScalarExprWith (locals.map ScalarStepBinding.toScalar) operand)
      function arguments
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have bound := scalarManyStepFunction_body_size _stepFunction; simp_all; omega)
    | (obtain ⟨hi, hd, ho⟩ := predicateInputTypes_sound _annotation
       simp_all [LeanExe.Source.Scalar.predicateInputExpr, LeanExe.Source.Scalar.ResultType.expr]
       omega)

end LeanExe.Extract.Core
