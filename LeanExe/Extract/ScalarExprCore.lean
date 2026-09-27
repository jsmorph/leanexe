import LeanExe.Extract.ScalarBooleanScopeBinding
import LeanExe.Extract.ScalarBooleanRelationSelection
import LeanExe.Extract.ScalarBooleanGuardedSelection
import LeanExe.Extract.ScalarBooleanSelected
import LeanExe.Extract.ScalarBooleanRelated
import LeanExe.Extract.ScalarBooleanJoined
import LeanExe.Extract.ScalarBooleanNegated
import LeanExe.Extract.ScalarBooleanWrapped
import LeanExe.Extract.ScalarBooleanScopeGuard
import LeanExe.Extract.ScalarBooleanHelper
import LeanExe.Extract.ScalarBooleanCondition
import Lean.Meta.Tactic.FunInd
import LeanExe.Extract.ScalarExtractionSize
import LeanExe.Extract.ScalarBooleanBind
import LeanExe.Extract.ScalarTypedLiteralInstance
import LeanExe.Extract.ScalarCall
import LeanExe.Extract.ScalarArguments
import LeanExe.Extract.ScalarManyFunction
import LeanExe.Extract.ScalarHead
import LeanExe.Extract.ScalarComplement
import LeanExe.Extract.ScalarExtremum
import LeanExe.Extract.ScalarDo
import LeanExe.Extract.ScalarBooleanPredicatePropositionChoice
import LeanExe.Extract.ScalarBooleanPredicateBindings
import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarBooleanLocalDependentBranch
import LeanExe.Extract.ScalarDependentBranch
import LeanExe.Extract.ScalarGuard
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

private theorem scalarResultType_guard_ite {type : Lean.Expr} {annotation : LeanExe.Source.Scalar.ResultType}
    (parsed : scalarResultType? type = some annotation) :
    LeanExe.Source.Scalar.guardOperandOverhead ≤ sizeOf ("ite" : String) + sizeOf type := by
  rw [scalarResultType_sound parsed]
  exact Nat.le_trans LeanExe.Source.Scalar.guardOperandOverhead_ite_word
    (Nat.add_le_add_left annotation.word_size _)

private theorem scalarResultType_guard_dite {type : Lean.Expr} {annotation : LeanExe.Source.Scalar.ResultType}
    (parsed : scalarResultType? type = some annotation) :
    LeanExe.Source.Scalar.guardOperandOverhead ≤ sizeOf ("dite" : String) + sizeOf type := by
  rw [scalarResultType_sound parsed]
  exact Nat.le_trans LeanExe.Source.Scalar.guardOperandOverhead_dite_word
    (Nat.add_le_add_left annotation.word_size _)

set_option maxHeartbeats 300000 in
/-- Compile pure, total scalar expressions with an environment of already
compiled bindings. Substitution removes source lets without introducing effects.
Bindings may be duplicated or unused in the output; this is valid only for this
pure arithmetic fragment. The source semantics still evaluates each binding. -/
def extractScalarExprWith (locals : List ScalarBinding) : Lean.Expr → Option LeanExe.IR.Expr
  | .bvar index => locals[index]?.bind ScalarBinding.word?
  | .app (.const ``UInt64.ofNat _) (.lit (.natVal n)) => some (.u64 n)
  | .app (.const ``UInt64.ofNat _) (.bvar index) => locals[index]?.bind ScalarBinding.natural?
  | .app (.const ``UInt64.ofNat _) numeral =>
      match naturalLiteral? numeral with
      | some n => some (.u64 n)
      | none => none
  | .app (.const ``Nat.toUInt64 []) (.bvar index) => locals[index]?.bind ScalarBinding.natural?
  | .app (.const ``Nat.toUInt64 []) numeral =>
      match naturalLiteral? numeral with
      | some n => some (.u64 n)
      | none => none
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) sourceType) numeral) evidence =>
      match scalarResultType? sourceType with
      | none => none
      | some type =>
          match naturalLiteral? numeral with
          | some n => if typedLiteralInstance? n type evidence then some (.u64 n) else none
          | none => none
  | .app (.app (.const ``Id.run [.zero]) sourceType) body =>
      match scalarResultType? sourceType with
      | none => none
      | some _ => extractScalarExprWith locals body
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) sourceType) body =>
      match scalarResultType? sourceType with
      | none => none
      | some _ => extractScalarExprWith locals body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match scalarBindTypes? input domain output with
      | none =>
          match booleanBindType? scalarResultType? input domain output with
          | none => none
          | some _ =>
              match _action : booleanAction? value with
              | none => none
              | some action => do
                  let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) action.expr)
                  extractScalarExprWith (.boolean bound :: locals) body
      | some _ => do
          let bound ← extractScalarExprWith locals value
          extractScalarExprWith (.word bound :: locals) body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match _resultType : scalarResultType? type with
      | none => none
      | some _ =>
        match _h : comparison? condition evidence with
        | none =>
          match _g : compoundGuard? condition evidence with
          | none =>
            match _booleanGuard : booleanLocalGuard? condition evidence with
            | none =>
                match _scope : booleanScopeGuard? condition evidence with
                | none => none
                | some guard => do
                    let c ← extractScalarExprWith locals guard.operand
                    let t ← extractScalarExprWith locals onTrue
                    let e ← extractScalarExprWith locals onFalse
                    pure (.ite (wordGuard c) t e)
            | some guard => do
                let c ← if hasBooleanPredicate locals guard.value.functions then
                    extractBooleanCondition guard.form (fun input _member =>
                      extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input.expr))
                  else
                    extractBooleanLocalWith locals guard.value
                      (fun operand _member => extractScalarExprWith locals operand)
                let t ← extractScalarExprWith locals onTrue
                let e ← extractScalarExprWith locals onFalse
                pure (.ite c t e)
          | some guard => do
              let c ← extractGuard guard.tree (fun operand _member => extractScalarExprWith locals operand)
              let t ← extractScalarExprWith locals onTrue
              let e ← extractScalarExprWith locals onFalse
              pure (.ite c t e)
        | some (op, left, right) => do
            let a ← extractScalarExprWith locals left
            let b ← extractScalarExprWith locals right
            let t ← extractScalarExprWith locals onTrue
            let e ← extractScalarExprWith locals onFalse
            pure (.ite (lowerComparison op a b) t e)
  | .app (.app (.bvar index) (.const ``Unit.unit [])) argument
  | .app (.app (.bvar index) (.const ``PUnit.unit [.succ .zero])) argument => do
      let function ← locals[index]?.bind (ScalarBinding.function? true)
      let value ← extractScalarExprWith locals argument
      function value
  | .app (.app (.bvar index) first) second => do
      let function ← locals[index]?.bind ScalarBinding.binaryFunction?
      let a ← extractScalarExprWith locals first
      let b ← extractScalarExprWith locals second
      function a b
  | .app (.const ``UInt64.complement []) argument => do
      let value ← extractScalarExprWith locals argument
      pure (lowerComplement value)
  | .app (.app (.app (.const ``Complement.complement [.zero]) (.const ``UInt64 []))
      (.const ``instComplementUInt64 [])) argument => do
      let value ← extractScalarExprWith locals argument
      pure (lowerComplement value)
  | .app (.app (.app (.app (.const ``Min.min [.zero]) (.const ``UInt64 []))
      (.const ``instMinUInt64 [])) left) right => do
      let a ← extractScalarExprWith locals left
      let b ← extractScalarExprWith locals right
      pure (lowerExtremum .minimum a b)
  | .app (.app (.app (.app (.const ``Max.max [.zero]) (.const ``UInt64 []))
      (.const ``instMaxUInt64 [])) left) right => do
      let a ← extractScalarExprWith locals left
      let b ← extractScalarExprWith locals right
      pure (lowerExtremum .maximum a b)
  | .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
      condition) evidence) (.lam _ trueDomain onTrue _)) (.lam _ falseDomain onFalse _) =>
      match _resultType : scalarResultType? type with
      | none => none
      | some _ =>
          match _guard : dependentGuard? condition evidence trueDomain falseDomain with
          | none =>
              match _booleanGuard : booleanLocalDependentGuard? condition evidence trueDomain falseDomain with
              | none =>
                  match _scope : booleanScopeDependentGuard? condition evidence trueDomain falseDomain with
                  | none => none
                  | some guard => do
                      let c ← extractScalarExprWith locals guard.operand
                      let t ← extractScalarExprWith (.unit :: locals) onTrue
                      let e ← extractScalarExprWith (.unit :: locals) onFalse
                      pure (.ite (wordGuard c) t e)
              | some guard => do
                  let c ← if hasBooleanPredicate locals guard.value.functions then
                      extractBooleanCondition guard.form (fun input _member =>
                        extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input.expr))
                    else
                      extractBooleanLocalWith locals guard.value
                        (fun operand _member => extractScalarExprWith locals operand)
                  let t ← extractScalarExprWith (.unit :: locals) onTrue
                  let e ← extractScalarExprWith (.unit :: locals) onFalse
                  pure (.ite c t e)
          | some guard => do
              let c ← extractGuard guard (fun operand _member => extractScalarExprWith locals operand)
              let t ← extractScalarExprWith (.unit :: locals) onTrue
              let e ← extractScalarExprWith (.unit :: locals) onFalse
              pure (.ite c t e)
  | .app (.app head left) right =>
      match ScalarPrimitive.ofHead? head with
      | some op => do
          let a ← extractScalarExprWith locals left
          let b ← extractScalarExprWith locals right
          pure (op.lower a b)
      | none =>
          match _call : scalarManyCall? head left right with
          | none => none
          | some call => do
              let function ← locals[call.index]?.bind (ScalarBinding.manyFunction? call.arity)
              let arguments ← extractScalarArguments call.arguments
                (fun operand _member => extractScalarExprWith locals operand)
              function arguments
  | .letE _ (.const ``Bool []) value body _ => do
      let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      extractScalarExprWith (.boolean bound :: locals) body
  | .letE _ (.const ``UInt64 []) value body _ => do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (.word bound :: locals) body
  | .letE _ (.forallE firstTypeName (.const ``UInt64 [])
      (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) body _ =>
      match scalarResultType? resultType with
      | none =>
          match _function : scalarManyFunction?
              (.forallE firstTypeName (.const ``UInt64 [])
                (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
              (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
          | none => none
          | some shape => do
              let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
              let function := ScalarBinding.manyFunction shape.arity fun arguments =>
                extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
              extractScalarExprWith (function :: locals) body
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
          let function := ScalarBinding.binaryFunction fun first second =>
            extractScalarExprWith (.word second :: .word first :: locals) value
          extractScalarExprWith (function :: locals) body
  | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
      (.lam _ (.const ``UInt64 []) value _) body _ =>
      match scalarResultType? resultType with
      | none =>
          match booleanType? resultType with
          | none => none
          | some _ =>
              do
                let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
                  (.app (.const ``Bool.toUInt64 []) value)
                let function := ScalarBinding.predicateFunction fun argument =>
                  extractScalarExprWith (.word argument :: locals)
                    (.app (.const ``Bool.toUInt64 []) value)
                extractScalarExprWith (function :: locals) body
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
          let function := ScalarBinding.function false fun argument =>
            extractScalarExprWith (.word argument :: locals) value
          extractScalarExprWith (function :: locals) body
  | .letE _ (.forallE _ (.const ``Unit [])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _
  | .letE _ (.forallE _ (.const ``PUnit [.succ .zero])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``PUnit [.succ .zero]) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
      match scalarResultType? resultType with
      | none => none
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) value
          let function := ScalarBinding.function true fun argument =>
            extractScalarExprWith (.word argument :: .unit :: locals) value
          extractScalarExprWith (function :: locals) body
  | .app (.bvar index) argument =>
      match locals[index]?.bind (ScalarBinding.function? false) with
      | some function => do
          let value ← extractScalarExprWith locals argument
          function value
      | none => do
          let function ← locals[index]?.bind ScalarBinding.booleanFunction?
          let value ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) argument)
          function value
  | .letE _ (.forallE _ (.const ``Bool []) resultType _)
      (.lam _ (.const ``Bool []) value _) body _ =>
      match scalarResultType? resultType with
      | none =>
          match booleanType? resultType with
          | none => none
          | some _ =>
              do
                let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
                  (.app (.const ``Bool.toUInt64 []) value)
                let function := ScalarBinding.booleanPredicateFunction fun argument =>
                  extractScalarExprWith (.boolean argument :: locals)
                    (.app (.const ``Bool.toUInt64 []) value)
                extractScalarExprWith (function :: locals) body
      | some _ => do
          let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
          let function := ScalarBinding.booleanFunction fun argument =>
            extractScalarExprWith (.boolean argument :: locals) value
          extractScalarExprWith (function :: locals) body
  | .app (.const ``Bool.toUInt64 []) argument =>
      match _boolean : booleanLocalOperands? argument with
      | none =>
          match _wordHelper : booleanHelper? false argument with
          | some helper => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
                (.app (.const ``Bool.toUInt64 []) helper.body)
              let function := ScalarBinding.predicateFunction fun input =>
                extractScalarExprWith (.word input :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
              extractScalarExprWith (function :: locals) (.app (.const ``Bool.toUInt64 []) helper.continuation)
          | none =>
              match _booleanHelper : booleanHelper? true argument with
              | some helper => do
                  let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
                    (.app (.const ``Bool.toUInt64 []) helper.body)
                  let function := ScalarBinding.booleanPredicateFunction fun input =>
                    extractScalarExprWith (.boolean input :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
                  extractScalarExprWith (function :: locals) (.app (.const ``Bool.toUInt64 []) helper.continuation)
              | none =>
                  match _wrapper : booleanWrapped? argument with
                  | none =>
                      match _negated : booleanNegated? argument with
                      | none =>
                          match _joined : booleanJoined? argument with
                          | none =>
                              match _related : booleanRelated? argument with
                              | none =>
                                  match _selected : booleanSelected? argument with
                                  | none =>
                                      match _guarded : booleanGuardedSelection? argument with
                                      | none =>
                                          match _relation : booleanRelationSelection? argument with
                                          | none =>
                                              match _scopeWord : booleanScopeBinding? false argument with
                                              | some binding => do
                                                  let value ← extractScalarExprWith locals binding.value
                                                  extractScalarExprWith (.word value :: locals) (.app (.const ``Bool.toUInt64 []) binding.body)
                                              | none =>
                                                  match _scopeBoolean : booleanScopeBinding? true argument with
                                                  | none => none
                                                  | some binding => do
                                                      let value ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) binding.value)
                                                      extractScalarExprWith (.boolean value :: locals) (.app (.const ``Bool.toUInt64 []) binding.body)
                                          | some related => do
                                              let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.guard.left)
                                              let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.guard.right)
                                              let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.yes)
                                              let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.no)
                                              pure (booleanWordChoice 0 related.selection.guard.unequal left right yes no)
                                      | some guarded => do
                                          let condition ← extractGuard guarded.selection.guard.value
                                            (fun operand _member => extractScalarExprWith locals operand)
                                          let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) guarded.selection.yes)
                                          let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) guarded.selection.no)
                                          pure (booleanWordConditional 0 condition yes no)
                                  | some selected => do
                                      let condition ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.condition)
                                      let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.yes)
                                      let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.no)
                                      pure (.ite (wordGuard condition) yes no)
                              | some related => do
                                  let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.relation.left)
                                  let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.relation.right)
                                  pure (booleanWordEquality 0 related.relation.unequal left right)
                          | some joined => do
                              let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) joined.left)
                              let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) joined.right)
                              pure (booleanWordJunction 0 joined.operation left right)
                      | some negated => do
                          let body ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) negated.body)
                          pure (booleanWordNegation 1 body)
                  | some wrapped =>
                      extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) wrapped.body)
      | some expression =>
          match expression with
          | .predicate negations index input =>
              match locals[index]?.bind ScalarBinding.booleanPredicateFunction? with
              | some function => do
                  let argument ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input)
                  let result ← function argument
                  pure (booleanWordNegation negations result)
              | none => do
                  let condition ← extractBooleanLocalWith locals expression
                    (fun operand _member => extractScalarExprWith locals operand)
                  pure (guardWord condition)
          | .junction negations op left right =>
              if hasBooleanPredicate locals (left.functions ++ right.functions) then do
                let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
                let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
                pure (booleanWordJunction negations op first second)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .equality negations unequal left right
          | .relationDecision negations unequal left right =>
              if hasBooleanPredicate locals (left.functions ++ right.functions) then do
                let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
                let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
                pure (booleanWordEquality negations unequal first second)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .choice negations unequal left right yes no =>
              if hasBooleanPredicate locals (left.functions ++ (right.functions ++ (yes.functions ++ no.functions))) then do
                let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
                let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
                let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
                let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
                pure (booleanWordChoice negations unequal first second trueBranch falseBranch)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .dependentChoice negations _shape unequal left right yes no =>
              if hasBooleanPredicate locals (left.functions ++ (right.functions ++ (yes.functions ++ no.functions))) then do
                let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
                let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
                let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
                let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
                pure (booleanWordChoice negations unequal first second trueBranch falseBranch)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .proposition negations guard yes no =>
              if hasBooleanPredicate locals (yes.functions ++ no.functions) then do
                let test ← extractGuard guard.value (fun operand _member => extractScalarExprWith locals operand)
                let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
                let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
                pure (booleanWordConditional negations test trueBranch falseBranch)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .dependentProposition negations _shape guard yes no =>
              if hasBooleanPredicate locals (yes.functions ++ no.functions) then do
                let test ← extractGuard guard.value (fun operand _member => extractScalarExprWith locals operand)
                let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
                let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
                pure (booleanWordConditional negations test trueBranch falseBranch)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .wrapped negations wrapper body =>
              if hasBooleanPredicate locals body.functions then do
                let inner ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) body.expr)
                pure (booleanWordNegation negations inner)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .binding negations name form value body type =>
              if hasBooleanPredicate locals (value.functions ++ LeanExe.Source.Scalar.booleanLetVariables body.functions) then do
                let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value.expr)
                let result ← extractScalarExprWith (.boolean bound :: locals) (.app (.const ``Bool.toUInt64 []) body.expr)
                pure (booleanWordNegation negations result)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | .wordBinding negations name form value body type =>
              if hasBooleanPredicate locals (LeanExe.Source.Scalar.booleanLetVariables body.functions) then do
                let bound ← extractScalarExprWith locals value
                let result ← extractScalarExprWith (.word bound :: locals) (.app (.const ``Bool.toUInt64 []) body.expr)
                pure (booleanWordNegation negations result)
              else do
                let condition ← extractBooleanLocalWith locals expression
                  (fun operand _member => extractScalarExprWith locals operand)
                pure (guardWord condition)
          | _ => do
              let condition ← extractBooleanLocalWith locals expression
                (fun operand _member => extractScalarExprWith locals operand)
              pure (guardWord condition)
  | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
      if input = domain then
        match scalarResultType? input with
        | none =>
            match booleanType? input with
            | none => none
            | some _ => extractScalarExprWith locals (.letE name
                (.forallE typeName input resultType typeBi)
                (.lam paramName domain value paramBi) body nondep)
        | some _ =>
            match booleanType? resultType with
            | none => none
            | some _ => extractScalarExprWith locals (.letE name
                (.forallE typeName input resultType typeBi)
                (.lam paramName domain value paramBi) body nondep)
      else none
  | .letE name (.app (.const ``Id [.zero]) type) value body nondep =>
      extractScalarExprWith locals (.letE name type value body nondep)
  | .mdata _ body => extractScalarExprWith locals body
  | _ => none
termination_by source => scalarExtractionSize source
decreasing_by
  all_goals simp_wf
  all_goals try simp only [scalarExtractionSize_conversion]
  all_goals try apply Nat.lt_of_le_of_lt (scalarExtractionSize_le _)
  all_goals try simp only [scalarExtractionSize]
  all_goals simp_wf
  all_goals first
    | omega
    | (have bounds := booleanScopeBinding_sizes _scopeWord; omega)
    | (have bounds := booleanScopeBinding_sizes _scopeBoolean; omega)
    | (have bound := booleanScopeGuard_size _scope; omega)
    | (have bound := booleanScopeDependentGuard_size _scope; omega)
    | (have bounds := booleanRelationSelection_sizes _relation; omega)
    | (have bound := booleanGuardedSelection_operand_size _guarded _member; omega)
    | (have bounds := booleanGuardedSelection_branch_sizes _guarded; omega)
    | (have bounds := booleanSelected_sizes _selected; omega)
    | (have bounds := booleanRelated_sizes _related; omega)
    | (have bounds := booleanJoined_sizes _joined; omega)
    | (have bound := booleanNegated_size _negated; omega)
    | (have bound := booleanWrapped_size _wrapper; omega)
    | (have bounds := booleanHelper_sizes _wordHelper; omega)
    | (have bounds := booleanHelper_sizes _booleanHelper; omega)
    | (exact scalarManyCall_size _call _member)
    | (have bounds := scalarManyFunction_body_size _function; simp_all; omega)
    | (have bounds := booleanLocalDependentGuard_size _booleanGuard _member; omega)
    | (have bounds := dependentGuard_size _guard _member
       have overhead := scalarResultType_guard_dite (by assumption)
       omega)
    | (have same := booleanAction_sound _action
       rw [← same]
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       rw [← same]
       omega)
    | (have bounds := booleanLocalOperands_size _boolean _member; omega)
    | (have bounds := booleanLocalOperands_size (operand := input) _boolean
         (by simp [LeanExe.Source.Scalar.BooleanLocal.operands])
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bound := form.binding_size name type.expr value.expr body.expr
       have outer := LeanExe.Source.Scalar.BooleanGuardNegation.expr_size negations
         (form.expr name type.expr value.expr body.expr)
       simp only [LeanExe.Source.Scalar.BooleanLocal.expr] at same
       rw [← same] at outer
       simp at bound
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bound := form.binding_size name type.expr value body.expr
       have outer := LeanExe.Source.Scalar.BooleanGuardNegation.expr_size negations
         (form.expr name type.expr value body.expr)
       simp only [LeanExe.Source.Scalar.BooleanLocal.expr] at same
       rw [← same] at outer
       simp at bound
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := wrapper.body_size body.expr
       have outer := LeanExe.Source.Scalar.BooleanGuardNegation.expr_size negations (wrapper.expr body.expr)
       simp only [LeanExe.Source.Scalar.BooleanLocal.expr] at same
       rw [← same] at outer
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := booleanJunction_children_size negations op left right
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanEqualityForm.children_size .equality negations unequal left right
       simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanEqualityForm.children_size .decision negations unequal left right
       simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.children_size .ordinary negations unequal left right yes no
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.children_size (.dependent _shape) negations unequal left right yes no
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.proposition_children_size .ordinary negations guard yes no
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.proposition] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.proposition_operands_size .ordinary negations guard yes no _member
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.proposition] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.proposition_children_size (.dependent _shape) negations guard yes no
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.proposition] at bounds
       rw [← same] at bounds
       omega)
    | (have same := booleanLocalOperands_sound _boolean
       have bounds := LeanExe.Source.Scalar.BooleanChoiceForm.proposition_operands_size (.dependent _shape) negations guard yes no _member
       simp only [LeanExe.Source.Scalar.BooleanChoiceForm.proposition] at bounds
       rw [← same] at bounds
       omega)
    | (have bounds := booleanLocalGuard_size _booleanGuard _member; omega)
    | (have bounds := comparison_size _h; omega)
    | (have bounds := compoundGuard_size _g _member
       have overhead := scalarResultType_guard_ite (by assumption)
       omega)
    | (have bounds := booleanLocalOperands_size (value := expression) (by assumption) _member; omega)
    | (have bounds : sizeOf input.expr < sizeOf guard.condition := guard.form.inputs_size _member
       first
       | rw [← (booleanLocalGuard_sound _booleanGuard).1] at bounds
       | rw [← (booleanLocalDependentGuard_sound _booleanGuard).1] at bounds
       omega)

-- Realize the induction theorem in this module so dependent modules reuse it
-- with the definition's bounded elaboration budget.
run_elab Lean.executeReservedNameAction `LeanExe.Extract.Core.extractScalarExprWith.induct

/-- Source argument indices map to the production IR's materialized slots. -/
def extractScalarExpr (locals : List Nat) (source : Lean.Expr) : Option LeanExe.IR.Expr :=
  extractScalarExprWith (locals.map fun slot => .word (.local slot)) source

theorem extractScalarExprWith_scopeBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanScopeGuard) (type : LeanExe.Source.Scalar.ResultType)
    (yes no : Lean.Expr) :
    extractScalarExprWith locals (guard.branch type.expr yes no) = (do
      let condition ← extractScalarExprWith locals guard.operand
      let t ← extractScalarExprWith locals yes
      let e ← extractScalarExprWith locals no
      pure (.ite (wordGuard condition) t e)) := by
  rw [LeanExe.Source.Scalar.BooleanScopeGuard.branch, extractScalarExprWith]
  rw [scalarResultType_accepts, booleanScopeGuard_not_comparison,
    booleanScopeGuard_not_compound, booleanScopeGuard_not_boolean, booleanScopeGuard_accepts]

theorem extractScalarExprWith_scopeDependentBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanScopeGuard) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (ti fi : Lean.BinderInfo) (yes no : Lean.Expr) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn ti fi yes no) = (do
      let condition ← extractScalarExprWith locals guard.operand
      let t ← extractScalarExprWith (.unit :: locals) yes
      let e ← extractScalarExprWith (.unit :: locals) no
      pure (.ite (wordGuard condition) t e)) := by
  rw [LeanExe.Source.Scalar.BooleanScopeGuard.dependentBranch, extractScalarExprWith]
  rw [scalarResultType_accepts, booleanScopeGuard_not_dependent,
    booleanScopeGuard_not_booleanDependent, booleanScopeDependentGuard_accepts]

theorem extractScalarExprWith_scopedRelationSelection (locals : List ScalarBinding)
    (related : LeanExe.Source.Scalar.BooleanRelationSelection) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.expr) = (do
      let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.guard.left)
      let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.guard.right)
      let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.yes)
      let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.selection.no)
      pure (booleanWordChoice 0 related.selection.guard.unequal left right yes no)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanRelationSelection_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanRelationSelection_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · split
                · split
                  · split
                    · rename_i absent
                      rw [booleanRelationSelection_accepts] at absent
                      contradiction
                    · rename_i actual found
                      have equal := Option.some.inj ((booleanRelationSelection_accepts related).symm.trans found)
                      subst actual
                      rfl
                  · rename_i guarded found
                    rw [booleanRelationSelection_not_guarded] at found
                    contradiction
                · rename_i selected found
                  rw [booleanRelationSelection_not_selected] at found
                  contradiction
              · rename_i equality found
                rw [booleanRelationSelection_not_related] at found
                contradiction
            · rename_i joined found
              rw [booleanRelationSelection_not_joined] at found
              contradiction
          · rename_i negated found
            rw [booleanRelationSelection_not_negated] at found
            contradiction
        · rename_i wrapped found
          rw [booleanRelationSelection_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanRelationSelection_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedPropositionSelection (locals : List ScalarBinding)
    (guarded : LeanExe.Source.Scalar.BooleanGuardedSelection) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) guarded.expr) = (do
      let condition ← extractGuard guarded.selection.guard.value
        (fun operand _member => extractScalarExprWith locals operand)
      let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) guarded.selection.yes)
      let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) guarded.selection.no)
      pure (booleanWordConditional 0 condition yes no)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanGuardedSelection_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanGuardedSelection_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · split
                · split
                  · rename_i absent
                    rw [booleanGuardedSelection_accepts] at absent
                    contradiction
                  · rename_i actual found
                    have equal := Option.some.inj ((booleanGuardedSelection_accepts guarded).symm.trans found)
                    subst actual
                    rfl
                · rename_i selected found
                  rw [booleanGuardedSelection_not_selected] at found
                  contradiction
              · rename_i related found
                rw [booleanGuardedSelection_not_related] at found
                contradiction
            · rename_i joined found
              rw [booleanGuardedSelection_not_joined] at found
              contradiction
          · rename_i negated found
            rw [booleanGuardedSelection_not_negated] at found
            contradiction
        · rename_i wrapped found
          rw [booleanGuardedSelection_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanGuardedSelection_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedSelection (locals : List ScalarBinding)
    (selected : LeanExe.Source.Scalar.BooleanSelected) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.expr) = (do
      let condition ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.condition)
      let yes ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.yes)
      let no ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) selected.selection.no)
      pure (.ite (wordGuard condition) yes no)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanSelected_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanSelected_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · split
                · rename_i absent
                  rw [booleanSelected_accepts] at absent
                  contradiction
                · rename_i actual found
                  have equal := Option.some.inj ((booleanSelected_accepts selected).symm.trans found)
                  subst actual
                  rfl
              · rename_i related found
                rw [booleanSelected_not_related] at found
                contradiction
            · rename_i joined found
              rw [booleanSelected_not_joined] at found
              contradiction
          · rename_i negated found
            rw [booleanSelected_not_negated] at found
            contradiction
        · rename_i wrapped found
          rw [booleanSelected_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanSelected_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedEquality (locals : List ScalarBinding)
    (related : LeanExe.Source.Scalar.BooleanRelated) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.expr) = (do
      let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.relation.left)
      let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) related.relation.right)
      pure (booleanWordEquality 0 related.relation.unequal left right)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanRelated_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanRelated_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · rename_i absent
                rw [booleanRelated_accepts] at absent
                contradiction
              · rename_i actual found
                have equal := Option.some.inj ((booleanRelated_accepts related).symm.trans found)
                subst actual
                rfl
            · rename_i joined found
              rw [booleanRelated_not_joined] at found
              contradiction
          · rename_i negated found
            rw [booleanRelated_not_negated] at found
            contradiction
        · rename_i wrapped found
          rw [booleanRelated_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanRelated_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedJunction (locals : List ScalarBinding)
    (joined : LeanExe.Source.Scalar.BooleanJoined) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) joined.expr) = (do
      let left ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) joined.left)
      let right ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) joined.right)
      pure (booleanWordJunction 0 joined.operation left right)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanJoined_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanJoined_not_helper] at found
        contradiction
      · split
        · split
          · split
            · rename_i absent
              rw [booleanJoined_accepts] at absent
              contradiction
            · rename_i actual found
              have equal := Option.some.inj ((booleanJoined_accepts joined).symm.trans found)
              subst actual
              rfl
          · rename_i negated found
            rw [booleanJoined_not_negated] at found
            contradiction
        · rename_i wrapped found
          rw [booleanJoined_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanJoined_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedNegation (locals : List ScalarBinding)
    (negated : LeanExe.Source.Scalar.BooleanNegated) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) negated.expr) = (do
      let body ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) negated.body)
      pure (booleanWordNegation 1 body)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanNegated_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanNegated_not_helper] at found
        contradiction
      · split
        · split
          · rename_i absent
            rw [booleanNegated_accepts] at absent
            contradiction
          · rename_i actual found
            have equal := Option.some.inj ((booleanNegated_accepts negated).symm.trans found)
            subst actual
            rfl
        · rename_i wrapped found
          rw [booleanNegated_not_wrapped] at found
          contradiction
  · rename_i expression found
    rw [booleanNegated_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedWrapper (locals : List ScalarBinding)
    (wrapped : LeanExe.Source.Scalar.BooleanWrapped) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) wrapped.expr) =
      extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) wrapped.body) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i helper found
      rw [booleanWrapped_not_helper] at found
      contradiction
    · split
      · rename_i helper found
        rw [booleanWrapped_not_helper] at found
        contradiction
      · split
        · rename_i absent
          rw [booleanWrapped_accepts] at absent
          contradiction
        · rename_i actual found
          have equal := Option.some.inj ((booleanWrapped_accepts wrapped).symm.trans found)
          subst actual
          rfl
  · rename_i expression found
    rw [booleanWrapped_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedWordBinding (locals : List ScalarBinding)
    (binding : LeanExe.Source.Scalar.BooleanScopeBinding false) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) binding.expr) = (do
      let value ← extractScalarExprWith locals binding.value
      extractScalarExprWith (.word value :: locals) (.app (.const ``Bool.toUInt64 []) binding.body)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      rw [booleanScopeBinding_not_helper] at found
      contradiction
    · split
      · rename_i actual found
        rw [booleanScopeBinding_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · split
                · split
                  · split
                    · split
                      · rename_i actual found
                        have equal := Option.some.inj ((booleanScopeBinding_accepts binding).symm.trans found)
                        subst actual
                        rfl
                      · rename_i found
                        rw [booleanScopeBinding_accepts] at found
                        contradiction
                    · rename_i actual found
                      rw [booleanScopeBinding_not_relation] at found
                      contradiction
                  · rename_i actual found
                    rw [booleanScopeBinding_not_guarded] at found
                    contradiction
                · rename_i actual found
                  rw [booleanScopeBinding_not_selected] at found
                  contradiction
              · rename_i actual found
                rw [booleanScopeBinding_not_related] at found
                contradiction
            · rename_i actual found
              rw [booleanScopeBinding_not_joined] at found
              contradiction
          · rename_i actual found
            rw [booleanScopeBinding_not_negated] at found
            contradiction
        · rename_i actual found
          rw [booleanScopeBinding_not_wrapped] at found
          contradiction
  · rename_i actual found
    rw [booleanScopeBinding_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedBooleanBinding (locals : List ScalarBinding)
    (binding : LeanExe.Source.Scalar.BooleanScopeBinding true) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) binding.expr) = (do
      let value ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) binding.value)
      extractScalarExprWith (.boolean value :: locals) (.app (.const ``Bool.toUInt64 []) binding.body)) := by
  have other := booleanScopeBinding_other binding
  change booleanScopeBinding? false binding.expr = none at other
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      rw [booleanScopeBinding_not_helper] at found
      contradiction
    · split
      · rename_i actual found
        rw [booleanScopeBinding_not_helper] at found
        contradiction
      · split
        · split
          · split
            · split
              · split
                · split
                  · split
                    · split
                      · rename_i actual found
                        rw [other] at found
                        contradiction
                      · split
                        · rename_i found
                          rw [booleanScopeBinding_accepts] at found
                          contradiction
                        · rename_i actual found
                          have equal := Option.some.inj ((booleanScopeBinding_accepts binding).symm.trans found)
                          subst actual
                          rfl
                    · rename_i actual found
                      rw [booleanScopeBinding_not_relation] at found
                      contradiction
                  · rename_i actual found
                    rw [booleanScopeBinding_not_guarded] at found
                    contradiction
                · rename_i actual found
                  rw [booleanScopeBinding_not_selected] at found
                  contradiction
              · rename_i actual found
                rw [booleanScopeBinding_not_related] at found
                contradiction
            · rename_i actual found
              rw [booleanScopeBinding_not_joined] at found
              contradiction
          · rename_i actual found
            rw [booleanScopeBinding_not_negated] at found
            contradiction
        · rename_i actual found
          rw [booleanScopeBinding_not_wrapped] at found
          contradiction
  · rename_i actual found
    rw [booleanScopeBinding_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedPredicate (locals : List ScalarBinding)
    (helper : LeanExe.Source.Scalar.BooleanHelper false) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) helper.expr) = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.predicateFunction fun input =>
        extractScalarExprWith (.word input :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarExprWith (function :: locals) (.app (.const ``Bool.toUInt64 []) helper.continuation)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      have equal := Option.some.inj ((booleanHelper_accepts helper).symm.trans found)
      subst actual
      rfl
    · rename_i absent
      rw [booleanHelper_accepts] at absent
      contradiction
  · rename_i expression found
    rw [booleanHelper_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedBooleanPredicate (locals : List ScalarBinding)
    (helper : LeanExe.Source.Scalar.BooleanHelper true) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) helper.expr) = (do
      let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.booleanPredicateFunction fun input =>
        extractScalarExprWith (.boolean input :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarExprWith (function :: locals) (.app (.const ``Bool.toUInt64 []) helper.continuation)) := by
  have other := booleanHelper_other helper
  change booleanHelper? false helper.expr = none at other
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      rw [other] at found
      contradiction
    · split
      · rename_i actual found
        have equal := Option.some.inj ((booleanHelper_accepts helper).symm.trans found)
        subst actual
        rfl
      · rename_i absent
        rw [booleanHelper_accepts] at absent
        contradiction
  · rename_i expression found
    rw [booleanHelper_not_local] at found
    contradiction

theorem extractScalarExprWith_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List ScalarBinding) (a b : Lean.Expr) :
    extractScalarExprWith locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      pure (p.lower left right)) := by
  obtain ⟨op, found, _⟩ := sourceHead_recognized h
  cases h with
  | direct meaning => cases meaning <;> rw [extractScalarExprWith] <;> simp_all
  | canonical meaning result left right instanceType => cases meaning <;> dsimp only [LeanExe.Source.Scalar.classHead] <;>
      rw [extractScalarExprWith] <;> simp_all [LeanExe.Source.Scalar.classHead]

theorem extractScalarExprWith_extremum (op : LeanExe.Source.Scalar.Extremum)
    (locals : List ScalarBinding) (a b : Lean.Expr) :
    extractScalarExprWith locals (op.expr a b) = (do
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      pure (lowerExtremum op left right)) := by
  cases op <;> rw [LeanExe.Source.Scalar.Extremum.expr, LeanExe.Source.Scalar.Extremum.head,
    extractScalarExprWith]

theorem extractScalarExprWith_complement {operation : Lean.Expr}
    (head : LeanExe.Source.Scalar.ComplementHead operation) (locals : List ScalarBinding) (a : Lean.Expr) :
    extractScalarExprWith locals (.app operation a) = (do
      let argument ← extractScalarExprWith locals a
      pure (lowerComplement argument)) := by
  cases head <;> rw [extractScalarExprWith]

theorem extractScalarExprWith_branch (op : LeanExe.Source.Scalar.Comparison)
    (locals : List ScalarBinding) (a b t e : Lean.Expr) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (op.branch a b t e type) = (do
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite (lowerComparison op left right) onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.Comparison.branch, extractScalarExprWith]
  rw [scalarResultType_accepts, comparison_accepts]

theorem extractScalarExprWith_compoundBranch (guard : LeanExe.Source.Scalar.CompoundGuard)
    (locals : List ScalarBinding) (type : LeanExe.Source.Scalar.ResultType) (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.branch type.expr t e) = (do
      let c ← extractGuard guard.tree (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.CompoundGuard.branch, extractScalarExprWith]
  rw [scalarResultType_accepts, compoundGuard_not_comparison, compoundGuard_accepts]

theorem extractScalarExprWith_dependentBranch (guard : LeanExe.Source.Scalar.DecidedGuard)
    (locals : List ScalarBinding) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = (do
      let c ← extractGuard guard (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith (.unit :: locals) t
      let onFalse ← extractScalarExprWith (.unit :: locals) e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.DecidedGuard.dependentBranch, extractScalarExprWith,
    scalarResultType_accepts, dependentGuard_accepts]

theorem extractScalarExprWith_booleanBind (locals : List ScalarBinding)
    (action : LeanExe.Source.Scalar.BooleanAction) (type : LeanExe.Source.Scalar.ResultType)
    (name : Lean.Name) (bi : Lean.BinderInfo) (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.BooleanIdentity.bind name bi action.expr body type.expr) = (do
      let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) action.expr)
      extractScalarExprWith (.boolean bound :: locals) body) := by
  rw [LeanExe.Source.Scalar.BooleanIdentity.bind, extractScalarExprWith,
    booleanBindType_not_scalar, booleanBindType_accepts _ (scalarResultType_accepts type), booleanAction_accepts]

theorem extractScalarExprWith_booleanWord (locals : List ScalarBinding)
    (expression : LeanExe.Source.Scalar.BooleanLocal)
    (noBoolean : ∀ negations index input, expression = .predicate negations index input →
      (locals[index]?.bind ScalarBinding.booleanPredicateFunction?) = none)
    (noJunction : ∀ negations op left right, expression = .junction negations op left right →
      hasBooleanPredicate locals (left.functions ++ right.functions) = false)
    (noEquality : ∀ (form : LeanExe.Source.Scalar.BooleanEqualityForm) negations unequal left right,
      expression = form.local negations unequal left right →
      hasBooleanPredicate locals (left.functions ++ right.functions) = false)
    (noChoice : ∀ (form : LeanExe.Source.Scalar.BooleanChoiceForm) negations unequal left right yes no,
      expression = form.local negations unequal left right yes no →
      hasBooleanPredicate locals (left.functions ++ (right.functions ++ (yes.functions ++ no.functions))) = false)
    (noProposition : ∀ (form : LeanExe.Source.Scalar.BooleanChoiceForm) negations guard yes no,
      expression = form.proposition negations guard yes no →
      hasBooleanPredicate locals (yes.functions ++ no.functions) = false)
    (noWrapped : ∀ negations wrapper body, expression = .wrapped negations wrapper body →
      hasBooleanPredicate locals body.functions = false)
    (noBinding : ∀ negations name form value body type, expression = .binding negations name form value body type →
      hasBooleanPredicate locals (value.functions ++ LeanExe.Source.Scalar.booleanLetVariables body.functions) = false)
    (noWordBinding : ∀ negations name form value body type, expression = .wordBinding negations name form value body type →
      hasBooleanPredicate locals (LeanExe.Source.Scalar.booleanLetVariables body.functions) = false) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) expression.expr) = (do
      let condition ← extractBooleanLocalWith locals expression
        (fun operand _member => extractScalarExprWith locals operand)
      pure (guardWord condition)) := by
  rw [extractScalarExprWith]
  split
  next rejected => simp [booleanLocalOperands_expr] at rejected
  next value parsed =>
    have same := Option.some.inj (parsed.symm.trans (booleanLocalOperands_expr expression))
    subst value
    split
    next negations index input _ _ =>
      rw [noBoolean negations index input rfl]
    next negations op left right _ _ =>
      simp only [noJunction negations op left right rfl, Bool.false_eq_true, ↓reduceIte]
    next negations unequal left right _ _ =>
      simp only [noEquality .equality negations unequal left right rfl, Bool.false_eq_true, ↓reduceIte]
    next negations unequal left right _ _ =>
      simp only [noEquality .decision negations unequal left right rfl, Bool.false_eq_true, ↓reduceIte]
    next negations unequal left right yes no _ _ =>
      simp only [noChoice .ordinary negations unequal left right yes no rfl, Bool.false_eq_true, ↓reduceIte]
    next negations shape unequal left right yes no _ _ =>
      simp only [noChoice (.dependent shape) negations unequal left right yes no rfl, Bool.false_eq_true, ↓reduceIte]
    next negations guard yes no _ _ =>
      simp only [noProposition .ordinary negations guard yes no rfl, Bool.false_eq_true, ↓reduceIte]
    next negations shape guard yes no _ _ =>
      simp only [noProposition (.dependent shape) negations guard yes no rfl, Bool.false_eq_true, ↓reduceIte]
    next negations wrapper body _ _ =>
      simp only [noWrapped negations wrapper body rfl, Bool.false_eq_true, ↓reduceIte]
    next negations name form value body type _ _ =>
      simp only [noBinding negations name form value body type rfl, Bool.false_eq_true, ↓reduceIte]
    next negations name form value body type _ _ =>
      simp only [noWordBinding negations name form value body type rfl, Bool.false_eq_true, ↓reduceIte]
    next => rfl

theorem extractScalarExprWith_booleanBinding (locals : List ScalarBinding)
    (negations : Nat) (name : Lean.Name) (form : LeanExe.Source.Scalar.BooleanBindingForm)
    (value body : LeanExe.Source.Scalar.BooleanLocal) (type : LeanExe.Source.Scalar.BooleanType) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanLocal.binding negations name form value body type).expr) =
      (if hasBooleanPredicate locals (value.functions ++ LeanExe.Source.Scalar.booleanLetVariables body.functions) then do
        let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value.expr)
        let result ← extractScalarExprWith (.boolean bound :: locals) (.app (.const ``Bool.toUInt64 []) body.expr)
        pure (booleanWordNegation negations result)
      else do
        let condition ← extractBooleanLocalWith locals (.binding negations name form value body type)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr
    (LeanExe.Source.Scalar.BooleanLocal.binding negations name form value body type)
  rw [extractScalarExprWith]
  split
  next rejected => rw [rejected] at accepted; cases accepted
  next expression parsed =>
    have same := Option.some.inj (parsed.symm.trans accepted)
    subst expression
    rfl

theorem extractScalarExprWith_booleanWordBinding (locals : List ScalarBinding)
    (negations : Nat) (name : Lean.Name) (form : LeanExe.Source.Scalar.BooleanBindingForm)
    (value : Lean.Expr) (body : LeanExe.Source.Scalar.BooleanLocal) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanLocal.wordBinding negations name form value body type).expr) =
      (if hasBooleanPredicate locals (LeanExe.Source.Scalar.booleanLetVariables body.functions) then do
        let bound ← extractScalarExprWith locals value
        let result ← extractScalarExprWith (.word bound :: locals) (.app (.const ``Bool.toUInt64 []) body.expr)
        pure (booleanWordNegation negations result)
      else do
        let condition ← extractBooleanLocalWith locals (.wordBinding negations name form value body type)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr
    (LeanExe.Source.Scalar.BooleanLocal.wordBinding negations name form value body type)
  rw [extractScalarExprWith]
  split
  next rejected => rw [rejected] at accepted; cases accepted
  next expression parsed =>
    have same := Option.some.inj (parsed.symm.trans accepted)
    subst expression
    rfl

theorem extractScalarExprWith_booleanWrapped (locals : List ScalarBinding)
    (negations : Nat) (wrapper : LeanExe.Source.Scalar.BooleanWrapper)
    (body : LeanExe.Source.Scalar.BooleanLocal) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanLocal.wrapped negations wrapper body).expr) =
      (if hasBooleanPredicate locals body.functions then do
        let inner ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) body.expr)
        pure (booleanWordNegation negations inner)
      else do
        let condition ← extractBooleanLocalWith locals (.wrapped negations wrapper body)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr
    (LeanExe.Source.Scalar.BooleanLocal.wrapped negations wrapper body)
  rw [extractScalarExprWith]
  split
  next rejected => rw [rejected] at accepted; cases accepted
  next value parsed =>
    have same := Option.some.inj (parsed.symm.trans accepted)
    subst value
    rfl

theorem extractScalarExprWith_booleanJunction (locals : List ScalarBinding)
    (negations : Nat) (op : LeanExe.Source.Scalar.Junction)
    (left right : LeanExe.Source.Scalar.BooleanLocal) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanLocal.junction negations op left right).expr) =
      (if hasBooleanPredicate locals (left.functions ++ right.functions) then do
        let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
        let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
        pure (booleanWordJunction negations op first second)
      else do
        let condition ← extractBooleanLocalWith locals (.junction negations op left right)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr
    (LeanExe.Source.Scalar.BooleanLocal.junction negations op left right)
  rw [extractScalarExprWith]
  split
  next rejected => rw [rejected] at accepted; cases accepted
  next value parsed =>
    have same := Option.some.inj (parsed.symm.trans accepted)
    subst value
    rfl

theorem extractScalarExprWith_booleanEquality (locals : List ScalarBinding)
    (form : LeanExe.Source.Scalar.BooleanEqualityForm) (negations : Nat) (unequal : Bool)
    (left right : LeanExe.Source.Scalar.BooleanLocal) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (form.local negations unequal left right).expr) =
      (if hasBooleanPredicate locals (left.functions ++ right.functions) then do
        let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
        let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
        pure (booleanWordEquality negations unequal first second)
      else do
        let condition ← extractBooleanLocalWith locals (form.local negations unequal left right)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr (form.local negations unequal left right)
  cases form <;> simp only [LeanExe.Source.Scalar.BooleanEqualityForm.local] at accepted ⊢
  all_goals
    rw [extractScalarExprWith]
    split
    next rejected => rw [rejected] at accepted; cases accepted
    next value parsed =>
      have same := Option.some.inj (parsed.symm.trans accepted)
      subst value
      rfl

theorem extractScalarExprWith_booleanChoice (locals : List ScalarBinding)
    (form : LeanExe.Source.Scalar.BooleanChoiceForm) (negations : Nat) (unequal : Bool)
    (left right yes no : LeanExe.Source.Scalar.BooleanLocal) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (form.local negations unequal left right yes no).expr) =
      (if hasBooleanPredicate locals (left.functions ++ (right.functions ++ (yes.functions ++ no.functions))) then do
        let first ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) left.expr)
        let second ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) right.expr)
        let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
        let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
        pure (booleanWordChoice negations unequal first second trueBranch falseBranch)
      else do
        let condition ← extractBooleanLocalWith locals (form.local negations unequal left right yes no)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr (form.local negations unequal left right yes no)
  cases form <;> simp only [LeanExe.Source.Scalar.BooleanChoiceForm.local] at accepted ⊢
  all_goals
    rw [extractScalarExprWith]
    split
    next rejected => rw [rejected] at accepted; cases accepted
    next value parsed =>
      have same := Option.some.inj (parsed.symm.trans accepted)
      subst value
      rfl

theorem extractScalarExprWith_booleanProposition (locals : List ScalarBinding)
    (form : LeanExe.Source.Scalar.BooleanChoiceForm) (negations : Nat)
    (guard : LeanExe.Source.Scalar.PropositionGuard) (yes no : LeanExe.Source.Scalar.BooleanLocal) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (form.proposition negations guard yes no).expr) =
      (if hasBooleanPredicate locals (yes.functions ++ no.functions) then do
        let test ← extractGuard guard.value (fun operand _member => extractScalarExprWith locals operand)
        let trueBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes.expr)
        let falseBranch ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no.expr)
        pure (booleanWordConditional negations test trueBranch falseBranch)
      else do
        let condition ← extractBooleanLocalWith locals (form.proposition negations guard yes no)
          (fun operand _member => extractScalarExprWith locals operand)
        pure (guardWord condition)) := by
  have accepted := booleanLocalOperands_expr (form.proposition negations guard yes no)
  cases form <;> simp only [LeanExe.Source.Scalar.BooleanChoiceForm.proposition] at accepted ⊢
  all_goals
    rw [extractScalarExprWith]
    split
    next rejected => rw [rejected] at accepted; cases accepted
    next value parsed =>
      have same := Option.some.inj (parsed.symm.trans accepted)
      subst value
      rfl

theorem extractScalarExprWith_booleanPredicateCall (locals : List ScalarBinding)
    (negations index : Nat) (input : Lean.Expr) (function : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
    (found : (locals[index]?.bind ScalarBinding.booleanPredicateFunction?) = some function) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanGuardNegation.expr negations (.app (.bvar index) input))) = (do
        let argument ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input)
        let result ← function argument
        pure (booleanWordNegation negations result)) := by
  have accepted := booleanLocalOperands_expr
    (LeanExe.Source.Scalar.BooleanLocal.predicate negations index input)
  simp only [LeanExe.Source.Scalar.BooleanLocal.expr] at accepted
  rw [extractScalarExprWith]
  split
  next rejected => rw [rejected] at accepted; cases accepted
  next value parsed =>
    have same := Option.some.inj (parsed.symm.trans accepted)
    subst value
    simp only [found]

theorem extractScalarExprWith_applyBooleanPredicateWord (locals : List ScalarBinding)
    (negations index : Nat) (input : Lean.Expr)
    (function : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
    (found : (locals[index]?.bind ScalarBinding.booleanPredicateFunction?) = some function) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanGuardNegation.expr negations (.app (.bvar index) input))) = (do
        let argument ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input)
        let result ← function argument
        pure (booleanWordNegation negations result)) :=
  extractScalarExprWith_booleanPredicateCall _ _ _ _ _ found

theorem extractScalarExprWith_applyBooleanPredicateWordOnly (locals : List ScalarBinding)
    (negations index : Nat) (input : Lean.Expr)
    (noPredicate : (locals[index]?.bind ScalarBinding.predicateFunction?) = none) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanGuardNegation.expr negations (.app (.bvar index) input))) = (do
        let function ← locals[index]?.bind ScalarBinding.booleanPredicateFunction?
        let argument ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input)
        let result ← function argument
        pure (booleanWordNegation negations result)) := by
  cases found : locals[index]?.bind ScalarBinding.booleanPredicateFunction? with
  | some function =>
    rw [extractScalarExprWith_applyBooleanPredicateWord _ _ _ _ _ found]
    simp
  | none =>
    have noBoolean : ∀ n i argument,
        (LeanExe.Source.Scalar.BooleanLocal.predicate negations index input) = .predicate n i argument →
        (locals[i]?.bind ScalarBinding.booleanPredicateFunction?) = none := by
      intro n i argument same
      cases same
      exact found
    change extractScalarExprWith locals (.app (.const ``Bool.toUInt64 [])
      (LeanExe.Source.Scalar.BooleanLocal.predicate negations index input).expr) = _
    rw [extractScalarExprWith_booleanWord _ _ noBoolean (by intros; contradiction)
      (by intro form n unequal left right same; cases form <;> cases same)
      (by intro form n unequal left right yes no same; cases form <;> cases same)
      (by intro form n guard yes no same; cases form <;> cases same)
      (by intros; contradiction) (by intros; contradiction) (by intros; contradiction)]
    simp [extractBooleanLocalWith, extractBooleanLocal, noPredicate]

theorem extractScalarExprWith_letBoolean (locals : List ScalarBinding)
    (value : Lean.Expr) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name (.const ``Bool []) value body nondep) = (do
      let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      extractScalarExprWith (.boolean bound :: locals) body) := by
  rw [extractScalarExprWith]

theorem extractScalarExprWith_booleanPredicateBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.branch type.expr t e) = (do
      let c ← if hasBooleanPredicate locals guard.value.functions then
          extractBooleanCondition guard.form (fun input _member =>
            extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input.expr))
        else
          extractBooleanLocalWith locals guard.value
            (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.BooleanLocalGuard.branch, extractScalarExprWith,
    scalarResultType_accepts, booleanLocalGuard_not_comparison, booleanLocal_not_compound,
    booleanLocalGuard_accepts]

theorem extractScalarExprWith_booleanBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (t e : Lean.Expr)
    (noBoolean : hasBooleanPredicate locals guard.value.functions = false) :
    extractScalarExprWith locals (guard.branch type.expr t e) = (do
      let c ← extractBooleanLocalWith locals guard.value
        (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite c onTrue onFalse)) := by
  rw [extractScalarExprWith_booleanPredicateBranch, noBoolean]
  rfl

theorem extractScalarExprWith_booleanPredicateDependentBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = (do
      let c ← if hasBooleanPredicate locals guard.value.functions then
          extractBooleanCondition guard.form (fun input _member =>
            extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) input.expr))
        else
          extractBooleanLocalWith locals guard.value
            (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith (.unit :: locals) t
      let onFalse ← extractScalarExprWith (.unit :: locals) e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.BooleanLocalGuard.dependentBranch, extractScalarExprWith,
    scalarResultType_accepts, booleanLocalDependentGuard_not_closed,
    booleanLocalDependentGuard_accepts]

theorem extractScalarExprWith_booleanDependentBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr)
    (noBoolean : hasBooleanPredicate locals guard.value.functions = false) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = (do
      let c ← extractBooleanLocalWith locals guard.value
        (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith (.unit :: locals) t
      let onFalse ← extractScalarExprWith (.unit :: locals) e
      pure (.ite c onTrue onFalse)) := by
  rw [extractScalarExprWith_booleanPredicateDependentBranch, noBoolean]
  rfl

@[simp] theorem extractScalarExprWith_idRun (locals : List ScalarBinding) (body : Lean.Expr) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.run body type) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.run, extractScalarExprWith, scalarResultType_accepts]

@[simp] theorem extractScalarExprWith_idPure (locals : List ScalarBinding) (body : Lean.Expr) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.pure body type) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.pure, extractScalarExprWith, scalarResultType_accepts]

@[simp] theorem extractScalarExprWith_idBind (locals : List ScalarBinding)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) (input output : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.bind name bi value body input output) = (do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (.word bound :: locals) body) := by
  rw [LeanExe.Source.Scalar.Identity.bind, extractScalarExprWith, scalarBindTypes_accepts]

theorem extractScalarExprWith_booleanApply (locals : List ScalarBinding) (index : Nat)
    (argument : Lean.Expr) (function : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
    (found : (locals[index]?.bind ScalarBinding.booleanFunction?) = some function) :
    extractScalarExprWith locals (.app (.bvar index) argument) = (do
      let value ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) argument)
      function value) := by
  rw [extractScalarExprWith, scalarBooleanFunction_not_word found]
  simp [found]

theorem extractScalarExprWith_wordApply (locals : List ScalarBinding) (index : Nat)
    (argument : Lean.Expr) (function : LeanExe.IR.Expr → Option LeanExe.IR.Expr)
    (found : (locals[index]?.bind (ScalarBinding.function? false)) = some function) :
    extractScalarExprWith locals (.app (.bvar index) argument) = (do
      let value ← extractScalarExprWith locals argument
      function value) := by
  rw [extractScalarExprWith, found]

theorem extractScalarExprWith_wordApplyOnly (locals : List ScalarBinding) (index : Nat)
    (argument : Lean.Expr)
    (noBoolean : (locals[index]?.bind ScalarBinding.booleanFunction?) = none) :
    extractScalarExprWith locals (.app (.bvar index) argument) = (do
      let function ← locals[index]?.bind (ScalarBinding.function? false)
      let value ← extractScalarExprWith locals argument
      function value) := by
  rw [extractScalarExprWith]
  cases found : locals[index]?.bind (ScalarBinding.function? false) with
  | some function => rfl
  | none =>
    simp [noBoolean]

theorem extractScalarExprWith_letFn (locals : List ScalarBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) a
        extractScalarExprWith (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals) a) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_accepts]
  cases type <;> simp [LeanExe.Source.Scalar.ResultType.expr]

theorem extractScalarExprWith_letPredicateFn (locals : List ScalarBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.BooleanType) (expression : Lean.Expr)
    (b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) expression paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) expression)
        extractScalarExprWith (.predicateFunction (fun argument =>
          extractScalarExprWith (.word argument :: locals)
            (.app (.const ``Bool.toUInt64 []) expression)) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_boolean, booleanType_accepts]
  cases type <;> simp [LeanExe.Source.Scalar.BooleanType.expr]

theorem extractScalarExprWith_letBooleanPredicateFn (locals : List ScalarBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.BooleanType) (expression : Lean.Expr)
    (b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) expression paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) expression)
        extractScalarExprWith (.booleanPredicateFunction (fun argument =>
          extractScalarExprWith (.boolean argument :: locals)
            (.app (.const ``Bool.toUInt64 []) expression)) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_boolean, booleanType_accepts]

theorem extractScalarExprWith_predicateInput (locals : List ScalarBinding)
    (input : LeanExe.Source.Scalar.ResultType) (result : LeanExe.Source.Scalar.BooleanType)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.predicateInputExpr (.identity input) result
      name typeName paramName typeBi paramBi a b nondep) =
    extractScalarExprWith locals (LeanExe.Source.Scalar.predicateInputExpr input result
      name typeName paramName typeBi paramBi a b nondep) := by
  simp only [LeanExe.Source.Scalar.predicateInputExpr, LeanExe.Source.Scalar.ResultType.expr]
  rw [extractScalarExprWith]
  simp [scalarResultType_accepts, booleanType_accepts]

theorem extractScalarExprWith_booleanInput (locals : List ScalarBinding)
    (input : LeanExe.Source.Scalar.BooleanType) (result : Lean.Expr)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.booleanInputExpr (.identity input) result
      name typeName paramName typeBi paramBi a b nondep) =
    extractScalarExprWith locals (LeanExe.Source.Scalar.booleanInputExpr input result
      name typeName paramName typeBi paramBi a b nondep) := by
  simp only [LeanExe.Source.Scalar.booleanInputExpr, LeanExe.Source.Scalar.BooleanType.expr]
  rw [extractScalarExprWith]
  simp [scalarResultType_boolean, booleanType_accepts]

theorem extractScalarExprWith_letBooleanFn (locals : List ScalarBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) a
        extractScalarExprWith (.booleanFunction (fun argument =>
          extractScalarExprWith (.boolean argument :: locals) a) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_accepts]

theorem extractScalarExprWith_letUnitFn (locals : List ScalarBinding)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : LeanExe.Source.Scalar.UnitSyntax) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarExprWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) b) := by
  cases unitForm <;> rw [LeanExe.Source.Scalar.UnitSyntax.type, extractScalarExprWith, scalarResultType_accepts]

theorem extractScalarExprWith_unitApply (locals : List ScalarBinding)
    (unitForm : LeanExe.Source.Scalar.UnitSyntax) (index : Nat) (argument : Lean.Expr) :
    extractScalarExprWith locals (.app (.app (.bvar index) unitForm.value) argument) = (do
      let function ← locals[index]?.bind (ScalarBinding.function? true)
      let value ← extractScalarExprWith locals argument
      function value) := by
  cases unitForm <;> rw [LeanExe.Source.Scalar.UnitSyntax.value, extractScalarExprWith]

theorem extractScalarExprWith_binaryApply (locals : List ScalarBinding) (index : Nat) (a b : Lean.Expr)
    (notUnit : ∀ unitForm : LeanExe.Source.Scalar.UnitSyntax, a ≠ unitForm.value) :
    extractScalarExprWith locals (.app (.app (.bvar index) a) b) = (do
      let function ← locals[index]?.bind ScalarBinding.binaryFunction?
      let first ← extractScalarExprWith locals a
      let second ← extractScalarExprWith locals b
      function first second) := by
  rw [extractScalarExprWith]
  · exact notUnit .unit
  · exact notUnit .punit

theorem extractScalarExprWith_letBinaryFn (locals : List ScalarBinding)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarExprWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_accepts]

theorem extractScalarExprWith_naturalLiteral (locals : List ScalarBinding) (levels : List Lean.Level)
    {n : Nat} {numeral : Lean.Expr} (meaning : LeanExe.Source.Scalar.NaturalLiteral n numeral) :
    extractScalarExprWith locals (.app (.const ``UInt64.ofNat levels) numeral) = some (.u64 n) := by
  cases meaning with
  | raw => rw [extractScalarExprWith]
  | ofNat type => simp [extractScalarExprWith, naturalLiteral?, naturalType_accepts type]
  | metadata literal =>
    simp [extractScalarExprWith, naturalLiteral_accepts (.metadata literal)]

theorem extractScalarExprWith_naturalLiteralToUInt64 (locals : List ScalarBinding)
    {n : Nat} {numeral : Lean.Expr} (meaning : LeanExe.Source.Scalar.NaturalLiteral n numeral) :
    extractScalarExprWith locals (.app (.const ``Nat.toUInt64 []) numeral) = some (.u64 n) := by
  cases meaning with
  | raw => simp [extractScalarExprWith, naturalLiteral?]
  | ofNat type => simp [extractScalarExprWith, naturalLiteral?, naturalType_accepts type]
  | metadata literal => simp [extractScalarExprWith, naturalLiteral_accepts (.metadata literal)]

theorem extractScalarExprWith_idLet (locals : List ScalarBinding)
    (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.idLetExpr name type value body nondep) =
      extractScalarExprWith locals (.letE name type value body nondep) := by
  rw [LeanExe.Source.Scalar.idLetExpr, extractScalarExprWith]

theorem extractScalarExprWith_ofNatTyped (locals : List ScalarBinding)
    {n : Nat} {type : LeanExe.Source.Scalar.ResultType} {numeral evidence : Lean.Expr}
    (numberMeaning : LeanExe.Source.Scalar.NaturalLiteral n numeral)
    (instanceMeaning : LeanExe.Source.Scalar.TypedLiteralInstance n type evidence) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.typedLiteralExpr type numeral evidence) =
      some (.u64 n) := by
  rw [LeanExe.Source.Scalar.typedLiteralExpr, extractScalarExprWith,
    scalarResultType_accepts, naturalLiteral_accepts numberMeaning]
  simp [typedLiteralInstance_accepts instanceMeaning]

theorem extractScalarExprWith_ofNatNatural (locals : List ScalarBinding)
    {n : Nat} {numeral evidence : Lean.Expr}
    (numberMeaning : LeanExe.Source.Scalar.NaturalLiteral n numeral)
    (instanceMeaning : LeanExe.Source.Scalar.LiteralInstance n 0 evidence) :
    extractScalarExprWith locals (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) numeral) evidence) = some (.u64 n) := by
  exact extractScalarExprWith_ofNatTyped locals numberMeaning (.word instanceMeaning)

theorem extractScalarExprWith_ofNatInstance (locals : List ScalarBinding)
    {n : Nat} {evidence : Lean.Expr} (meaning : LeanExe.Source.Scalar.LiteralInstance n 0 evidence) :
    extractScalarExprWith locals (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n))) evidence) = some (.u64 n) :=
  extractScalarExprWith_ofNatNatural locals .raw meaning

@[simp] theorem extractScalarExprWith_literalExpr (locals : List ScalarBinding) (n : Nat) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) := by
  exact extractScalarExprWith_ofNatInstance locals .standard

theorem extractScalarExpr_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List Nat) (a b : Lean.Expr) :
    extractScalarExpr locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExpr locals a
      let right ← extractScalarExpr locals b
      pure (p.lower left right)) :=
  extractScalarExprWith_binary h _ a b

@[simp] theorem extractScalarExpr_literalExpr (locals : List Nat) (n : Nat) :
    extractScalarExpr locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) :=
  extractScalarExprWith_literalExpr _ n

/-- Existing slots contain the values of the corresponding source binders. -/
def ScalarLocalsMatch (locals : List Nat) (values : List UInt64)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index slot : Nat), locals[index]? = some slot → store[slot]? = values[index]?

/-- Range calls are statement computations and cannot enter the pure expression path. -/
theorem extractScalarExprWith_range (locals : List ScalarBinding) (count initial : Lean.Expr)
    (indexName accumulatorName : Lean.Name) (indexBi accumulatorBi : Lean.BinderInfo)
    (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Range.call count initial
      indexName accumulatorName indexBi accumulatorBi body) = none := by
  simp [LeanExe.Source.Scalar.Range.call, LeanExe.Source.Scalar.Range.head,
    Lean.mkAppN, Lean.mkApp, extractScalarExprWith, ScalarPrimitive.ofHead?, scalarManyCall?, scalarLocalCall?]

theorem extractScalarExprWith_manyApply (locals : List ScalarBinding) (call : LeanExe.Source.Scalar.ManyCall) :
    extractScalarExprWith locals call.expr = (do
      let function ← locals[call.index]?.bind (ScalarBinding.manyFunction? call.arity)
      let arguments ← extractScalarArguments call.arguments
        (fun operand _ => extractScalarExprWith locals operand)
      function arguments) := by
  unfold LeanExe.Source.Scalar.ManyCall.expr
  rw [extractScalarExprWith]
  · rw [scalarLocalCall_not_primitive, scalarManyCall_accepts]
  all_goals
    intros
    have head := call.callee.head
    have nonvar := call.callee.not_bvar call.positive
    simp_all [Lean.Expr.getAppFn]

theorem extractScalarExprWith_letManyFn (locals : List ScalarBinding)
    (shape : LeanExe.Source.Scalar.ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (shape.bind name body nondep) = (do
      let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
      extractScalarExprWith (.manyFunction shape.arity (fun arguments =>
        extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) body) := by
  rw [LeanExe.Source.Scalar.ManyFunction.bind, LeanExe.Source.Scalar.ManyFunction.type,
    LeanExe.Source.Scalar.ManyFunction.value, LeanExe.Source.Scalar.Parameter.arrow,
    LeanExe.Source.Scalar.Parameter.arrow, LeanExe.Source.Scalar.Parameter.lambda,
    LeanExe.Source.Scalar.Parameter.lambda, extractScalarExprWith,
    scalarFunctionSuffix_not_result shape.suffix shape.positive]
  have accepted := scalarManyFunction_accepts shape
  simp only [LeanExe.Source.Scalar.ManyFunction.type, LeanExe.Source.Scalar.ManyFunction.value,
    LeanExe.Source.Scalar.Parameter.arrow, LeanExe.Source.Scalar.Parameter.lambda] at accepted
  rw [accepted]

end LeanExe.Extract.Core
