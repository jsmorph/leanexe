import LeanExe.Extract.ScalarBooleanWordRange
import LeanExe.Source.ScalarWordRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Select a checked scalar or loop plan, or recursively compile word branches. -/
def extractScalarWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match extractScalarExprWith locals source with
  | some value => some (ScalarRangeExitPlan.scalar value)
  | none =>
    match extractScalarRangeExitWith locals slot source with
    | some plan => some plan
    | none =>
      match extractScalarBooleanWordRangeWith locals slot source with
      | some plan => some plan
      | none =>
        match source with
        | .letE functionName (.forallE firstTypeName (.const ``UInt64 [])
            (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
            (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) body nondep =>
            match scalarResultType? resultType with
            | none =>
                match scalarManyFunction?
                    (.forallE firstTypeName (.const ``UInt64 [])
                      (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
                    (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
                | none =>
                    match _binary : booleanBinaryHelper? (.letE functionName
                        (.forallE firstTypeName (.const ``UInt64 [])
                          (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
                        (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi)
                        body nondep) with
                    | none => none
                    | some helper => do
                        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
                          (.app (.const ``Bool.toUInt64 []) helper.body)
                        let function := ScalarBinding.binaryPredicateFunction fun first second =>
                          extractScalarExprWith (.word second :: .word first :: locals)
                            (.app (.const ``Bool.toUInt64 []) helper.body)
                        extractScalarWordRangeWith (function :: locals) slot helper.continuation
                | some shape => do
                    let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
                    let function := ScalarBinding.manyFunction shape.arity fun arguments =>
                      extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
                let function := ScalarBinding.binaryFunction fun first second =>
                  extractScalarExprWith (.word second :: .word first :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
            (.lam _ (.const ``UInt64 []) value _) body _ =>
            match scalarResultType? resultType with
            | none =>
                match booleanType? resultType with
                | none => none
                | some _ => do
                    let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
                      (.app (.const ``Bool.toUInt64 []) value)
                    let function := ScalarBinding.predicateFunction fun argument =>
                      extractScalarExprWith (.word argument :: locals)
                        (.app (.const ``Bool.toUInt64 []) value)
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
                let function := ScalarBinding.function false fun argument =>
                  extractScalarExprWith (.word argument :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
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
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE _ (.forallE _ (.const ``Bool []) resultType _)
            (.lam _ (.const ``Bool []) value _) body _ =>
            match scalarResultType? resultType with
            | none =>
                match booleanType? resultType with
                | none => none
                | some _ => do
                    let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
                      (.app (.const ``Bool.toUInt64 []) value)
                    let function := ScalarBinding.booleanPredicateFunction fun argument =>
                      extractScalarExprWith (.boolean argument :: locals)
                        (.app (.const ``Bool.toUInt64 []) value)
                    extractScalarWordRangeWith (function :: locals) slot body
            | some _ => do
                let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
                let function := ScalarBinding.booleanFunction fun argument =>
                  extractScalarExprWith (.boolean argument :: locals) value
                extractScalarWordRangeWith (function :: locals) slot body
        | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
            (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
            if input = domain then
              extractScalarWordRangeWith locals slot (.letE name
                (.forallE typeName input resultType typeBi) (.lam paramName domain value paramBi) body nondep)
            else none
        | .letE _ type value body _ =>
            match booleanType? type with
            | none =>
                match scalarResultType? type with
                | none => none
                | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
                  (fun bound => extractScalarWordRangeWith (.word bound :: locals) slot body)
                  (fun _ => extractScalarWordRangeWith locals slot value)
                  (fun bound => extractScalarExprWith (.word bound :: locals) body)
            | some _ => do
                let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
                extractScalarWordRangeWith (.boolean bound :: locals) slot body
        | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero]))) input) output) value)
            (.lam _ domain body _) =>
            match booleanWordRangeBindTypes? input domain output with
            | none =>
                match scalarBindTypes? input domain output with
                | none => none
                | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
                  (fun bound => extractScalarWordRangeWith (.word bound :: locals) slot body)
                  (fun _ => extractScalarWordRangeWith locals slot value)
                  (fun bound => extractScalarExprWith (.word bound :: locals) body)
            | some _ => do
                let bound ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
                extractScalarWordRangeWith (.boolean bound :: locals) slot body
        | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no =>
            match scalarResultType? type with
            | none => none
            | some _ => do
                let guard ← extractScalarExprWith locals (BooleanRange.decision condition evidence)
                let first ← extractScalarWordRangeWith locals slot yes
                let second ← extractScalarWordRangeWith locals slot no
                pure (ScalarRangeExitPlan.choice guard first second)
        | .app (.app (.const ``Id.run [.zero]) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
              (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
                (.const ``Id.instMonad [.zero])))) type) body =>
            match scalarResultType? type with
            | none => none
            | some _ => extractScalarWordRangeWith locals slot body
        | .mdata _ body => extractScalarWordRangeWith locals slot body
        | _ => none
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have bounds := booleanBinaryHelper_sizes _binary
      simp at bounds
      omega

theorem extractScalarWordRangeWith_letBinaryPredicate (locals : List ScalarBinding) (slot : Nat)
    (helper : BooleanBinaryHelper)
    (noScalar : extractScalarExprWith locals helper.expr = none)
    (noRange : extractScalarRangeExitWith locals slot helper.expr = none)
    (noBooleanWord : extractScalarBooleanWordRangeWith locals slot helper.expr = none) :
    extractScalarWordRangeWith locals slot helper.expr = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.binaryPredicateFunction fun first second =>
        extractScalarExprWith (.word second :: .word first :: locals)
          (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarWordRangeWith (function :: locals) slot helper.continuation) := by
  rw [extractScalarWordRangeWith.eq_def, noScalar, noRange, noBooleanWord]
  have noMany := booleanBinaryHelper_not_many helper
  simp only [Parameter.arrow, Parameter.lambda] at noMany
  simp only [BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.lambda]
  rw [scalarResultType_boolean, noMany]
  change (match found : booleanBinaryHelper? helper.expr with
    | none => none
    | some value => do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) value.body)
        let function := ScalarBinding.binaryPredicateFunction fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals)
            (.app (.const ``Bool.toUInt64 []) value.body)
        extractScalarWordRangeWith (function :: locals) slot value.continuation) = _
  split
  · rename_i found
    rw [booleanBinaryHelper_accepts] at found
    contradiction
  · rename_i actual found
    have equal := Option.some.inj ((booleanBinaryHelper_accepts helper).symm.trans found)
    subst actual
    rfl


end LeanExe.Extract.Core
set_option pp.maxSteps 100000 in
#check LeanExe.Extract.Core.extractScalarWordRangeWith.induct
