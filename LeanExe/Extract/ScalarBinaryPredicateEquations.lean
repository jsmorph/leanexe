import LeanExe.Extract.ScalarExprCore

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

theorem extractScalarExprWith_applyBinaryPredicate (locals : List ScalarBinding)
    (call : BooleanBinaryCall) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) call.expr) = (do
      let function ← locals[call.index]?.bind ScalarBinding.binaryPredicateFunction?
      let first ← extractScalarExprWith locals call.first
      let second ← extractScalarExprWith locals call.second
      function first second) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      rw [booleanBinaryCall_not_helper] at found
      contradiction
    · split
      · rename_i actual found
        rw [booleanBinaryCall_not_helper] at found
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
                        rw [booleanBinaryCall_not_binding] at found
                        contradiction
                      · split
                        · split
                          · rename_i actual found
                            have equal := Option.some.inj ((booleanBinaryCall_accepts call).symm.trans found)
                            subst actual
                            rfl
                          · rename_i found
                            rw [booleanBinaryCall_accepts] at found
                            contradiction
                        · rename_i actual found
                          rw [booleanBinaryCall_not_binding] at found
                          contradiction
                    · rename_i actual found
                      rw [booleanBinaryCall_not_relation] at found
                      contradiction
                  · rename_i actual found
                    rw [booleanBinaryCall_not_guarded] at found
                    contradiction
                · rename_i actual found
                  rw [booleanBinaryCall_not_selected] at found
                  contradiction
              · rename_i actual found
                rw [booleanBinaryCall_not_related] at found
                contradiction
            · rename_i actual found
              rw [booleanBinaryCall_not_joined] at found
              contradiction
          · rename_i actual found
            rw [booleanBinaryCall_not_negated] at found
            contradiction
        · rename_i actual found
          rw [booleanBinaryCall_not_wrapped] at found
          contradiction
  · rename_i actual found
    rw [booleanBinaryCall_not_local] at found
    contradiction

theorem extractScalarExprWith_scopedBinaryPredicate (locals : List ScalarBinding)
    (helper : BooleanBinaryHelper) :
    extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) helper.expr) = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.binaryPredicateFunction fun first second =>
        extractScalarExprWith (.word second :: .word first :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarExprWith (function :: locals) (.app (.const ``Bool.toUInt64 []) helper.continuation)) := by
  rw [extractScalarExprWith]
  split
  · split
    · rename_i actual found
      rw [booleanBinaryHelper_not_helper] at found
      contradiction
    · split
      · rename_i actual found
        rw [booleanBinaryHelper_not_helper] at found
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
                        rw [booleanBinaryHelper_not_binding] at found
                        contradiction
                      · split
                        · split
                          · rename_i actual found
                            rw [booleanBinaryHelper_not_call] at found
                            contradiction
                          · split
                            · rename_i found
                              rw [booleanBinaryHelper_accepts] at found
                              contradiction
                            · rename_i actual found
                              have equal := Option.some.inj ((booleanBinaryHelper_accepts helper).symm.trans found)
                              subst actual
                              rfl
                        · rename_i actual found
                          rw [booleanBinaryHelper_not_binding] at found
                          contradiction
                    · rename_i actual found
                      rw [booleanBinaryHelper_not_relation] at found
                      contradiction
                  · rename_i actual found
                    rw [booleanBinaryHelper_not_guarded] at found
                    contradiction
                · rename_i actual found
                  rw [booleanBinaryHelper_not_selected] at found
                  contradiction
              · rename_i actual found
                rw [booleanBinaryHelper_not_related] at found
                contradiction
            · rename_i actual found
              rw [booleanBinaryHelper_not_joined] at found
              contradiction
          · rename_i actual found
            rw [booleanBinaryHelper_not_negated] at found
            contradiction
        · rename_i actual found
          rw [booleanBinaryHelper_not_wrapped] at found
          contradiction
  · rename_i actual found
    rw [booleanBinaryHelper_not_local] at found
    contradiction

theorem booleanBinaryHelper_not_many (helper : BooleanBinaryHelper) :
    scalarManyFunction? (helper.shape.first.arrow (helper.shape.second.arrow helper.shape.result.expr))
      (helper.shape.first.lambda (helper.shape.second.lambda helper.body)) = none := by
  cases result : helper.shape.result <;>
    simp [scalarManyFunction?, manyFunction?, Parameter.arrow, Parameter.lambda,
      functionSuffix?, BooleanType.expr, FunctionSuffix.arity]

theorem extractScalarExprWith_letBinaryPredicate (locals : List ScalarBinding)
    (helper : BooleanBinaryHelper) :
    extractScalarExprWith locals helper.expr = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.binaryPredicateFunction fun first second =>
        extractScalarExprWith (.word second :: .word first :: locals) (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarExprWith (function :: locals) helper.continuation) := by
  have absent := booleanBinaryHelper_not_many helper
  simp only [Parameter.arrow, Parameter.lambda] at absent
  rw [BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.arrow,
    Parameter.lambda, Parameter.lambda, extractScalarExprWith, scalarResultType_boolean, absent]
  change (match found : booleanBinaryHelper? helper.expr with
    | none => none
    | some value => do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) value.body)
        let function := ScalarBinding.binaryPredicateFunction fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) (.app (.const ``Bool.toUInt64 []) value.body)
        extractScalarExprWith (function :: locals) value.continuation) = _
  split
  · rename_i found
    rw [booleanBinaryHelper_accepts] at found
    contradiction
  · rename_i actual found
    have equal := Option.some.inj ((booleanBinaryHelper_accepts helper).symm.trans found)
    subst actual
    rfl

end LeanExe.Extract.Core
