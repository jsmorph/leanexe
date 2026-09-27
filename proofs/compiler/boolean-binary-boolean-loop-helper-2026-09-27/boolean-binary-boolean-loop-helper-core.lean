import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarRangeBinding
import LeanExe.Extract.ScalarBooleanRangeContinuation
import LeanExe.Extract.ScalarBooleanFunctionChoice
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanRange
import LeanExe.Extract.ScalarBooleanAccumulator

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A scalar arm uses the same plan interface with zero loop iterations. -/
def ScalarRangeExitPlan.scalar (value : LeanExe.IR.Expr) : ScalarRangeExitPlan :=
  { count := .u64 0, initial := .u64 0, step := .u64 0, done := .u64 0, result := value }

/-- Try a scalar result before extracting a loop; the fallback is evaluated only when needed. -/
def scalarBooleanRangeArm (scalar : Option LeanExe.IR.Expr)
    (range : Unit → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan :=
  match scalar with
  | some value => some (ScalarRangeExitPlan.scalar value)
  | none => range ()

theorem scalarBooleanRangeArm_accepts {scalar : Option LeanExe.IR.Expr}
    {range : Unit → Option ScalarRangeExitPlan}
    (available : (∃ value, scalar = some value) ∨ (∃ plan, range () = some plan)) :
    ∃ plan, scalarBooleanRangeArm scalar range = some plan := by
  cases found : scalar with
  | some value => exact ⟨ScalarRangeExitPlan.scalar value, by simp [scalarBooleanRangeArm]⟩
  | none =>
    rcases available with ⟨value, matched⟩ | ⟨plan, matched⟩
    · simp [found] at matched
    · exact ⟨plan, by simp [scalarBooleanRangeArm, matched]⟩

theorem scalarBooleanRangeArm_success {scalar : Option LeanExe.IR.Expr}
    {range : Unit → Option ScalarRangeExitPlan} {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeArm scalar range = some plan) :
    (∃ value, scalar = some value ∧ plan = ScalarRangeExitPlan.scalar value) ∨
      (scalar = none ∧ range () = some plan) := by
  cases found : scalar with
  | none => exact .inr ⟨rfl, by simpa [scalarBooleanRangeArm, found] using compiled⟩
  | some value =>
    exact .inl ⟨value, rfl, (Option.some.inj (by simpa [scalarBooleanRangeArm, found] using compiled)).symm⟩

/-- The condition is captured outside either loop and selects every plan field. -/
def ScalarRangeExitPlan.choice (guard : LeanExe.IR.Expr) (yes no : ScalarRangeExitPlan) : ScalarRangeExitPlan :=
  let condition := lowerComparison .bne guard (.u64 0)
  { count := .ite condition yes.count no.count
    initial := .ite condition yes.initial no.initial
    step := .ite condition yes.step no.step
    done := .ite condition yes.done no.done
    result := .ite condition yes.result no.result }

/-- Try existing helper/call extraction before choosing between helper bodies. -/
def scalarBooleanRangeCompleteContinuation (locals : List ScalarBinding) (boolean : Bool)
    (value tail : Lean.Expr) (enclosing direct : ScalarBinding → Option ScalarRangeExitPlan)
    (branch : (arm : Lean.Expr) → sizeOf arm < sizeOf tail → Option ScalarRangeExitPlan) :
    Option ScalarRangeExitPlan :=
  (scalarBooleanRangeContinuation locals boolean value tail enclosing direct).orElse fun _ =>
    match parsed : booleanFunctionChoice? tail with
    | none => none
    | some choice => do
        let guard ← extractScalarExprWith locals (BooleanRange.decision choice.condition choice.evidence)
        let first ← branch choice.yes (booleanFunctionChoice_sizes parsed).1
        let second ← branch choice.no (booleanFunctionChoice_sizes parsed).2
        pure (ScalarRangeExitPlan.choice guard first second)

theorem scalarBooleanRangeCompleteContinuation_accepts_old {locals : List ScalarBinding} {boolean : Bool}
    {value tail : Lean.Expr} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {branch : (arm : Lean.Expr) → sizeOf arm < sizeOf tail → Option ScalarRangeExitPlan}
    {plan : ScalarRangeExitPlan}
    (accepted : scalarBooleanRangeContinuation locals boolean value tail enclosing direct = some plan) :
    scalarBooleanRangeCompleteContinuation locals boolean value tail enclosing direct branch = some plan := by
  simp [scalarBooleanRangeCompleteContinuation, accepted]

theorem scalarBooleanRangeCompleteContinuation_accepts_choice {locals : List ScalarBinding} {boolean : Bool}
    {value : Lean.Expr} {choice : BooleanFunctionChoice}
    {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {branch : (arm : Lean.Expr) → sizeOf arm < sizeOf choice.expr → Option ScalarRangeExitPlan}
    {guard : LeanExe.IR.Expr}
    (condition : extractScalarExprWith locals (BooleanRange.decision choice.condition choice.evidence) = some guard)
    (yes : ∀ smaller, ∃ plan, branch choice.yes smaller = some plan)
    (no : ∀ smaller, ∃ plan, branch choice.no smaller = some plan) :
    ∃ plan, scalarBooleanRangeCompleteContinuation locals boolean value choice.expr enclosing direct branch = some plan := by
  cases old : scalarBooleanRangeContinuation locals boolean value choice.expr enclosing direct with
  | some plan => exact ⟨plan, scalarBooleanRangeCompleteContinuation_accepts_old old⟩
  | none =>
    obtain ⟨first, ht⟩ := yes choice.arm_sizes.1
    obtain ⟨second, he⟩ := no choice.arm_sizes.2
    refine ⟨ScalarRangeExitPlan.choice guard first second, ?_⟩
    have parsed := booleanFunctionChoice_accepts choice
    simp only [scalarBooleanRangeCompleteContinuation, old, Option.orElse]
    split <;> simp_all

theorem scalarBooleanRangeCompleteContinuation_success {locals : List ScalarBinding} {boolean : Bool}
    {value tail : Lean.Expr} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {branch : (arm : Lean.Expr) → sizeOf arm < sizeOf tail → Option ScalarRangeExitPlan}
    {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeCompleteContinuation locals boolean value tail enclosing direct branch = some plan) :
    scalarBooleanRangeContinuation locals boolean value tail enclosing direct = some plan ∨
    (∃ (choice : BooleanFunctionChoice) (parsed : booleanFunctionChoice? tail = some choice)
      (guard : LeanExe.IR.Expr) (first second : ScalarRangeExitPlan),
      extractScalarExprWith locals (BooleanRange.decision choice.condition choice.evidence) = some guard ∧
      branch choice.yes (booleanFunctionChoice_sizes parsed).1 = some first ∧
      branch choice.no (booleanFunctionChoice_sizes parsed).2 = some second ∧
      plan = ScalarRangeExitPlan.choice guard first second) := by
  unfold scalarBooleanRangeCompleteContinuation at compiled
  cases old : scalarBooleanRangeContinuation locals boolean value tail enclosing direct with
  | some target =>
    have same : target = plan := by simpa [old] using compiled
    subst target
    exact .inl rfl
  | none =>
    simp only [old, Option.orElse] at compiled
    split at compiled
    · contradiction
    · rename_i choice parsed
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨guard, hg, first, ht, second, he, same⟩ := compiled
      exact .inr ⟨choice, parsed, guard, first, second, hg, ht, he, same.symm⟩

/-- Compose checked scalar Boolean results, local helpers and bounded word loops. -/
def extractScalarBooleanRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source) with
  | some value => some (ScalarRangeExitPlan.scalar value)
  | none =>
      match source with
      | .letE _ (.const ``UInt64 []) value body _ =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeExitWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
              pure { plan with result }
      | .letE _ (.const ``Bool []) value body _ =>
          scalarRangeValueBinding
            (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
            (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
            (fun _ => extractScalarBooleanRangeWith locals slot value)
            (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body))
      | .letE name (.app (.const ``Id [.zero]) type) value body nondep =>
          extractScalarBooleanRangeWith locals slot (.letE name type value body nondep)
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
                      extractScalarBooleanRangeWith (function :: locals) slot helper.continuation
              | some shape =>
                  match extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body with
                  | none => none
                  | some _ => extractScalarBooleanRangeWith
                      (.manyFunction shape.arity (fun arguments => extractScalarExprWith
                        (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) slot body
          | some _ =>
              match extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value with
              | none => none
              | some _ => extractScalarBooleanRangeWith
                  (.binaryFunction (fun first second => extractScalarExprWith
                    (.word second :: .word first :: locals) value) :: locals) slot body
      | .letE name (.forallE typeName (.const ``UInt64 []) resultType typeBi) (.lam paramName (.const ``UInt64 []) value paramBi) body nondep =>
          match scalarResultType? resultType with
          | none =>
              match booleanType? resultType with
              | none => none
              | some _ =>
                  scalarBooleanRangeCompleteContinuation locals false value body
                    (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
                    (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
                    (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
                      (.forallE typeName (.const ``UInt64 []) resultType typeBi)
                      (.lam paramName (.const ``UInt64 []) value paramBi) arm nondep))
          | some _ =>
              match extractScalarExprWith (.word (.u64 0) :: locals) value with
              | none => none
              | some _ => extractScalarBooleanRangeWith
                  (.function false (fun argument => extractScalarExprWith (.word argument :: locals) value) :: locals) slot body
      | .letE name (.forallE typeName (.const ``Bool []) resultType typeBi) (.lam paramName (.const ``Bool []) value paramBi) body nondep =>
          match scalarResultType? resultType with
          | none =>
              match booleanType? resultType with
              | none => none
              | some _ =>
                  scalarBooleanRangeCompleteContinuation locals true value body
                    (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
                    (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
                    (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
                      (.forallE typeName (.const ``Bool []) resultType typeBi)
                      (.lam paramName (.const ``Bool []) value paramBi) arm nondep))
          | some _ =>
              match extractScalarExprWith (.boolean (.u64 0) :: locals) value with
              | none => none
              | some _ => extractScalarBooleanRangeWith
                  (.booleanFunction (fun argument => extractScalarExprWith (.boolean argument :: locals) value) :: locals) slot body
      | .letE _ (.forallE _ (.const ``Unit [])
          (.forallE _ (.const ``UInt64 []) resultType _) _)
          (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _
      | .letE _ (.forallE _ (.const ``PUnit [.succ .zero])
          (.forallE _ (.const ``UInt64 []) resultType _) _)
          (.lam _ (.const ``PUnit [.succ .zero]) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
          match scalarResultType? resultType with
          | none => none
          | some _ =>
              match extractScalarExprWith (.word (.u64 0) :: .unit :: locals) value with
              | none => none
              | some _ => extractScalarBooleanRangeWith
                  (.function true (fun argument => extractScalarExprWith (.word argument :: .unit :: locals) value) :: locals) slot body
      | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
          (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
          if input = domain then
            extractScalarBooleanRangeWith locals slot (.letE name
              (.forallE typeName input resultType typeBi) (.lam paramName domain value paramBi) body nondep)
          else none
      | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero]))) input) output) value)
          (.lam _ domain body _) =>
          match booleanRangeBindTypes? input domain output with
          | none =>
              match booleanRangeFlagBindTypes? input domain output with
              | none => none
              | some _ =>
                  scalarRangeValueBinding
                    (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
                    (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
                    (fun _ => extractScalarBooleanRangeWith locals slot value)
                    (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body))
          | some _ =>
              match extractScalarExprWith locals value with
              | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
              | none => do
                  let plan ← extractScalarRangeExitWith locals slot value
                  let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
                  pure { plan with result }
      | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no =>
          match booleanType? type with
          | none => none
          | some _ =>
              match extractScalarExprWith locals (BooleanRange.decision condition evidence) with
              | none => none
              | some guard => do
                  let first ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
                    (fun _ => extractScalarBooleanRangeWith locals slot yes)
                  let second ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
                    (fun _ => extractScalarBooleanRangeWith locals slot no)
                  pure (ScalarRangeExitPlan.choice guard first second)
      | source =>
          match _wrapped : booleanRangeWrapper? source with
          | some (_, body) => extractScalarBooleanRangeWith locals slot body
          | none => extractScalarBooleanAccumulatorWith locals slot source
termination_by sizeOf source
decreasing_by
  all_goals first
    | (simp_wf; omega)
    | exact booleanRangeWrapper_size _wrapped
    | have bounds := booleanBinaryHelper_sizes _binary
      simp_wf
      simp at bounds
      omega

theorem extractScalarBooleanRangeWith_letBinaryPredicate (locals : List ScalarBinding) (slot : Nat)
    (helper : BooleanBinaryHelper)
    (noScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) helper.expr) = none) :
    extractScalarBooleanRangeWith locals slot helper.expr = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.binaryPredicateFunction fun first second =>
        extractScalarExprWith (.word second :: .word first :: locals)
          (.app (.const ``Bool.toUInt64 []) helper.body)
      extractScalarBooleanRangeWith (function :: locals) slot helper.continuation) := by
  rw [extractScalarBooleanRangeWith.eq_def, noScalar]
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
        extractScalarBooleanRangeWith (function :: locals) slot value.continuation) = _
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
#check LeanExe.Extract.Core.extractScalarBooleanRangeWith.induct
