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

theorem extractScalarBooleanRangeWith_scalar {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {value : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source) = some value) :
    extractScalarBooleanRangeWith locals slot source = some (ScalarRangeExitPlan.scalar value) := by
  rw [extractScalarBooleanRangeWith.eq_def, compiled]

theorem extractScalarBooleanRangeWith_accumulator {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarRangeExitPlan}
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source) = none)
    (compiled : extractScalarBooleanAccumulatorWith locals slot source = some plan) :
    extractScalarBooleanRangeWith locals slot source = some plan := by
  have checked := compiled
  simp only [extractScalarBooleanAccumulatorWith, bind, Option.bind_eq_some_iff] at checked
  obtain ⟨view, parsed, _⟩ := checked
  rw [scalarBooleanAccumulator_sound parsed] at notScalar compiled ⊢
  have notWrapped : booleanRangeWrapper? view.source = none := by rfl
  rw [extractScalarBooleanRangeWith, notScalar]
  rw [notWrapped]
  exact compiled
  all_goals simp [ScalarBooleanAccumulatorView.source, BooleanAccumulator.call,
    BooleanAccumulator.head, Lean.mkAppN, Lean.mkApp]

theorem extractScalarBooleanRangeWith_accepts_fallback {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr}
    (fallback : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source) = none →
      ∃ plan, extractScalarBooleanRangeWith locals slot source = some plan) :
    ∃ plan, extractScalarBooleanRangeWith locals slot source = some plan := by
  cases found : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source) with
  | some value => exact ⟨_, extractScalarBooleanRangeWith_scalar found⟩
  | none => exact fallback found

@[simp] theorem extractScalarBooleanRangeWith_let (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name (.const ``UInt64 []) value body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  rw [extractScalarBooleanRangeWith, notScalar]

@[simp] theorem extractScalarBooleanRangeWith_bind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input : ResultType) (output : BooleanType)
    (value body : Lean.Expr)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (BooleanRange.bind name binder input output value body)) = none) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bind name binder input output value body) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  simp only [BooleanRange.bind, BooleanBindingForm.expr] at notScalar
  rw [BooleanRange.bind, BooleanBindingForm.expr, extractScalarBooleanRangeWith, notScalar, booleanRangeBindTypes_accepts]

@[simp] theorem extractScalarBooleanRangeWith_letFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name (.const ``Bool []) value body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``Bool []) value body nondep) = scalarRangeValueBinding
        (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body)) := by
  rw [extractScalarBooleanRangeWith, notScalar]

@[simp] theorem extractScalarBooleanRangeWith_bindFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input output : BooleanType) (value body : Lean.Expr)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (BooleanRange.bindBoolean name binder input output value body)) = none) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bindBoolean name binder input output value body) = scalarRangeValueBinding
        (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body)) := by
  simp only [BooleanRange.bindBoolean, BooleanBindingForm.expr] at notScalar
  rw [BooleanRange.bindBoolean, BooleanBindingForm.expr, extractScalarBooleanRangeWith, notScalar,
    booleanRangeBindTypes_not_boolean, booleanRangeFlagBindTypes_accepts]

@[simp] theorem extractScalarBooleanRangeWith_idLet (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name (.app (.const ``Id [.zero]) type) value body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name (.app (.const ``Id [.zero]) type) value body nondep) =
      extractScalarBooleanRangeWith locals slot (.letE name type value body nondep) := by
  rw [extractScalarBooleanRangeWith, notScalar]

@[simp] theorem extractScalarBooleanRangeWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.function false (fun argument => extractScalarExprWith (.word argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, notScalar, scalarResultType_accepts]
  · cases extractScalarExprWith (.word (.u64 0) :: locals) value <;> rfl
  · cases type <;> simp [ResultType.expr]

@[simp] theorem extractScalarBooleanRangeWith_letBooleanFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.booleanFunction (fun argument => extractScalarExprWith (.boolean argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, notScalar, scalarResultType_accepts]
  cases extractScalarExprWith (.boolean (.u64 0) :: locals) value <;> rfl

theorem extractScalarBooleanRangeWith_letPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : BooleanType) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep) =
      scalarBooleanRangeCompleteContinuation locals false value body
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
        (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
          (.lam paramName (.const ``UInt64 []) value paramBi) arm nondep)) := by
  rw [extractScalarBooleanRangeWith, notScalar, scalarResultType_boolean, booleanType_accepts]
  · cases type <;> simp [BooleanType.expr]

theorem extractScalarBooleanRangeWith_letBooleanPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : BooleanType) (value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep) =
      scalarBooleanRangeCompleteContinuation locals true value body
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
        (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
          (.forallE typeName (.const ``Bool []) type.expr typeBi)
          (.lam paramName (.const ``Bool []) value paramBi) arm nondep)) := by
  rw [extractScalarBooleanRangeWith, notScalar, scalarResultType_boolean, booleanType_accepts]

@[simp] theorem extractScalarBooleanRangeWith_idFunctionInput (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (input result value body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) body nondep) =
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName input result typeBi) (.lam paramName input value paramBi) body nondep) := by
  rw [extractScalarBooleanRangeWith, notScalar]
  simp only [ite_true]

theorem extractScalarBooleanRangeWith_letBinaryFn (locals : List ScalarBinding) (slot : Nat)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarBooleanRangeWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) slot b) := by
  rw [extractScalarBooleanRangeWith, notScalar, scalarResultType_accepts]
  simp only []
  cases extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a <;> rfl

theorem extractScalarBooleanRangeWith_letManyFn (locals : List ScalarBinding) (slot : Nat)
    (shape : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (shape.bind name body nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (shape.bind name body nondep) = (do
      let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
      extractScalarBooleanRangeWith (.manyFunction shape.arity (fun arguments =>
        extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) slot body) := by
  simp only [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at notScalar
  rw [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow,
    Parameter.arrow, Parameter.lambda, Parameter.lambda, extractScalarBooleanRangeWith, notScalar,
    scalarFunctionSuffix_not_result shape.suffix shape.positive]
  have accepted := scalarManyFunction_accepts shape
  simp only [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at accepted
  rw [accepted]
  simp only []
  cases extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body <;> rfl

theorem extractScalarBooleanRangeWith_letUnitFn (locals : List ScalarBinding) (slot : Nat)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : UnitSyntax) (a b : Lean.Expr) (nondep : Bool)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)) = none) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarBooleanRangeWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) slot b) := by
  cases unitForm <;> rw [UnitSyntax.type, extractScalarBooleanRangeWith, notScalar, scalarResultType_accepts]
  all_goals cases extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_choice (locals : List ScalarBinding) (slot : Nat)
    (type : BooleanType) (condition evidence yes no : Lean.Expr)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (BooleanRange.choiceExpr type condition evidence yes no)) = none) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.choiceExpr type condition evidence yes no) = (do
      let guard ← extractScalarExprWith locals (BooleanRange.decision condition evidence)
      let first ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
        (fun _ => extractScalarBooleanRangeWith locals slot yes)
      let second ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
        (fun _ => extractScalarBooleanRangeWith locals slot no)
      pure (ScalarRangeExitPlan.choice guard first second)) := by
  simp only [BooleanRange.choiceExpr] at notScalar
  rw [BooleanRange.choiceExpr, extractScalarBooleanRangeWith, notScalar, booleanType_accepts]
  cases extractScalarExprWith locals (BooleanRange.decision condition evidence) <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_wrapped (locals : List ScalarBinding) (slot : Nat)
    (wrapper : BooleanWrapper) (body : Lean.Expr)
    (notScalar : extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) (wrapper.expr body)) = none) :
    extractScalarBooleanRangeWith locals slot (wrapper.expr body) =
      extractScalarBooleanRangeWith locals slot body := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed notScalar ⊢
  all_goals rw [extractScalarBooleanRangeWith.eq_def]
  all_goals simp only [notScalar]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem extractScalarBooleanRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
  | scalar body =>
    obtain ⟨value, compiled⟩ := extractScalarExprWith_accepts body locals typed total
    exact ⟨_, extractScalarBooleanRangeWith_scalar compiled⟩
  | accumulator body =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨plan, compiled⟩ := extractScalarBooleanAccumulatorWith_accepts body locals slot typed total
    exact ⟨plan, extractScalarBooleanRangeWith_accumulator notScalar compiled⟩
  | wordFunctionChoice shape choice condition _ _ yesIH noIH =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition locals typed total
    rw [BooleanFunctionBinding.bodyExpr, extractScalarBooleanRangeWith_letPredicateFn (notScalar := notScalar)]
    apply scalarBooleanRangeCompleteContinuation_accepts_choice matched
    · intro smaller
      exact yesIH locals typed total
    · intro smaller
      exact noIH locals typed total
  | booleanFunctionChoice shape choice condition _ _ yesIH noIH =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition locals typed total
    rw [BooleanFunctionBinding.bodyExpr, extractScalarBooleanRangeWith_letBooleanPredicateFn (notScalar := notScalar)]
    apply scalarBooleanRangeCompleteContinuation_accepts_choice matched
    · intro smaller
      exact yesIH locals typed total
    · intro smaller
      exact noIH locals typed total
  | @applyWord types a b parameterName shape call argument _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, matched⟩ := extractScalarExprWith_accepts argument locals typed total
    have emitted := ih (.word bound :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [BooleanFunctionBinding.callExpr, extractScalarBooleanRangeWith_letPredicateFn (notScalar := notScalar)]
    obtain ⟨plan, accepted⟩ := scalarBooleanRangeContinuation_accepts_direct
      (locals := locals) (boolean := false) (value := b) (call := call)
      (enclosing := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot (call.expr a))
      (direct := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot b) matched emitted
    exact ⟨plan, scalarBooleanRangeCompleteContinuation_accepts_old accepted⟩
  | @applyBoolean types a b parameterName shape call argument _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, matched⟩ := extractScalarExprWith_accepts argument locals typed total
    have emitted := ih (.boolean bound :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [BooleanFunctionBinding.callExpr, extractScalarBooleanRangeWith_letBooleanPredicateFn (notScalar := notScalar)]
    obtain ⟨plan, accepted⟩ := scalarBooleanRangeContinuation_accepts_direct
      (locals := locals) (boolean := true) (value := b) (call := call)
      (enclosing := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot (call.expr a))
      (direct := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot b) matched emitted
    exact ⟨plan, scalarBooleanRangeCompleteContinuation_accepts_old accepted⟩
  | @choice types test evidence yes no type condition _ _ yesIH noIH =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inr (yesIH locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inr (noIH locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice (notScalar := notScalar), hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalarLeft types test evidence yes no type condition first _ noIH =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inl (extractScalarExprWith_accepts first locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inr (noIH locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice (notScalar := notScalar), hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalarRight types test evidence yes no type condition _ second yesIH =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inr (yesIH locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inl (extractScalarExprWith_accepts second locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice (notScalar := notScalar), hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalars types test evidence yes no type condition first second =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inl (extractScalarExprWith_accepts first locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inl (extractScalarExprWith_accepts second locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice (notScalar := notScalar), hg, bind, Option.bind_some, ht, he, pure]⟩
  | letBinaryPredicate helper function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (first second : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word second :: .word first :: locals) (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0) (.u64 0)
    let f := fun first second => extractScalarExprWith (.word second :: .word first :: locals)
      (.app (.const ``Bool.toUInt64 []) helper.body)
    obtain ⟨target, ht⟩ := ihb (.binaryPredicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBinaryPredicate locals slot helper notScalar]; simp [hc, ht, f]⟩
  | @letBinaryFn types a b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (first second : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word second :: .word first :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0) (.u64 0)
    let f := fun first second => extractScalarExprWith (.word second :: .word first :: locals) a
    obtain ⟨target, ht⟩ := ihb (.binaryFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBinaryFn (notScalar := notScalar)]; simp [hc, ht, f]⟩
  | letManyFn shape function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (arguments : List LeanExe.IR.Expr) (len : arguments.length = shape.arity) :=
      extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
        (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len, typed])
        (scalarWords_total _ total)
    obtain ⟨checked, hc⟩ := accepts (List.replicate shape.arity (.u64 0)) (by simp)
    simp only [List.reverse_replicate, List.map_replicate] at hc
    let f := fun (arguments : List LeanExe.IR.Expr) => extractScalarExprWith
      (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
    obtain ⟨target, ht⟩ := ihb (.manyFunction shape.arity f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letManyFn (notScalar := notScalar)]; simp only [bind, hc, Option.bind_some, ht, f]⟩
  | @letUnitFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: .unit :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: .unit :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function true f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letUnitFn (notScalar := notScalar)]; simp [hc, ht, f]⟩
  | @letFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function false f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letFn (notScalar := notScalar)]; simp [hc, ht, f]⟩
  | @letBooleanFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.boolean argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.booleanFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBooleanFn (notScalar := notScalar)]; simp [hc, ht, f]⟩
  | letPredicateFn expression type function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression)
    obtain ⟨target, ht⟩ := ihb (.predicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by
      rw [extractScalarBooleanRangeWith_letPredicateFn (notScalar := notScalar)]
      apply scalarBooleanRangeCompleteContinuation_accepts_old
      apply scalarBooleanRangeContinuation_accepts_scalar (boolean := false) (locals := locals) (expression := expression) hc
      exact ht⟩
  | letBooleanPredicateFn expression type function _ ihb =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.boolean argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression)
    obtain ⟨target, ht⟩ := ihb (.booleanPredicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by
      rw [extractScalarBooleanRangeWith_letBooleanPredicateFn (notScalar := notScalar)]
      apply scalarBooleanRangeCompleteContinuation_accepts_old
      apply scalarBooleanRangeContinuation_accepts_scalar (boolean := true) (locals := locals) (expression := expression) hc
      exact ht⟩
  | letFlagResult _ body ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [extractScalarBooleanRangeWith_letFlag (notScalar := notScalar)]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | bindFlagResult input output _ body ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [extractScalarBooleanRangeWith_bindFlag (notScalar := notScalar)]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | letFlagBefore value _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarBooleanRangeWith_letFlag (notScalar := notScalar)]; exact scalarRangeValueBinding_accepts_primary hb hp⟩
  | bindFlagBefore input output value _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarBooleanRangeWith_bindFlag (notScalar := notScalar)]; exact scalarRangeValueBinding_accepts_primary hb hp⟩
  | letBefore value _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [notScalar, hb, hp]⟩
  | bindBefore input output value _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [notScalar, hb, hp]⟩
  | letResult value body =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [notScalar, rangeExitSupported_excludes_pure value, hp, hr]⟩
  | bindResult input output value body =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [notScalar, rangeExitSupported_excludes_pure value, hp, hr]⟩
  | idFunctionInput input result _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    simpa only [extractScalarBooleanRangeWith_idFunctionInput (notScalar := notScalar)] using ih locals typed total
  | idLet type _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    simpa only [extractScalarBooleanRangeWith_idLet (notScalar := notScalar)] using ih locals typed total
  | wrapped wrapper _ ih =>
    apply extractScalarBooleanRangeWith_accepts_fallback
    intro notScalar
    simpa only [extractScalarBooleanRangeWith_wrapped (notScalar := notScalar)] using ih locals typed total

theorem scalarBooleanRangeArm_supported {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) source))
      (fun _ => extractScalarBooleanRangeWith locals slot source) = some plan)
    (fallback : ∀ plan, extractScalarBooleanRangeWith locals slot source = some plan →
      BooleanRange.Supported (locals.map ScalarBinding.kind) source) :
    SupportedWith (locals.map ScalarBinding.kind) (.app (.const ``Bool.toUInt64 []) source) ∨
      BooleanRange.Supported (locals.map ScalarBinding.kind) source := by
  rcases scalarBooleanRangeArm_success compiled with ⟨value, matched, same⟩ | ⟨notScalar, matched⟩
  · exact .inl (extractScalarExprWith_supported matched)
  · exact .inr (fallback plan matched)

theorem extractScalarBooleanRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan) :
    BooleanRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanRangeWith locals slot source generalizing plan with
  | case1 locals source value matched =>
    exact .scalar (extractScalarExprWith_supported matched)
  | case2 locals name value body nondep bound matched notScalar ih =>
    exact .letBefore (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case3 locals name value body nondep notPure notScalar =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    exact .letResult (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case4 locals name value body nondep notScalar bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · exact .letFlagBefore (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .letFlagResult (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case5 locals name type value body nondep notScalar ih => exact .idLet type (ih compiled)
  | case6 => contradiction
  | case7 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord notMany helper parsed notScalar ih =>
    rw [booleanBinaryHelper_sound parsed]
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    exact .letBinaryPredicate helper
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case8 => contradiction
  | case9 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed checked validated notScalar ih =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    rw [sameType, sameValue]
    exact .letManyFn shape
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case10 => contradiction
  | case11 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letBinaryFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case12 => contradiction
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed notScalar enclosingIH directIH branchIH =>
    have sameType := booleanType_sound parsed
    subst resultType
    rcases scalarBooleanRangeCompleteContinuation_success compiled with previous |
      ⟨view, parsedChoice, guard, first, second, matched, ht, he, samePlan⟩
    · rcases scalarBooleanRangeContinuation_success previous with
        ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨call, argument, bound, sameBody, validated, emitted⟩
      · subst value
        exact .letPredicateFn expression type
          (by simpa [booleanRangeInput, ScalarBinding.kind] using extractScalarExprWith_supported validated)
          (by simpa [booleanRangePredicate, ScalarBinding.kind] using enclosingIH _ emitted)
      · subst body
        exact .applyWord ⟨name, typeName, typeBi, paramBi, type, nondep⟩ call
          (by simpa [booleanRangeArgument] using extractScalarExprWith_supported validated)
          (by simpa [booleanRangeInput, ScalarBinding.kind] using directIH _ emitted)
    · have shape := booleanFunctionChoice_sound parsedChoice
      subst body
      exact .wordFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view
        (extractScalarExprWith_supported matched)
        (branchIH view.yes (booleanFunctionChoice_sizes parsedChoice).1 ht)
        (branchIH view.no (booleanFunctionChoice_sizes parsedChoice).2 he)
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case16 => contradiction
  | case17 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed notScalar enclosingIH directIH branchIH =>
    have sameType := booleanType_sound parsed
    subst resultType
    rcases scalarBooleanRangeCompleteContinuation_success compiled with previous |
      ⟨view, parsedChoice, guard, first, second, matched, ht, he, samePlan⟩
    · rcases scalarBooleanRangeContinuation_success previous with
        ⟨expression, checked, sameValue, validated, emitted⟩ | ⟨call, argument, bound, sameBody, validated, emitted⟩
      · subst value
        exact .letBooleanPredicateFn expression type
          (by simpa [booleanRangeInput, ScalarBinding.kind] using extractScalarExprWith_supported validated)
          (by simpa [booleanRangePredicate, ScalarBinding.kind] using enclosingIH _ emitted)
      · subst body
        exact .applyBoolean ⟨name, typeName, typeBi, paramBi, type, nondep⟩ call
          (by simpa [booleanRangeArgument] using extractScalarExprWith_supported validated)
          (by simpa [booleanRangeInput, ScalarBinding.kind] using directIH _ emitted)
    · have shape := booleanFunctionChoice_sound parsedChoice
      subst body
      exact .booleanFunctionChoice ⟨name, typeName, typeBi, paramBi, type, nondep⟩ view
        (extractScalarExprWith_supported matched)
        (branchIH view.yes (booleanFunctionChoice_sizes parsedChoice).1 ht)
        (branchIH view.no (booleanFunctionChoice_sizes parsedChoice).2 he)
  | case18 => contradiction
  | case19 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letBooleanFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case20 => contradiction
  | case21 => contradiction
  | case22 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letUnitFn type .unit
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case23 => contradiction
  | case24 => contradiction
  | case25 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated notScalar ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letUnitFn type .punit
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case26 locals name typeName resultType typeBi paramName input value paramBi body nondep notScalar ih =>
    exact .idFunctionInput input resultType (ih compiled)
  | case27 => contradiction
  | case28 => contradiction
  | case29 locals input output value name domain body binder notWord types parsed notScalar bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .bindFlagResult types.1 types.2 (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case30 locals input output value name domain body binder types parsed bound matched notScalar ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case31 locals input output value name domain body binder types parsed notPure notScalar =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindResult types.1 types.2 (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case32 => contradiction
  | case33 => contradiction
  | case34 locals type condition evidence yes no resultType parsed guard matched notScalar yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, ht, second, he, rfl⟩ := compiled
    have same := booleanType_sound parsed
    subst type
    have firstSupport := scalarBooleanRangeArm_supported ht (fun plan h => yesIH h)
    have secondSupport := scalarBooleanRangeArm_supported he (fun plan h => noIH h)
    rcases firstSupport with scalarYes | rangeYes <;> rcases secondSupport with scalarNo | rangeNo
    · exact .choiceScalars resultType (extractScalarExprWith_supported matched) scalarYes scalarNo
    · exact .choiceScalarLeft resultType (extractScalarExprWith_supported matched) scalarYes rangeNo
    · exact .choiceScalarRight resultType (extractScalarExprWith_supported matched) rangeYes scalarNo
    · exact .choice resultType (extractScalarExprWith_supported matched) rangeYes rangeNo
  | case35 locals source notLet notFlag notIdLet notBinaryFunction notFunction notBooleanFunction notUnitFunction notPUnitFunction notIdFunction notBind notIf wrapper body parsed notScalar ih =>
    rw [booleanRangeWrapper_sound parsed]
    exact .wrapped wrapper (ih compiled)
  | case36 => exact .accumulator (extractScalarBooleanAccumulatorWith_supported compiled)

end LeanExe.Extract.Core
