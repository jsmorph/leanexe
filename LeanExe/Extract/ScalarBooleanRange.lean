import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarRangeBinding
import LeanExe.Extract.ScalarBooleanRangeContinuation
import LeanExe.Extract.ScalarBooleanFunctionChoice
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanRange

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

/-- Reuse a checked word loop and replace its result with a Boolean conversion. -/
def extractScalarBooleanRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
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
  | .letE _ (.forallE firstTypeName (.const ``UInt64 [])
      (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) body _ =>
      match scalarResultType? resultType with
      | none =>
          match scalarManyFunction?
              (.forallE firstTypeName (.const ``UInt64 [])
                (.forallE secondTypeName (.const ``UInt64 []) resultType secondTypeBi) firstTypeBi)
              (.lam firstName (.const ``UInt64 []) (.lam secondName (.const ``UInt64 []) value secondBi) firstBi) with
          | none => none
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
      | none => none
termination_by sizeOf source
decreasing_by
  all_goals first | (simp_wf; omega) | exact booleanRangeWrapper_size _wrapped

@[simp] theorem extractScalarBooleanRangeWith_let (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``UInt64 []) value body nondep) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_bind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input : ResultType) (output : BooleanType)
    (value body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bind name binder input output value body) = (match extractScalarExprWith locals value with
      | some bound => extractScalarBooleanRangeWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) (.app (.const ``Bool.toUInt64 []) body)
          pure { plan with result }) := by
  rw [BooleanRange.bind, BooleanBindingForm.expr, extractScalarBooleanRangeWith, booleanRangeBindTypes_accepts]

@[simp] theorem extractScalarBooleanRangeWith_letFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.const ``Bool []) value body nondep) = scalarRangeValueBinding
        (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body)) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_bindFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (binder : Lean.BinderInfo) (input output : BooleanType) (value body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.bindBoolean name binder input output value body) = scalarRangeValueBinding
        (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun flag => extractScalarBooleanRangeWith (.boolean flag :: locals) slot body)
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun flag => extractScalarExprWith (.boolean flag :: locals) (.app (.const ``Bool.toUInt64 []) body)) := by
  rw [BooleanRange.bindBoolean, BooleanBindingForm.expr, extractScalarBooleanRangeWith,
    booleanRangeBindTypes_not_boolean, booleanRangeFlagBindTypes_accepts]

@[simp] theorem extractScalarBooleanRangeWith_idLet (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name (.app (.const ``Id [.zero]) type) value body nondep) =
      extractScalarBooleanRangeWith locals slot (.letE name type value body nondep) := by
  rw [extractScalarBooleanRangeWith]

@[simp] theorem extractScalarBooleanRangeWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.function false (fun argument => extractScalarExprWith (.word argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_accepts]
  · cases extractScalarExprWith (.word (.u64 0) :: locals) value <;> rfl
  · cases type <;> simp [ResultType.expr]

@[simp] theorem extractScalarBooleanRangeWith_letBooleanFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
        extractScalarBooleanRangeWith
          (.booleanFunction (fun argument => extractScalarExprWith (.boolean argument :: locals) value) :: locals) slot body) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_accepts]
  cases extractScalarExprWith (.boolean (.u64 0) :: locals) value <;> rfl

theorem extractScalarBooleanRangeWith_letPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : BooleanType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) value paramBi) body nondep) =
      scalarBooleanRangeCompleteContinuation locals false value body
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
        (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
          (.lam paramName (.const ``UInt64 []) value paramBi) arm nondep)) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_boolean, booleanType_accepts]
  · cases type <;> simp [BooleanType.expr]

theorem extractScalarBooleanRangeWith_letBooleanPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : BooleanType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) value paramBi) body nondep) =
      scalarBooleanRangeCompleteContinuation locals true value body
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot body)
        (fun binding => extractScalarBooleanRangeWith (binding :: locals) slot value)
        (fun arm _ => extractScalarBooleanRangeWith locals slot (.letE name
          (.forallE typeName (.const ``Bool []) type.expr typeBi)
          (.lam paramName (.const ``Bool []) value paramBi) arm nondep)) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_boolean, booleanType_accepts]

@[simp] theorem extractScalarBooleanRangeWith_idFunctionInput (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (input result value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) body nondep) =
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE typeName input result typeBi) (.lam paramName input value paramBi) body nondep) := by
  rw [extractScalarBooleanRangeWith]
  simp only [ite_true]

theorem extractScalarBooleanRangeWith_letBinaryFn (locals : List ScalarBinding) (slot : Nat)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarBooleanRangeWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) slot b) := by
  rw [extractScalarBooleanRangeWith, scalarResultType_accepts]
  simp only []
  cases extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a <;> rfl

theorem extractScalarBooleanRangeWith_letManyFn (locals : List ScalarBinding) (slot : Nat)
    (shape : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (shape.bind name body nondep) = (do
      let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
      extractScalarBooleanRangeWith (.manyFunction shape.arity (fun arguments =>
        extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) slot body) := by
  rw [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow,
    Parameter.arrow, Parameter.lambda, Parameter.lambda, extractScalarBooleanRangeWith,
    scalarFunctionSuffix_not_result shape.suffix shape.positive]
  have accepted := scalarManyFunction_accepts shape
  simp only [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at accepted
  rw [accepted]
  simp only []
  cases extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body <;> rfl

theorem extractScalarBooleanRangeWith_letUnitFn (locals : List ScalarBinding) (slot : Nat)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : UnitSyntax) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanRangeWith locals slot (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarBooleanRangeWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) slot b) := by
  cases unitForm <;> rw [UnitSyntax.type, extractScalarBooleanRangeWith, scalarResultType_accepts]
  all_goals cases extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_choice (locals : List ScalarBinding) (slot : Nat)
    (type : BooleanType) (condition evidence yes no : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (BooleanRange.choiceExpr type condition evidence yes no) = (do
      let guard ← extractScalarExprWith locals (BooleanRange.decision condition evidence)
      let first ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
        (fun _ => extractScalarBooleanRangeWith locals slot yes)
      let second ← scalarBooleanRangeArm (extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
        (fun _ => extractScalarBooleanRangeWith locals slot no)
      pure (ScalarRangeExitPlan.choice guard first second)) := by
  rw [BooleanRange.choiceExpr, extractScalarBooleanRangeWith, booleanType_accepts]
  cases extractScalarExprWith locals (BooleanRange.decision condition evidence) <;> rfl

@[simp] theorem extractScalarBooleanRangeWith_wrapped (locals : List ScalarBinding) (slot : Nat)
    (wrapper : BooleanWrapper) (body : Lean.Expr) :
    extractScalarBooleanRangeWith locals slot (wrapper.expr body) =
      extractScalarBooleanRangeWith locals slot body := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
  all_goals rw [extractScalarBooleanRangeWith.eq_def]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

theorem extractScalarBooleanRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
  | wordFunctionChoice shape choice condition _ _ yesIH noIH =>
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition locals typed total
    rw [BooleanFunctionBinding.bodyExpr, extractScalarBooleanRangeWith_letPredicateFn]
    apply scalarBooleanRangeCompleteContinuation_accepts_choice matched
    · intro smaller
      exact yesIH locals typed total
    · intro smaller
      exact noIH locals typed total
  | booleanFunctionChoice shape choice condition _ _ yesIH noIH =>
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition locals typed total
    rw [BooleanFunctionBinding.bodyExpr, extractScalarBooleanRangeWith_letBooleanPredicateFn]
    apply scalarBooleanRangeCompleteContinuation_accepts_choice matched
    · intro smaller
      exact yesIH locals typed total
    · intro smaller
      exact noIH locals typed total
  | @applyWord types a b parameterName shape call argument _ ih =>
    obtain ⟨bound, matched⟩ := extractScalarExprWith_accepts argument locals typed total
    have emitted := ih (.word bound :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [BooleanFunctionBinding.callExpr, extractScalarBooleanRangeWith_letPredicateFn]
    obtain ⟨plan, accepted⟩ := scalarBooleanRangeContinuation_accepts_direct
      (locals := locals) (boolean := false) (value := b) (call := call)
      (enclosing := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot (call.expr a))
      (direct := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot b) matched emitted
    exact ⟨plan, scalarBooleanRangeCompleteContinuation_accepts_old accepted⟩
  | @applyBoolean types a b parameterName shape call argument _ ih =>
    obtain ⟨bound, matched⟩ := extractScalarExprWith_accepts argument locals typed total
    have emitted := ih (.boolean bound :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [BooleanFunctionBinding.callExpr, extractScalarBooleanRangeWith_letBooleanPredicateFn]
    obtain ⟨plan, accepted⟩ := scalarBooleanRangeContinuation_accepts_direct
      (locals := locals) (boolean := true) (value := b) (call := call)
      (enclosing := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot (call.expr a))
      (direct := fun binding => extractScalarBooleanRangeWith (binding :: locals) slot b) matched emitted
    exact ⟨plan, scalarBooleanRangeCompleteContinuation_accepts_old accepted⟩
  | @choice types test evidence yes no type condition _ _ yesIH noIH =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inr (yesIH locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inr (noIH locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice, hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalarLeft types test evidence yes no type condition first _ noIH =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inl (extractScalarExprWith_accepts first locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inr (noIH locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice, hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalarRight types test evidence yes no type condition _ second yesIH =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inr (yesIH locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inl (extractScalarExprWith_accepts second locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice, hg, bind, Option.bind_some, ht, he, pure]⟩
  | @choiceScalars types test evidence yes no type condition first second =>
    obtain ⟨guard, hg⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨yesPlan, ht⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) yes))
      (range := fun _ => extractScalarBooleanRangeWith locals slot yes) (Or.inl (extractScalarExprWith_accepts first locals typed total))
    obtain ⟨noPlan, he⟩ := scalarBooleanRangeArm_accepts
      (scalar := extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) no))
      (range := fun _ => extractScalarBooleanRangeWith locals slot no) (Or.inl (extractScalarExprWith_accepts second locals typed total))
    exact ⟨ScalarRangeExitPlan.choice guard yesPlan noPlan, by
      simp only [extractScalarBooleanRangeWith_choice, hg, bind, Option.bind_some, ht, he, pure]⟩
  | @letBinaryFn types a b name firstTypeName secondTypeName secondTypeBi firstTypeBi firstName secondName secondBi firstBi nondep type function _ ihb =>
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
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBinaryFn]; simp [hc, ht, f]⟩
  | letManyFn shape function _ ihb =>
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
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letManyFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
  | @letUnitFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type unitForm function _ ihb =>
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
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letUnitFn]; simp [hc, ht, f]⟩
  | @letFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
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
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letFn]; simp [hc, ht, f]⟩
  | @letBooleanFn types a b name typeName typeBi paramName paramBi nondep type function _ ihb =>
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
    exact ⟨target, by rw [extractScalarBooleanRangeWith_letBooleanFn]; simp [hc, ht, f]⟩
  | letPredicateFn expression type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression.expr)
    obtain ⟨target, ht⟩ := ihb (.predicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by
      rw [extractScalarBooleanRangeWith_letPredicateFn]
      apply scalarBooleanRangeCompleteContinuation_accepts_old
      apply scalarBooleanRangeContinuation_accepts_scalar (boolean := false) (locals := locals) (expression := expression) hc
      exact ht⟩
  | letBooleanPredicateFn expression type function _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function (.boolean argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals)
      (.app (.const ``Bool.toUInt64 []) expression.expr)
    obtain ⟨target, ht⟩ := ihb (.booleanPredicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by
      rw [extractScalarBooleanRangeWith_letBooleanPredicateFn]
      apply scalarBooleanRangeCompleteContinuation_accepts_old
      apply scalarBooleanRangeContinuation_accepts_scalar (boolean := true) (locals := locals) (expression := expression) hc
      exact ht⟩
  | letFlagResult _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [extractScalarBooleanRangeWith_letFlag]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | bindFlagResult input output _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    rw [extractScalarBooleanRangeWith_bindFlag]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | letFlagBefore value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarBooleanRangeWith_letFlag]; exact scalarRangeValueBinding_accepts_primary hb hp⟩
  | bindFlagBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarBooleanRangeWith_bindFlag]; exact scalarRangeValueBinding_accepts_primary hb hp⟩
  | letBefore value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
  | bindBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by simp [hb, hp]⟩
  | letResult value body =>
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [rangeExitSupported_excludes_pure value, hp, hr]⟩
  | bindResult input output value body =>
    obtain ⟨plan, hp⟩ := extractScalarRangeExitWith_accepts value locals slot typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{ plan with result }, by simp [rangeExitSupported_excludes_pure value, hp, hr]⟩
  | idFunctionInput input result _ ih =>
    simpa only [extractScalarBooleanRangeWith_idFunctionInput] using ih locals typed total
  | idLet type _ ih => simpa only [extractScalarBooleanRangeWith_idLet] using ih locals typed total
  | wrapped wrapper _ ih => simpa using ih locals typed total

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
  | case1 locals name value body nondep bound matched ih =>
    exact .letBefore (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case2 locals name value body nondep notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    exact .letResult (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case3 locals name value body nondep bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · exact .letFlagBefore (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .letFlagResult (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case4 locals name type value body nondep ih => exact .idLet type (ih compiled)
  | case5 => contradiction
  | case6 => contradiction
  | case7 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed checked validated ih =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    rw [sameType, sameValue]
    exact .letManyFn shape
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case8 => contradiction
  | case9 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letBinaryFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case10 => contradiction
  | case11 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed enclosingIH directIH branchIH =>
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
  | case12 => contradiction
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case14 => contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed enclosingIH directIH branchIH =>
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
  | case16 => contradiction
  | case17 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letBooleanFn type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case18 => contradiction
  | case19 => contradiction
  | case20 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letUnitFn type .unit
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case21 => contradiction
  | case22 => contradiction
  | case23 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed checked validated ih =>
    have same := scalarResultType_sound parsed
    subst resultType
    exact .letUnitFn type .punit
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case24 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    exact .idFunctionInput input resultType (ih compiled)
  | case25 => contradiction
  | case26 => contradiction
  | case27 locals input output value name domain body binder notWord types parsed bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, result, hp, hr, rfl⟩
    · exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .bindFlagResult types.1 types.2 (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case28 locals input output value name domain body binder types parsed bound matched ih =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindBefore types.1 types.2 (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case29 locals input output value name domain body binder types parsed notPure =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hp, result, hr, _⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindResult types.1 types.2 (extractScalarRangeExitWith_supported hp)
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case30 => contradiction
  | case31 => contradiction
  | case32 locals type condition evidence yes no resultType parsed guard matched yesIH noIH =>
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
  | case33 locals source notLet notFlag notIdLet notBinaryFunction notFunction notBooleanFunction notUnitFunction notPUnitFunction notIdFunction notBind notIf wrapper body parsed ih =>
    rw [booleanRangeWrapper_sound parsed]
    exact .wrapped wrapper (ih compiled)
  | case34 => contradiction

end LeanExe.Extract.Core
