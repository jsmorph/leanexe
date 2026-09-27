import LeanExe.Extract.ScalarBooleanRangeCorrectness
import LeanExe.Extract.ScalarBooleanRangeInvariant
import LeanExe.Source.ScalarBooleanWordRange

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Exact standard Id annotations for a Boolean action and word continuation. -/
def booleanWordRangeBindTypes? (input domain output : Lean.Expr) : Option (BooleanType × ResultType) := do
  let first ← booleanType? input
  let last ← scalarResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanWordRangeBindTypes_accepts (input : BooleanType) (output : ResultType) :
    booleanWordRangeBindTypes? input.expr input.expr output.expr = some (input, output) := by
  simp [booleanWordRangeBindTypes?]

theorem booleanWordRangeBindTypes_sound {input domain output : Lean.Expr}
    {first : BooleanType} {last : ResultType}
    (parsed : booleanWordRangeBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = last.expr := by
  simp only [booleanWordRangeBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨booleanType_sound ha, same ▸ booleanType_sound ha, scalarResultType_sound hb⟩
  · contradiction

@[simp] theorem booleanWordRangeBindTypes_not_word (input : ResultType) (domain output : Lean.Expr) :
    booleanWordRangeBindTypes? input.expr domain output = none := by
  simp [booleanWordRangeBindTypes?]

/-- Reuse a Boolean loop and evaluate a pure word continuation at its final store. -/
def extractScalarBooleanWordRangeWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match source with
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
          | some shape => do
              let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
              let function := ScalarBinding.manyFunction shape.arity fun arguments =>
                extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body
              extractScalarBooleanWordRangeWith (function :: locals) slot body
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
          let function := ScalarBinding.binaryFunction fun first second =>
            extractScalarExprWith (.word second :: .word first :: locals) value
          extractScalarBooleanWordRangeWith (function :: locals) slot body
  | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
      (.lam _ (.const ``UInt64 []) value _) body _ =>
      match scalarResultType? resultType with
      | none =>
          match booleanType? resultType with
          | none => none
          | some _ => do
              let expression ← booleanLocalOperands? value
              let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
                (.app (.const ``Bool.toUInt64 []) expression.expr)
              let function := ScalarBinding.predicateFunction fun argument =>
                extractScalarExprWith (.word argument :: locals)
                  (.app (.const ``Bool.toUInt64 []) expression.expr)
              extractScalarBooleanWordRangeWith (function :: locals) slot body
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
          let function := ScalarBinding.function false fun argument =>
            extractScalarExprWith (.word argument :: locals) value
          extractScalarBooleanWordRangeWith (function :: locals) slot body
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
          extractScalarBooleanWordRangeWith (function :: locals) slot body
  | .letE _ (.forallE _ (.const ``Bool []) resultType _)
      (.lam _ (.const ``Bool []) value _) body _ =>
      match scalarResultType? resultType with
      | none =>
          match booleanType? resultType with
          | none => none
          | some _ => do
              let expression ← booleanLocalOperands? value
              let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
                (.app (.const ``Bool.toUInt64 []) expression.expr)
              let function := ScalarBinding.booleanPredicateFunction fun argument =>
                extractScalarExprWith (.boolean argument :: locals)
                  (.app (.const ``Bool.toUInt64 []) expression.expr)
              extractScalarBooleanWordRangeWith (function :: locals) slot body
      | some _ => do
          let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
          let function := ScalarBinding.booleanFunction fun argument =>
            extractScalarExprWith (.boolean argument :: locals) value
          extractScalarBooleanWordRangeWith (function :: locals) slot body
  | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
      if input = domain then
        extractScalarBooleanWordRangeWith locals slot (.letE name
          (.forallE typeName input resultType typeBi) (.lam paramName domain value paramBi) body nondep)
      else none
  | .letE _ type value body _ =>
      match booleanType? type with
      | none =>
          match scalarResultType? type with
          | none => none
          | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
            (fun bound => extractScalarBooleanWordRangeWith (.word bound :: locals) slot body)
            (fun _ => extractScalarBooleanWordRangeWith locals slot value)
            (fun bound => extractScalarExprWith (.word bound :: locals) body)
      | some _ => scalarRangeLoopFirstBinding
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.boolean bound :: locals) body)
        (fun _ => extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun bound => extractScalarBooleanWordRangeWith (.boolean bound :: locals) slot body)
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam _ domain body _) =>
      match booleanWordRangeBindTypes? input domain output with
      | none =>
          match scalarBindTypes? input domain output with
          | none => none
          | some _ => scalarRangeValueBinding (extractScalarExprWith locals value)
            (fun bound => extractScalarBooleanWordRangeWith (.word bound :: locals) slot body)
            (fun _ => extractScalarBooleanWordRangeWith locals slot value)
            (fun bound => extractScalarExprWith (.word bound :: locals) body)
      | some _ => scalarRangeLoopFirstBinding
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.boolean bound :: locals) body)
        (fun _ => extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun bound => extractScalarBooleanWordRangeWith (.boolean bound :: locals) slot body)
  | .app (.const ``Bool.toUInt64 []) value => extractScalarBooleanRangeWith locals slot value
  | .app (.app (.const ``Id.run [.zero]) type) body =>
      match scalarResultType? type with
      | none => none
      | some _ => extractScalarBooleanWordRangeWith locals slot body
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) type) body =>
      match scalarResultType? type with
      | none => none
      | some _ => extractScalarBooleanWordRangeWith locals slot body
  | .mdata _ body => extractScalarBooleanWordRangeWith locals slot body
  | _ => none
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

theorem extractScalarBooleanWordRangeWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) a
        extractScalarBooleanWordRangeWith (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals) a) :: locals) slot b) := by
  rw [extractScalarBooleanWordRangeWith, scalarResultType_accepts]
  cases type <;> simp [ResultType.expr]

theorem extractScalarBooleanWordRangeWith_letPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.BooleanType) (expression : LeanExe.Source.Scalar.BooleanLocal)
    (b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) expression.expr)
        extractScalarBooleanWordRangeWith (.predicateFunction (fun argument =>
          extractScalarExprWith (.word argument :: locals)
            (.app (.const ``Bool.toUInt64 []) expression.expr)) :: locals) slot b) := by
  rw [extractScalarBooleanWordRangeWith, scalarResultType_boolean, booleanType_accepts,
    booleanLocalOperands_expr]
  all_goals first | rfl | (cases type <;> simp [LeanExe.Source.Scalar.BooleanType.expr])

theorem extractScalarBooleanWordRangeWith_letBooleanPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.BooleanType) (expression : LeanExe.Source.Scalar.BooleanLocal)
    (b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) expression.expr paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals)
          (.app (.const ``Bool.toUInt64 []) expression.expr)
        extractScalarBooleanWordRangeWith (.booleanPredicateFunction (fun argument =>
          extractScalarExprWith (.boolean argument :: locals)
            (.app (.const ``Bool.toUInt64 []) expression.expr)) :: locals) slot b) := by
  rw [extractScalarBooleanWordRangeWith, scalarResultType_boolean, booleanType_accepts,
    booleanLocalOperands_expr]
  all_goals first | rfl | (cases type <;> simp [LeanExe.Source.Scalar.BooleanType.expr])

theorem extractScalarBooleanWordRangeWith_letBooleanFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) a
        extractScalarBooleanWordRangeWith (.booleanFunction (fun argument =>
          extractScalarExprWith (.boolean argument :: locals) a) :: locals) slot b) := by
  rw [extractScalarBooleanWordRangeWith, scalarResultType_accepts]

theorem extractScalarBooleanWordRangeWith_letBinaryFn (locals : List ScalarBinding) (slot : Nat)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarBooleanWordRangeWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) slot b) := by
  rw [extractScalarBooleanWordRangeWith, scalarResultType_accepts]

theorem extractScalarBooleanWordRangeWith_letManyFn (locals : List ScalarBinding) (slot : Nat)
    (shape : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (shape.bind name body nondep) = (do
      let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
      extractScalarBooleanWordRangeWith (.manyFunction shape.arity (fun arguments =>
        extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) slot body) := by
  rw [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow,
    Parameter.arrow, Parameter.lambda, Parameter.lambda, extractScalarBooleanWordRangeWith,
    scalarFunctionSuffix_not_result shape.suffix shape.positive]
  have accepted := scalarManyFunction_accepts shape
  simp only [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at accepted
  rw [accepted]

theorem extractScalarBooleanWordRangeWith_letUnitFn (locals : List ScalarBinding) (slot : Nat)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : UnitSyntax) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarBooleanWordRangeWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) slot b) := by
  cases unitForm <;> rw [UnitSyntax.type, extractScalarBooleanWordRangeWith, scalarResultType_accepts] <;> rfl

@[simp] theorem extractScalarBooleanWordRangeWith_idFunctionInput (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (input result value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
      (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) body nondep) =
    extractScalarBooleanWordRangeWith locals slot (.letE name
      (.forallE typeName input result typeBi) (.lam paramName input value paramBi) body nondep) := by
  rw [extractScalarBooleanWordRangeWith]
  simp only [ite_true]

theorem extractScalarBooleanWordRangeWith_letWord (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (input : ResultType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name input.expr value body nondep) =
      scalarRangeValueBinding (extractScalarExprWith locals value)
        (fun bound => extractScalarBooleanWordRangeWith (.word bound :: locals) slot body)
        (fun _ => extractScalarBooleanWordRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.word bound :: locals) body) := by
  rw [extractScalarBooleanWordRangeWith, booleanType_scalar, scalarResultType_accepts]
  all_goals cases input <;> simp [ResultType.expr]

theorem extractScalarBooleanWordRangeWith_letFlag (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (input : BooleanType) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarBooleanWordRangeWith locals slot (.letE name input.expr value body nondep) =
      scalarRangeLoopFirstBinding
        (fun _ => extractScalarBooleanRangeWith locals slot value)
        (fun bound => extractScalarExprWith (.boolean bound :: locals) body)
        (fun _ => extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value))
        (fun bound => extractScalarBooleanWordRangeWith (.boolean bound :: locals) slot body) := by
  rw [extractScalarBooleanWordRangeWith, booleanType_accepts]
  all_goals cases input <;> simp [BooleanType.expr]

/-- Every independently supported Boolean-to-word continuation is accepted. -/
theorem extractScalarBooleanWordRangeWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanWordRange.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanWordRangeWith locals slot source = some plan := by
  induction supported generalizing locals with
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letPredicateFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letBooleanPredicateFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letBooleanFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letBinaryFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letManyFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarBooleanWordRangeWith_letUnitFn]; simp [hc, ht, f]⟩
  | idFunctionInput input result _ ih =>
    simpa only [extractScalarBooleanWordRangeWith_idFunctionInput] using ih locals typed total
  | letFlagBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith_letFlag]
    exact scalarRangeLoopFirstBinding_accepts_scalar hb hp
  | bindFlagBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.boolean bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [BooleanWordRange.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_accepts]
    exact scalarRangeLoopFirstBinding_accepts_scalar hb hp
  | letWordBefore input value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith_letWord]
    exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
  | bindWordBefore input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    simp only [Identity.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
    exact ⟨plan, scalarRangeValueBinding_accepts_primary hb hp⟩
  | letWordResult input _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    simp only [extractScalarBooleanWordRangeWith_letWord]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | bindWordResult input output _ body ih =>
    obtain ⟨before, hp⟩ := ih locals typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.word before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    simp only [Identity.bind, extractScalarBooleanWordRangeWith, booleanWordRangeBindTypes_not_word, scalarBindTypes_accepts]
    exact scalarRangeValueBinding_accepts_loop hp ht
  | letResult input value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by rw [extractScalarBooleanWordRangeWith_letFlag]; simp [scalarRangeLoopFirstBinding, hp, ht]⟩
  | bindResult input output value body =>
    obtain ⟨before, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    obtain ⟨tail, ht⟩ := extractScalarExprWith_accepts body (.boolean before.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨{before with result := tail}, by simp [BooleanWordRange.bind, extractScalarBooleanWordRangeWith, scalarRangeLoopFirstBinding, hp, ht]⟩
  | converted value =>
    obtain ⟨plan, hp⟩ := extractScalarBooleanRangeWith_accepts value locals slot typed total
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩
  | run type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [Identity.run, extractScalarBooleanWordRangeWith, hp]⟩
  | pure type _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [Identity.pure, extractScalarBooleanWordRangeWith, hp]⟩
  | metadata _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by simp [extractScalarBooleanWordRangeWith, hp]⟩


theorem extractScalarBooleanWordRangeWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanWordRangeWith locals slot source = some plan) :
    BooleanWordRange.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanWordRangeWith locals slot source generalizing plan with
  | case1 => contradiction
  | case2 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    rw [sameType, sameValue]
    exact .letManyFn shape (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case3 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letBinaryFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case4 => contradiction
  | case5 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    rw [booleanType_sound parsed, booleanLocalOperands_sound parsedValue]
    exact .letPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih expression compiled)
  | case6 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case7 => contradiction
  | case8 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letUnitFn type .unit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case9 => contradiction
  | case10 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letUnitFn type .punit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case11 => contradiction
  | case12 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    rw [booleanType_sound parsed, booleanLocalOperands_sound parsedValue]
    exact .letBooleanPredicateFn expression type
      (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih expression compiled)
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letBooleanFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported validated)
      (by simpa [ScalarBinding.kind] using ih compiled)
  | case14 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    exact .idFunctionInput input resultType (ih compiled)
  | case15 => contradiction
  | case16 => contradiction
  | case17 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed bodyIH valueIH =>
    rw [scalarResultType_sound parsed]
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .letWordBefore input (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .letWordResult input (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case18 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed bodyIH =>
    rw [booleanType_sound parsed]
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · exact .letResult input (extractScalarBooleanRangeWith_supported hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
    · exact .letFlagBefore input (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
  | case19 => contradiction
  | case20 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · exact .bindWordBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
    · exact .bindWordResult types.1 types.2 (valueIH hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
  | case21 locals input output value name domain body binder types parsed bodyIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · exact .bindResult types.1 types.2 (extractScalarBooleanRangeWith_supported hp)
        (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported ht)
    · exact .bindFlagBefore types.1 types.2 (extractScalarExprWith_supported matched)
        (by simpa [ScalarBinding.kind] using bodyIH bound hc)
  | case22 => exact .converted (extractScalarBooleanRangeWith_supported compiled)
  | case23 => contradiction
  | case24 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .run result (ih compiled)
  | case25 => contradiction
  | case26 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    exact .pure result (ih compiled)
  | case27 locals data body ih => exact .metadata (ih compiled)
  | case28 => contradiction


theorem extractScalarBooleanWordRangeWith_correct {source : Lean.Expr} {locals : List ScalarBinding}
    {plan : ScalarRangeExitPlan} (saved : List UInt64) (values : List Value)
    (compiled : extractScalarBooleanWordRangeWith locals saved.length source = some plan)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : RangeExitBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ result, BooleanWordRange.Eval source values result ∧ plan.Meaning saved result := by
  fun_induction extractScalarBooleanWordRangeWith locals saved.length source generalizing values plan with
  | case1 => contradiction
  | case2 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound parsed
    have supported := extractScalarExprWith_supported validated
    have function : SupportedWith (List.replicate shape.arity .word ++ locals.map ScalarBinding.kind) shape.body := by
      simpa [ScalarBinding.kind] using supported
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates values typed
    obtain ⟨flag, evaluated, meaning⟩ := ih (.manyFunction shape.arity f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro arguments native target len argumentsMeaning hc
        exact extractScalarExprWith_correct (meanings native (argumentsMeaning.length.symm.trans len)) hc
          ((bindings accumulator index stop exitFlag).words argumentsMeaning.reverse)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro arguments len
          exact extractScalarExprWith_accepts function (arguments.reverse.map ScalarBinding.word ++ locals)
            (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len])
            (scalarWords_total _ total)
        · exact total binding member)
    rw [sameType, sameValue]
    exact ⟨flag, .letManyFn shape meanings evaluated, meaning⟩
  | case3 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x y : UInt64) := supported.evaluates (.word y :: .word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x y => (native x y).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.binaryFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro first x second y target hx hy hc
        exact extractScalarExprWith_correct ((native x y).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .word first) (value := .word x) hx).cons
            (binding := .word second) (value := .word y) hy)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro first second
          apply extractScalarExprWith_accepts supported (.word second :: .word first :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBinaryFn type (fun x y => (native x y).choose_spec) evaluated, meaning⟩
  | case4 => contradiction
  | case5 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    have sameType := booleanType_sound parsed
    subst resultType
    have sameValue := booleanLocalOperands_sound parsedValue
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : UInt64, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.word x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih expression (.predicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case6 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function false f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case7 => contradiction
  | case8 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .unit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case9 => contradiction
  | case10 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : UInt64) := supported.evaluates (.word x :: .unit :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.function true f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          (((bindings accumulator index stop exitFlag).cons (binding := .unit) (value := .unit) trivial).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.word argument :: .unit :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letUnitFn type .punit (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case11 => contradiction
  | case12 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    have sameType := booleanType_sound parsed
    subst resultType
    have sameValue := booleanLocalOperands_sound parsedValue
    subst value
    have supported := extractScalarExprWith_supported validated
    have native : ∀ x : Bool, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := supported.evaluates (.boolean x :: values)
        (by simp [Value.kind, ScalarBinding.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih expression (.booleanPredicateFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanPredicateFn expression type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    have same := scalarResultType_sound parsed
    subst resultType
    have supported := extractScalarExprWith_supported validated
    have native (x : Bool) := supported.evaluates (.boolean x :: values)
      (by simp [Value.kind, ScalarBinding.kind, typed])
    let f := fun x => (native x).choose
    obtain ⟨flag, evaluated, meaning⟩ := ih (.booleanFunction f :: values) compiled
      (by simp [Value.kind, ScalarBinding.kind, typed]) (by
        intro accumulator index stop exitFlag
        apply (bindings accumulator index stop exitFlag).cons
        intro argument x target hx hc
        exact extractScalarExprWith_correct ((native x).choose_spec) hc
          ((bindings accumulator index stop exitFlag).cons hx)) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · intro argument
          apply extractScalarExprWith_accepts supported (.boolean argument :: locals)
          · rfl
          · intro binding member
            rcases List.mem_cons.mp member with rfl | member
            · trivial
            · exact total binding member
        · exact total binding member)
    exact ⟨flag, .letBooleanFn type (fun x => (native x).choose_spec) evaluated, meaning⟩
  | case14 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    obtain ⟨result, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨result, .idFunctionInput input resultType evaluated, meaning⟩
  | case15 => contradiction
  | case16 => contradiction
  | case17 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed bodyIH valueIH =>
    rw [scalarResultType_sound parsed]
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · obtain ⟨word, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.word word :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind evaluated matched) (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .letWordBefore input evaluated continuation, meaning⟩
    · obtain ⟨word, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.word word :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .letWordResult input evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case18 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed bodyIH =>
    rw [booleanType_sound parsed]
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        extractScalarBooleanRangeWith_correct saved values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .letResult input evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .letFlagBefore input evaluated continuation, meaning⟩
  | case19 => contradiction
  | case20 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · obtain ⟨word, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.word word :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) (bindings.bind evaluated matched) (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .bindWordBefore types.1 types.2 evaluated continuation, meaning⟩
    · obtain ⟨word, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        valueIH values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.word word :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .bindWordResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
  | case21 locals input output value name domain body binder types parsed bodyIH =>
    obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound parsed
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨flag, evaluated, stop, start, step, countEval, initialEval, stepEval, resultEval⟩ :=
        extractScalarBooleanRangeWith_correct saved values hp typed bindings total
      obtain ⟨result, continuation⟩ := (extractScalarExprWith_supported ht).evaluates
        (.boolean flag :: values) (by simp [Value.kind, ScalarBinding.kind, typed])
      refine ⟨result, .bindResult types.1 types.2 evaluated continuation, stop, start, step, countEval, initialEval, stepEval, ?_⟩
      intro exitFlag
      exact extractScalarExprWith_correct continuation ht
        ((bindings (Range.Exit.iterate step stop.toNat 0 start) stop.toNat stop exitFlag).cons (resultEval exitFlag))
    · obtain ⟨encoded, evaluated⟩ := (extractScalarExprWith_supported matched).evaluates values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      have extended : RangeExitBindingsMatch (.boolean bound :: locals) (.boolean flag :: values) saved := by
        intro accumulator index stop done
        exact (bindings accumulator index stop done).cons
          (extractScalarExprWith_correct evaluated matched (bindings accumulator index stop done))
      obtain ⟨result, continuation, meaning⟩ := bodyIH bound (.boolean flag :: values) hc
        (by simp [Value.kind, ScalarBinding.kind, typed]) extended (by
          intro binding member
          rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)
      exact ⟨result, .bindFlagBefore types.1 types.2 evaluated continuation, meaning⟩
  | case22 =>
    obtain ⟨flag, evaluated, meaning⟩ := extractScalarBooleanRangeWith_correct saved values compiled typed bindings total
    exact ⟨flag.toUInt64, .converted evaluated, meaning⟩
  | case23 => contradiction
  | case24 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .run result evaluated, meaning⟩
  | case25 => contradiction
  | case26 locals type body result parsed ih =>
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .pure result evaluated, meaning⟩
  | case27 locals data body ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih values compiled typed bindings total
    exact ⟨value, .metadata evaluated, meaning⟩
  | case28 => contradiction


theorem extractScalarBooleanWordRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanWordRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarBooleanWordRangeWith locals slot source generalizing plan with
  | case1 => contradiction
  | case2 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep notWord shape parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro arguments target len holds extracted
      exact extractScalarExprWith_invariant P literal binary choice extracted (scalarWords_holds
        (fun argument member => holds argument (by simpa using member)) bindings)
    · exact bindings binding member
  | case3 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro first second target firstValid secondValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact secondValid
      rcases List.mem_cons.mp member with rfl | member
      · exact firstValid
      · exact bindings binding member
    · exact bindings binding member
  | case4 => contradiction
  | case5 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    apply ih expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case6 locals name typeName resultType typeBi paramName value paramBi body nondep notBinary type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case7 => contradiction
  | case8 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case9 => contradiction
  | case10 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | case11 => contradiction
  | case12 locals name typeName resultType typeBi paramName value paramBi body nondep notWord type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨expression, parsedValue, checked, validated, compiled⟩ := compiled
    apply ih expression compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep type parsed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, validated, compiled⟩ := compiled
    apply ih compiled
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target argumentValid extracted
      apply extractScalarExprWith_invariant P literal binary choice extracted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact argumentValid
      · exact bindings binding member
    · exact bindings binding member
  | case14 locals name typeName resultType typeBi paramName input value paramBi body nondep ih =>
    exact ih compiled bindings
  | case15 => contradiction
  | case16 => contradiction
  | case17 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn notBoolean input parsed bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
    · obtain ⟨count, initial, step, done, result⟩ := valueIH hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
  | case18 locals name type value body nondep notBinary notUnary notUnit notPunit notBoolFn notIdFn input parsed bodyIH =>
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨count, initial, step, done, result⟩ := extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
  | case19 => contradiction
  | case20 locals input output value name domain body binder notBoolean types parsed bodyIH valueIH =>
    rcases scalarRangeValueBinding_success compiled with ⟨bound, matched, hc⟩ | ⟨before, tail, hp, ht, rfl⟩
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
    · obtain ⟨count, initial, step, done, result⟩ := valueIH hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
  | case21 locals input output value name domain body binder types parsed bodyIH =>
    rcases scalarRangeLoopFirstBinding_success compiled with ⟨before, tail, hp, ht, rfl⟩ | ⟨bound, matched, hc⟩
    · obtain ⟨count, initial, step, done, result⟩ := extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index hp bindings
      refine ⟨count, initial, step, done, ?_⟩
      apply extractScalarExprWith_invariant P literal binary choice ht
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact result
      · exact bindings binding member
    · apply bodyIH bound hc
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact extractScalarExprWith_invariant P literal binary choice matched bindings
      · exact bindings binding member
  | case22 => exact extractScalarBooleanRangeWith_invariant P literal binary choice accumulator index compiled bindings
  | case23 => contradiction
  | case24 locals type body result parsed ih => exact ih compiled bindings
  | case25 => contradiction
  | case26 locals type body result parsed ih => exact ih compiled bindings
  | case27 locals data body ih => exact ih compiled bindings
  | case28 => contradiction


end LeanExe.Extract.Core
