import LeanExe.Extract.ScalarStepAcceptance
import LeanExe.Extract.ScalarStepSupported
import LeanExe.Extract.ScalarRangeStride
import LeanExe.Extract.ScalarRangeExitSyntax
import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.IR.ScalarRangeExitSlots

namespace LeanExe.Extract.Core

/-- One dynamic loop with a scalar accumulator and a pure result computation.
The allocated slots are accumulator, index, stop, and exit decision, in that order. -/
structure ScalarRangeExitPlan where
  count : LeanExe.IR.Expr
  initial : LeanExe.IR.Expr
  step : LeanExe.IR.Expr
  done : LeanExe.IR.Expr
  result : LeanExe.IR.Expr
  deriving Repr

def ScalarRangeExitPlan.body (plan : ScalarRangeExitPlan) (slot : Nat) : LeanExe.IR.Stmt :=
  .seq (.assign (slot + 2) plan.count)
    (.seq (.assign slot plan.initial)
      (.seq (.assign (slot + 1) (.u64 0))
        (.seq (.assign (slot + 3) (.u64 0))
          (.seq (.while (LeanExe.IR.rangeCondition slot)
            (LeanExe.IR.rangeExitBody slot plan.step plan.done))
            (.assign slot plan.result)))))

def ScalarRangeExitPlan.func (plan : ScalarRangeExitPlan) (name : Lean.Name)
    (exportName : Option String) (arity : Nat) : LeanExe.IR.Func :=
  { sourceName := name, exportName, params := arity, locals := arity + 4
    body := plan.body arity, results := [.local arity] }

/-- Extract a single early-exit range loop and surrounding pure computations.
The loop remains dynamic; its stop is evaluated once into a fresh local. -/
def extractScalarRangeExitWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarRangeExitPlan :=
  match scalarRangeExit? source with
  | some view => do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1))))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }
  | none =>
      match source with
      | .app (.app (.const ``Id.run [.zero]) sourceType) body =>
          match scalarResultType? sourceType with
          | none => none
          | some _ => extractScalarRangeExitWith locals slot body
      | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero])))) sourceType) body =>
          match scalarResultType? sourceType with
          | none => none
          | some _ => extractScalarRangeExitWith locals slot body
      | .letE _ (.const ``Bool []) value body _ =>
          match booleanLocalOperands? value with
          | none => none
          | some expression => do
              let c ← extractBooleanLocalWith locals expression
                (fun operand _ => extractScalarExprWith locals operand)
              extractScalarRangeExitWith (.boolean (guardWord c) :: locals) slot body
      | .letE _ (.const ``UInt64 []) value body _ =>
          match extractScalarExprWith locals value with
          | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
          | none => do
              let plan ← extractScalarRangeExitWith locals slot value
              let result ← extractScalarExprWith (.word plan.result :: locals) body
              pure { plan with result }
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
                  extractScalarRangeExitWith (function :: locals) slot body
          | some _ => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) value
              let function := ScalarBinding.binaryFunction fun first second =>
                extractScalarExprWith (.word second :: .word first :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
      | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
          (.lam _ (.const ``UInt64 []) value _) body _ =>
          match scalarResultType? resultType with
          | none =>
              match booleanType? resultType with
              | none => none
              | some _ => do
                  let expression ← booleanLocalOperands? value
                  let _ ← extractBooleanLocalWith (.word (.u64 0) :: locals) expression
                    (fun operand _ => extractScalarExprWith (.word (.u64 0) :: locals) operand)
                  let function := ScalarBinding.predicateFunction fun argument => do
                    let condition ← extractBooleanLocalWith (.word argument :: locals) expression
                      (fun operand _ => extractScalarExprWith (.word argument :: locals) operand)
                    pure (guardWord condition)
                  extractScalarRangeExitWith (function :: locals) slot body
          | some _ => do
              let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
              let function := ScalarBinding.function false fun argument =>
                extractScalarExprWith (.word argument :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
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
              extractScalarRangeExitWith (function :: locals) slot body
      | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero]))) input) output) value)
          (.lam _ domain body _) =>
          match scalarBindTypes? input domain output with
          | none =>
              match booleanBindType? scalarResultType? input domain output with
              | none => none
              | some _ =>
                  match booleanAction? value with
                  | none => none
                  | some action => do
                      let c ← extractBooleanLocalWith locals action.leaf
                        (fun operand _ => extractScalarExprWith locals operand)
                      extractScalarRangeExitWith (.boolean (guardWord c) :: locals) slot body
          | some _ =>
              match extractScalarExprWith locals value with
              | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
              | none => do
                  let plan ← extractScalarRangeExitWith locals slot value
                  let result ← extractScalarExprWith (.word plan.result :: locals) body
                  pure { plan with result }
      | .letE _ (.forallE _ (.const ``Bool []) resultType _)
          (.lam _ (.const ``Bool []) value _) body _ =>
          match scalarResultType? resultType with
          | none => none
          | some _ => do
              let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) value
              let function := ScalarBinding.booleanFunction fun argument =>
                extractScalarExprWith (.boolean argument :: locals) value
              extractScalarRangeExitWith (function :: locals) slot body
      | .letE name (.forallE typeName (.app (.const ``Id [.zero]) input) resultType typeBi)
          (.lam paramName (.app (.const ``Id [.zero]) domain) value paramBi) body nondep =>
          if input = domain then
            match scalarResultType? input with
            | none => none
            | some _ =>
                match booleanType? resultType with
                | none => none
                | some _ => extractScalarRangeExitWith locals slot (.letE name
                    (.forallE typeName input resultType typeBi)
                    (.lam paramName domain value paramBi) body nondep)
          else none
      | .letE name (.app (.const ``Id [.zero]) type) value body nondep =>
          extractScalarRangeExitWith locals slot (.letE name type value body nondep)
      | .mdata _ body => extractScalarRangeExitWith locals slot body
      | _ => none
termination_by sizeOf source

open LeanExe.Source.Scalar

theorem rangeExitSupported_excludes_pure {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) :
    extractScalarExprWith locals source = none := by
  induction supported generalizing locals with
  | range =>
    simp [Range.Exit.call, Range.Exit.head, Lean.mkAppN, Lean.mkApp,
      extractScalarExprWith, ScalarPrimitive.ofHead?, scalarManyCall?, scalarLocalCall?]
  | letBoolean expression _ _ _ ih =>
    rw [extractScalarExprWith_letBoolean]
    simp only [bind, Option.bind_eq_none_iff]
    intro condition compiled
    exact ih _
  | idBindBoolean action type _ _ _ ih =>
    rw [extractScalarExprWith_booleanBind]
    simp only [bind, Option.bind_eq_none_iff]
    intro condition compiled
    exact ih _
  | letE value body ih =>
    rw [extractScalarExprWith]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | idRun type _ ih => simpa only [extractScalarExprWith_idRun] using ih locals
  | idPure type _ ih => simpa only [extractScalarExprWith_idPure] using ih locals
  | bindRight input output value body ih =>
    rw [extractScalarExprWith_idBind]
    cases extractScalarExprWith locals _ <;> simp [ih]
  | bindLeft input output value body ih => simp [extractScalarExprWith_idBind, ih]
  | letFn type _ _ ih =>
    rw [extractScalarExprWith_letFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letPredicateFn expression type _ _ _ ih =>
    rw [extractScalarExprWith_letPredicateFn]
    simp only [bind, Option.bind_eq_none_iff]
    intro condition compiled
    exact ih _
  | predicateInput input result _ ih =>
    rw [extractScalarExprWith_predicateInput]
    exact ih locals
  | letBooleanFn type _ _ ih =>
    rw [extractScalarExprWith_letBooleanFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letBinaryFn type _ _ ih =>
    rw [extractScalarExprWith_letBinaryFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letManyFn shape _ _ ih =>
    rw [extractScalarExprWith_letManyFn]
    cases extractScalarExprWith _ shape.body <;> simp [ih]
  | letUnitFn type unitForm _ _ ih =>
    rw [extractScalarExprWith_letUnitFn]
    cases extractScalarExprWith _ _ <;> simp [ih]
  | letLeft value body ih => simp [extractScalarExprWith, ih]
  | idLet _ ih => simpa only [extractScalarExprWith_idLet] using ih locals
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals

theorem extractScalarRangeExitWith_call (locals : List ScalarBinding) (slot : Nat)
    (view : ScalarRangeExitView) : extractScalarRangeExitWith locals slot view.source = (do
      let first ← extractScalarExprWith locals view.first.scalar
      let count ← extractScalarExprWith locals view.count.scalar
      let initial ← extractScalarExprWith locals view.initial
      let code ← extractScalarStepWith
        (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset first (scalarRangeScale view.stride.number (.local (slot + 1))))) ::
          locals.map ScalarStepBinding.scalar) view.body
      pure { count := scalarRangeTrips view.stride.number (scalarRangeDistance first count), initial, step := code.value, done := code.done, result := .local slot }) := by
  rw [extractScalarRangeExitWith.eq_def, scalarRangeExit_accepts]

@[simp] theorem extractScalarRangeExitWith_idRun (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) (type : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.run body type) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.run, extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

@[simp] theorem extractScalarRangeExitWith_idPure (locals : List ScalarBinding) (slot : Nat) (body : Lean.Expr) (type : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.pure body type) = extractScalarRangeExitWith locals slot body := by
  rw [Identity.pure, extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

theorem extractScalarRangeExitWith_booleanBind (locals : List ScalarBinding) (slot : Nat)
    (action : BooleanAction) (type : ResultType) (name : Lean.Name) (bi : Lean.BinderInfo) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (BooleanIdentity.bind name bi action.expr body type.expr) = (do
      let c ← extractBooleanLocalWith locals action.leaf
        (fun operand _ => extractScalarExprWith locals operand)
      extractScalarRangeExitWith (.boolean (guardWord c) :: locals) slot body) := by
  rw [BooleanIdentity.bind, extractScalarRangeExitWith, booleanBindType_not_scalar,
    booleanBindType_accepts _ (scalarResultType_accepts type), booleanAction_accepts]
  cases type <;> rfl

theorem extractScalarRangeExitWith_letBoolean (locals : List ScalarBinding) (slot : Nat)
    (expression : BooleanLocal) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name (.const ``Bool []) expression.expr body nondep) = (do
      let c ← extractBooleanLocalWith locals expression
        (fun operand _ => extractScalarExprWith locals operand)
      extractScalarRangeExitWith (.boolean (guardWord c) :: locals) slot body) := by
  rw [extractScalarRangeExitWith]
  change (match booleanLocalOperands? expression.expr with
    | none => none
    | some expression => do
        let c ← extractBooleanLocalWith locals expression
          (fun operand _ => extractScalarExprWith locals operand)
        extractScalarRangeExitWith (.boolean (guardWord c) :: locals) slot body) = _
  rw [booleanLocalOperands_expr]

theorem extractScalarRangeExitWith_letE (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name (.const ``UInt64 []) value body nondep) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_letFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) a
        extractScalarRangeExitWith (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals) a) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_accepts]
  · rfl
  · cases type <;> simp [ResultType.expr]

theorem extractScalarRangeExitWith_letPredicateFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.BooleanType) (expression : LeanExe.Source.Scalar.BooleanLocal)
    (b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep) = (do
        let _ ← extractBooleanLocalWith (.word (.u64 0) :: locals) expression
          (fun operand _member => extractScalarExprWith (.word (.u64 0) :: locals) operand)
        extractScalarRangeExitWith (.predicateFunction (fun argument => do
          let condition ← extractBooleanLocalWith (.word argument :: locals) expression
            (fun operand _member => extractScalarExprWith (.word argument :: locals) operand)
          pure (guardWord condition)) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_boolean, booleanType_accepts,
    booleanLocalOperands_expr]
  all_goals first | rfl | (cases type <;> simp [LeanExe.Source.Scalar.BooleanType.expr])

theorem extractScalarRangeExitWith_predicateInput (locals : List ScalarBinding) (slot : Nat)
    (input : LeanExe.Source.Scalar.ResultType) (result : LeanExe.Source.Scalar.BooleanType)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.predicateInputExpr (.identity input) result
      name typeName paramName typeBi paramBi a b nondep) =
    extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.predicateInputExpr input result
      name typeName paramName typeBi paramBi a b nondep) := by
  simp only [LeanExe.Source.Scalar.predicateInputExpr, LeanExe.Source.Scalar.ResultType.expr]
  rw [extractScalarRangeExitWith]
  simp [scalarRangeExit?, scalarResultType_accepts, booleanType_accepts]

theorem extractScalarRangeExitWith_letBooleanFn (locals : List ScalarBinding) (slot : Nat)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE typeName (.const ``Bool []) type.expr typeBi)
      (.lam paramName (.const ``Bool []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals) a
        extractScalarRangeExitWith (.booleanFunction (fun argument =>
          extractScalarExprWith (.boolean argument :: locals) a) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

theorem extractScalarRangeExitWith_letBinaryFn (locals : List ScalarBinding) (slot : Nat)
    (name firstTypeName secondTypeName firstName secondName : Lean.Name)
    (firstTypeBi secondTypeBi firstBi secondBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE firstTypeName (.const ``UInt64 [])
        (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
      (.lam firstName (.const ``UInt64 [])
        (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals) a
        extractScalarRangeExitWith (.binaryFunction (fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals) a) :: locals) slot b) := by
  rw [extractScalarRangeExitWith, scalarResultType_accepts]
  rfl

theorem extractScalarRangeExitWith_letManyFn (locals : List ScalarBinding) (slot : Nat)
    (shape : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (shape.bind name body nondep) = (do
      let _ ← extractScalarExprWith (List.replicate shape.arity (.word (.u64 0)) ++ locals) shape.body
      extractScalarRangeExitWith (.manyFunction shape.arity (fun arguments =>
        extractScalarExprWith (arguments.reverse.map ScalarBinding.word ++ locals) shape.body) :: locals) slot body) := by
  rw [ManyFunction.bind, ManyFunction.type, ManyFunction.value, Parameter.arrow,
    Parameter.arrow, Parameter.lambda, Parameter.lambda, extractScalarRangeExitWith,
    scalarFunctionSuffix_not_result shape.suffix shape.positive]
  have accepted := scalarManyFunction_accepts shape
  simp only [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda] at accepted
  rw [accepted]
  rfl

theorem extractScalarRangeExitWith_letUnitFn (locals : List ScalarBinding) (slot : Nat)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (unitForm : UnitSyntax) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (.letE name
      (.forallE unitTypeName unitForm.type
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName unitForm.type
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarRangeExitWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) slot b) := by
  cases unitForm <;> rw [UnitSyntax.type, extractScalarRangeExitWith, scalarResultType_accepts] <;> rfl

theorem extractScalarRangeExitWith_idBind (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) (input output : ResultType) :
    extractScalarRangeExitWith locals slot (Identity.bind name bi value body input output) =
      (match extractScalarExprWith locals value with
      | some bound => extractScalarRangeExitWith (.word bound :: locals) slot body
      | none => do
          let plan ← extractScalarRangeExitWith locals slot value
          let result ← extractScalarExprWith (.word plan.result :: locals) body
          pure { plan with result }) := by
  rw [Identity.bind, extractScalarRangeExitWith, scalarBindTypes_accepts]
  cases output <;> rfl

@[simp] theorem extractScalarRangeExitWith_idLet (locals : List ScalarBinding) (slot : Nat)
    (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) :
    extractScalarRangeExitWith locals slot (idLetExpr name type value body nondep) =
      extractScalarRangeExitWith locals slot (.letE name type value body nondep) := by
  rw [idLetExpr, extractScalarRangeExitWith]
  rfl

@[simp] theorem extractScalarRangeExitWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr) :
    extractScalarRangeExitWith locals slot (.mdata data body) = extractScalarRangeExitWith locals slot body := by
  rw [extractScalarRangeExitWith]
  rfl

theorem extractScalarRangeExitWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : Range.Exit.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarRangeExitWith locals slot source = some plan := by
  have extend {locals : List ScalarBinding} (total : ∀ binding ∈ locals, binding.Total)
      (value : LeanExe.IR.Expr) : ∀ binding ∈ ScalarBinding.word value :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact total binding member
  induction supported generalizing locals with
  | @range types first count initial body indexName accumulatorName indexBi accumulatorBi indexType stride hf hc hi hs =>
    obtain ⟨f, ef⟩ := extractScalarExprWith_accepts hf.scalar locals typed total
    obtain ⟨c, ec⟩ := extractScalarExprWith_accepts hc.scalar locals typed total
    obtain ⟨i, ei⟩ := extractScalarExprWith_accepts hi locals typed total
    obtain ⟨code, es⟩ := extractScalarStepWith_accepts hs
      (.scalar (.word (.local slot)) :: .scalar (.natural (scalarRangeOffset f (scalarRangeScale stride.number (.local (slot + 1))))) ::
        locals.map ScalarStepBinding.scalar)
      (by simp [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def, ← typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact total original present)
    refine ⟨{ count := scalarRangeTrips stride.number (scalarRangeDistance f c), initial := i, step := code.value, done := code.done, result := .local slot }, ?_⟩
    have equation := extractScalarRangeExitWith_call locals slot
      { indexType, stride, first, count, initial, indexName, accumulatorName, indexBi, accumulatorBi, body }
    simpa [ScalarRangeExitView.source, ef, ec, ei, es] using equation
  | letBoolean expression variables arguments _ ih =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals expression
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => extractScalarExprWith_accepts (arguments operand member) locals typed total)
    obtain ⟨plan, hp⟩ := ih (.boolean (guardWord c) :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarRangeExitWith_letBoolean]; simp [hc, hp]⟩
  | idBindBoolean action type variables arguments _ ih =>
    obtain ⟨c, hc⟩ := extractBooleanLocalWith_accepts (total := total) locals action.leaf
      (fun operand _ => extractScalarExprWith locals operand) (by simpa [typed] using variables)
      (fun operand member => extractScalarExprWith_accepts (arguments operand member) locals typed total)
    obtain ⟨plan, hp⟩ := ih (.boolean (guardWord c) :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨plan, by rw [extractScalarRangeExitWith_booleanBind]; simp [hc, hp]⟩
  | letE value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_letE]; simp [hb, hp]⟩
  | idRun type _ ih => simpa using ih locals typed total
  | idPure type _ ih => simpa using ih locals typed total
  | bindRight input output value _ ih =>
    obtain ⟨bound, hb⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨plan, hp⟩ := ih (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (extend total bound)
    exact ⟨plan, by rw [extractScalarRangeExitWith_idBind, hb]; exact hp⟩
  | bindLeft input output value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeExitWith_idBind, rangeExitSupported_excludes_pure value]; simp [hp, hr]⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letFn]; simp [hc, ht, f]⟩
  | letPredicateFn expression type variables arguments _ ihb =>
    have accepts (argument : LeanExe.IR.Expr) := extractBooleanLocalWith_accepts
      (.word argument :: locals) expression
      (fun operand _member => extractScalarExprWith (.word argument :: locals) operand)
      (by simpa [ScalarBinding.kind, typed] using variables)
      (fun operand member => extractScalarExprWith_accepts (arguments operand member) (.word argument :: locals)
        (by simp [ScalarBinding.kind, typed]) (by
          intro binding member; rcases List.mem_cons.mp member with rfl | member
          · trivial
          · exact total binding member)) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => do
      let condition ← extractBooleanLocalWith (.word argument :: locals) expression
        (fun operand _member => extractScalarExprWith (.word argument :: locals) operand)
      pure (guardWord condition)
    obtain ⟨target, ht⟩ := ihb (.predicateFunction f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · intro argument
          obtain ⟨condition, found⟩ := accepts argument
          exact ⟨guardWord condition, by simp [f, found]⟩
        · exact total binding member)
    refine ⟨target, ?_⟩
    rw [extractScalarRangeExitWith_letPredicateFn]
    simp only [hc, bind, Option.bind_some]
    exact ht
  | predicateInput input result _ ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    exact ⟨plan, by rw [extractScalarRangeExitWith_predicateInput]; exact hp⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letBooleanFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letBinaryFn]; simp [hc, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letManyFn]; simp only [bind, hc, Option.bind_some, ht, f]⟩
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
    exact ⟨target, by rw [extractScalarRangeExitWith_letUnitFn]; simp [hc, ht, f]⟩
  | letLeft value body ih =>
    obtain ⟨plan, hp⟩ := ih locals typed total
    obtain ⟨result, hr⟩ := extractScalarExprWith_accepts body (.word plan.result :: locals)
      (by simp [ScalarBinding.kind, typed]) (extend total plan.result)
    exact ⟨{ plan with result }, by
      rw [extractScalarRangeExitWith_letE, rangeExitSupported_excludes_pure value]; simp [hp, hr]⟩
  | idLet _ ih => simpa only [extractScalarRangeExitWith_idLet] using ih locals typed total
  | metadata _ ih => simpa using ih locals typed total

/-- Successful range extraction admits the independently stated source grammar. -/
theorem extractScalarRangeExitWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {slot : Nat} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith locals slot source = some plan) :
    Range.Exit.Supported (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarRangeExitWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRangeExit_sound matched
    subst source
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, hf, count, hc, initial, hi, code, hs, _⟩ := compiled
    exact .range view.indexType view.stride (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hf)) (Range.Exit.Count.Supported.of_scalar _ (extractScalarExprWith_supported hc)) (extractScalarExprWith_supported hi)
      (by simpa [ScalarStepBinding.kind, ScalarBinding.kind, List.map_map, Function.comp_def]
        using extractScalarStepWith_supported hs)
  | case2 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case3 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.run body type) = some plan at compiled
    exact .idRun type (ih (by simpa only [extractScalarRangeExitWith_idRun] using compiled))
  | case4 locals sourceType body invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case5 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.pure body type) = some plan at compiled
    exact .idPure type (ih (by simpa only [extractScalarRangeExitWith_idPure] using compiled))
  | case6 locals name value body nondep invalid rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid] at compiled
  | case7 locals name value body nondep expression matched rejected ih =>
    have same := booleanLocalOperands_sound matched
    subst value
    rw [extractScalarRangeExitWith_letBoolean] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply Range.Exit.Supported.letBoolean expression (extractBooleanLocalWith_variables hc)
    · intro operand member
      obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact extractScalarExprWith_supported found
    · simpa [ScalarBinding.kind] using ih c ht
  | case8 locals name value body nondep bound matched notRange ih =>
    rw [extractScalarRangeExitWith_letE, matched] at compiled
    exact .letE (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case9 locals name value body nondep notPure notRange ih =>
    rw [extractScalarRangeExitWith_letE, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .letLeft (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case10 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected noMany notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected, noMany] at compiled
  | case11 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep rejected shape matched notRange ihb =>
    obtain ⟨sameType, sameValue⟩ := scalarManyFunction_sound matched
    rw [sameType, sameValue] at compiled ⊢
    change Range.Exit.Supported _ (shape.bind name body nondep)
    change extractScalarRangeExitWith locals slot (shape.bind name body nondep) = some plan at compiled
    rw [extractScalarRangeExitWith_letManyFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letManyFn shape (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case12 locals name firstTypeName secondTypeName resultType secondTypeBi firstTypeBi firstName secondName value secondBi firstBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letBinaryFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBinaryFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case13 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected noBoolean notRange =>
    rw [extractScalarRangeExitWith] at compiled
    · simp [notRange, rejected, noBoolean] at compiled
    · exact excludedBinary
  | case14 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary rejected type matched notRange ihb =>
    rw [extractScalarRangeExitWith] at compiled
    · simp only [notRange, rejected, matched, bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨boolean, parsed, checked, hc, ht⟩ := compiled
      have sameType := booleanType_sound matched
      have sameValue := booleanLocalOperands_sound parsed
      subst resultType
      subst value
      exact .letPredicateFn boolean type
        (by simpa [ScalarBinding.kind] using extractBooleanLocalWith_variables hc)
        (fun operand member => by
          obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
          simpa [ScalarBinding.kind] using extractScalarExprWith_supported found)
        (by simpa [ScalarBinding.kind] using ihb boolean ht)
    · exact excludedBinary
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep excludedBinary type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case16 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case17 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .unit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .unit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case18 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case19 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letUnitFn (unitForm := .punit)] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type .punit (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case20 locals input output value name domain body bi invalid invalidBoolean rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid, invalidBoolean] at compiled
  | case21 locals input output value name domain body bi invalid type matched invalidAction rejected =>
    rw [extractScalarRangeExitWith] at compiled
    simp [rejected, invalid, matched, invalidAction] at compiled
  | case22 locals input output value name domain body bi invalid type matched action parsed rejected ih =>
    obtain ⟨hi, hd, ho⟩ := booleanBindType_sound _ matched
    have outputEq := scalarResultType_sound ho
    have valueEq := booleanAction_sound parsed
    subst input domain output value
    change extractScalarRangeExitWith locals slot
      (LeanExe.Source.Scalar.BooleanIdentity.bind name bi action.expr body type.expr) = some plan at compiled
    rw [extractScalarRangeExitWith_booleanBind] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨c, hc, ht⟩ := compiled
    apply Range.Exit.Supported.idBindBoolean action type (extractBooleanLocalWith_variables hc)
    · intro operand member
      obtain ⟨target, found⟩ := extractBooleanLocalWith_operands hc operand member
      exact extractScalarExprWith_supported found
    · simpa [ScalarBinding.kind] using ih c ht
  | case23 locals input output value name domain body bi annotations typesMatched bound matched rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, matched] at compiled
    exact .bindRight inputType outputType (extractScalarExprWith_supported matched) (by simpa [ScalarBinding.kind] using ih compiled)
  | case24 locals input output value name domain body bi annotations typesMatched notPure rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeExitWith locals slot (Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, _⟩ := compiled
    exact .bindLeft inputType outputType (ih hb) (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hr)
  | case25 locals name typeName resultType typeBi paramName value paramBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case26 locals name typeName resultType typeBi paramName value paramBi body nondep type matched notRange ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarRangeExitWith_letBooleanFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letBooleanFn type (by simpa [ScalarBinding.kind] using extractScalarExprWith_supported hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case27 locals name typeName resultType typeBi paramName domain value paramBi body nondep rejected notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, rejected] at compiled
  | case28 locals name typeName resultType typeBi paramName domain value paramBi body nondep inputType rejected foundInput notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, foundInput, rejected] at compiled
  | case29 locals name typeName resultType typeBi paramName domain value paramBi body nondep inputType result foundResult foundInput notRange ih =>
    rw [extractScalarRangeExitWith] at compiled
    simp only [notRange, ↓reduceIte, foundInput, foundResult] at compiled
    have inputEq := scalarResultType_sound foundInput
    have resultEq := booleanType_sound foundResult
    subst domain resultType
    exact .predicateInput inputType result (ih compiled)
  | case30 locals name typeName input resultType typeBi paramName domain value paramBi body nondep different notRange =>
    rw [extractScalarRangeExitWith] at compiled
    simp [notRange, different] at compiled
  | case31 locals name type value body nondep rejected ih =>
    change extractScalarRangeExitWith locals slot (idLetExpr name type value body nondep) = some plan at compiled
    exact .idLet (ih (by simpa only [extractScalarRangeExitWith_idLet] using compiled))
  | case32 locals data body rejected ih =>
    exact .metadata (ih (by simpa only [extractScalarRangeExitWith_metadata] using compiled))
  | case33 locals source rejected hrun hpure hboolLet hlet hbinary hunary hunit hpunit hbind hPredicateInput hidLet hmetadata =>
    rw [extractScalarRangeExitWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
