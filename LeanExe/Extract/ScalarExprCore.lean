import LeanExe.Extract.ScalarLiteralInstance
import LeanExe.Extract.ScalarCall
import LeanExe.Extract.ScalarArguments
import LeanExe.Extract.ScalarManyFunction
import LeanExe.Extract.ScalarHead
import LeanExe.Extract.ScalarComplement
import LeanExe.Extract.ScalarExtremum
import LeanExe.Extract.ScalarDo
import LeanExe.Extract.ScalarBooleanLocalBindings
import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarBooleanLocalDependentBranch
import LeanExe.Extract.ScalarDependentBranch
import LeanExe.Extract.ScalarGuard
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

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
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) numeral) evidence =>
      match naturalLiteral? numeral with
      | some n => if literalInstance? n evidence 0 then some (.u64 n) else none
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
      | none => none
      | some _ => do
          let bound ← extractScalarExprWith locals value
          extractScalarExprWith (.word bound :: locals) body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match scalarResultType? type with
      | none => none
      | some _ =>
        match _h : comparison? condition evidence with
        | none =>
          match _g : compoundGuard? condition evidence with
          | none =>
            match _booleanGuard : booleanLocalGuard? condition evidence with
            | none => none
            | some guard => do
                let c ← extractBooleanLocalWith locals guard.value
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
      match scalarResultType? type with
      | none => none
      | some _ =>
          match _guard : dependentGuard? condition evidence trueDomain falseDomain with
          | none =>
              match _booleanGuard : booleanLocalDependentGuard? condition evidence trueDomain falseDomain with
              | none => none
              | some guard => do
                  let c ← extractBooleanLocalWith locals guard.value
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
  | .letE _ (.const ``Bool []) value body _ =>
      match _boolean : booleanLocalOperands? value with
      | none => none
      | some expression => do
          let c ← extractBooleanLocalWith locals expression
            (fun operand _member => extractScalarExprWith locals operand)
          extractScalarExprWith (.boolean (guardWord c) :: locals) body
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
      | none => none
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
  | .app (.bvar index) argument => do
      let function ← locals[index]?.bind (ScalarBinding.function? false)
      let value ← extractScalarExprWith locals argument
      function value
  | .mdata _ body => extractScalarExprWith locals body
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (exact scalarManyCall_size _call _member)
    | (have bounds := scalarManyFunction_body_size _function; simp_all; omega)
    | (have bounds := booleanLocalDependentGuard_size _booleanGuard _member; omega)
    | (have bounds := dependentGuard_size _guard _member; omega)
    | (have bounds := booleanLocalOperands_size _boolean _member; omega)
    | (have bounds := booleanLocalGuard_size _booleanGuard _member; omega)
    | (have bounds := comparison_size _h; omega)
    | (have bounds := compoundGuard_size _g _member; omega)

/-- Source argument indices map to the production IR's materialized slots. -/
def extractScalarExpr (locals : List Nat) (source : Lean.Expr) : Option LeanExe.IR.Expr :=
  extractScalarExprWith (locals.map fun slot => .word (.local slot)) source

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
  | canonical meaning => cases meaning <;> dsimp only [LeanExe.Source.Scalar.classHead] <;>
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

theorem extractScalarExprWith_dependentBranch (guard : LeanExe.Source.Scalar.Guard)
    (locals : List ScalarBinding) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = (do
      let c ← extractGuard guard (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith (.unit :: locals) t
      let onFalse ← extractScalarExprWith (.unit :: locals) e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.Guard.dependentBranch, extractScalarExprWith,
    scalarResultType_accepts, dependentGuard_accepts]

theorem extractScalarExprWith_letBoolean (locals : List ScalarBinding)
    (expression : LeanExe.Source.Scalar.BooleanLocal) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name (.const ``Bool []) expression.expr body nondep) = (do
      let c ← extractBooleanLocalWith locals expression
        (fun operand _ => extractScalarExprWith locals operand)
      extractScalarExprWith (.boolean (guardWord c) :: locals) body) := by
  rw [extractScalarExprWith, booleanLocalOperands_expr]

theorem extractScalarExprWith_booleanBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.branch type.expr t e) = (do
      let c ← extractBooleanLocalWith locals guard.value
        (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.BooleanLocalGuard.branch, extractScalarExprWith,
    scalarResultType_accepts, booleanLocalGuard_not_comparison, booleanLocal_not_compound,
    booleanLocalGuard_accepts]

theorem extractScalarExprWith_booleanDependentBranch (locals : List ScalarBinding)
    (guard : LeanExe.Source.Scalar.BooleanLocalGuard) (type : LeanExe.Source.Scalar.ResultType)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) :
    extractScalarExprWith locals (guard.dependentBranch type.expr tn fn tb fb t e) = (do
      let c ← extractBooleanLocalWith locals guard.value
        (fun operand _ => extractScalarExprWith locals operand)
      let onTrue ← extractScalarExprWith (.unit :: locals) t
      let onFalse ← extractScalarExprWith (.unit :: locals) e
      pure (.ite c onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.BooleanLocalGuard.dependentBranch, extractScalarExprWith,
    scalarResultType_accepts, booleanLocalDependentGuard_not_closed,
    booleanLocalDependentGuard_accepts]

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

theorem extractScalarExprWith_ofNatNatural (locals : List ScalarBinding)
    {n : Nat} {numeral evidence : Lean.Expr}
    (numberMeaning : LeanExe.Source.Scalar.NaturalLiteral n numeral)
    (instanceMeaning : LeanExe.Source.Scalar.LiteralInstance n 0 evidence) :
    extractScalarExprWith locals (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) numeral) evidence) = some (.u64 n) := by
  rw [extractScalarExprWith, naturalLiteral_accepts numberMeaning]
  simp [literalInstance_accepts instanceMeaning]

theorem extractScalarExprWith_ofNatInstance (locals : List ScalarBinding)
    {n : Nat} {evidence : Lean.Expr} (meaning : LeanExe.Source.Scalar.LiteralInstance n 0 evidence) :
    extractScalarExprWith locals (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n))) evidence) = some (.u64 n) :=
  extractScalarExprWith_ofNatNatural locals .raw meaning

@[simp] theorem extractScalarExprWith_literalExpr (locals : List ScalarBinding) (n : Nat) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) := by
  simp [extractScalarExprWith, LeanExe.Source.Scalar.literalExpr, literalInstance?, naturalLiteral?]

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
