import LeanExe.Extract.ScalarStep

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

theorem extractScalarStepWith_yield (locals : List ScalarStepBinding) (a : Lean.Expr) :
    extractScalarStepWith locals (Range.yieldValue a) = (do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      pure { value, done := .u64 0 }) := by
  rw [Range.yieldValue, extractScalarStepWith]
  change extractScalarStepWith locals (Step.yieldDirect a) = _
  rw [Step.yieldDirect, extractScalarStepWith]

theorem extractScalarStepWith_done (locals : List ScalarStepBinding) (a : Lean.Expr) :
    extractScalarStepWith locals (Step.doneValue a) = (do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      pure { value, done := .u64 1 }) := by
  rw [Step.doneValue, extractScalarStepWith]
  change extractScalarStepWith locals (Step.doneDirect a) = _
  rw [Step.doneDirect, extractScalarStepWith]

theorem extractScalarStepWith_yieldDirect (locals : List ScalarStepBinding) (a : Lean.Expr) :
    extractScalarStepWith locals (Step.yieldDirect a) = (do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      pure { value, done := .u64 0 }) := by rw [Step.yieldDirect, extractScalarStepWith]

theorem extractScalarStepWith_doneDirect (locals : List ScalarStepBinding) (a : Lean.Expr) :
    extractScalarStepWith locals (Step.doneDirect a) = (do
      let value ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      pure { value, done := .u64 1 }) := by rw [Step.doneDirect, extractScalarStepWith]

theorem extractScalarStepWith_letE (locals : List ScalarStepBinding)
    (name : Lean.Name) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name (.const ``UInt64 []) a b nondep) = (do
      let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      extractScalarStepWith (.scalar (.word bound) :: locals) b) := by rw [extractScalarStepWith]

theorem extractScalarStepWith_bind (locals : List ScalarStepBinding) (type : Step.ResultAnnotation)
    (name : Lean.Name) (bi : Lean.BinderInfo) (a b : Lean.Expr) :
    extractScalarStepWith locals (Step.bindWord name bi type a b) = (do
      let bound ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      extractScalarStepWith (.scalar (.word bound) :: locals) b) := by rw [Step.bindWord, extractScalarStepWith, scalarStepResultType_accepts]

theorem extractScalarStepWith_branch (locals : List ScalarStepBinding)
    (op : Comparison) (type : Step.ResultAnnotation) (a b t e : Lean.Expr) :
    extractScalarStepWith locals (Step.branch op type a b t e) = (do
      let ai ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) a
      let bi ← extractScalarExprWith (locals.map ScalarStepBinding.toScalar) b
      let ti ← extractScalarStepWith locals t
      let ei ← extractScalarStepWith locals e
      pure { value := .ite (lowerComparison op ai bi) ti.value ei.value
             done := .ite (lowerComparison op ai bi) ti.done ei.done }) := by
  rw [Step.branch, Range.branch, extractScalarStepWith, scalarStepResultType_accepts, comparison_accepts]

theorem extractScalarStepWith_letFn (locals : List ScalarStepBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals.map ScalarStepBinding.toScalar) a
        extractScalarStepWith (.scalar (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals.map ScalarStepBinding.toScalar) a)) :: locals) b) := by
  rw [extractScalarStepWith, scalarResultType_accepts]

theorem extractScalarStepWith_letUnitFn (locals : List ScalarStepBinding)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name
      (.forallE unitTypeName (.const ``Unit [])
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName (.const ``Unit [])
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals.map ScalarStepBinding.toScalar) a
        extractScalarStepWith (.scalar (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals.map ScalarStepBinding.toScalar) a)) :: locals) b) := by
  rw [extractScalarStepWith, scalarResultType_accepts]

theorem extractScalarStepWith_letStepFn (locals : List ScalarStepBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : Step.ResultAnnotation) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name
      (.forallE typeName (.const ``UInt64 []) (Step.resultType type) typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: locals) a
        extractScalarStepWith (.function false (fun argument =>
          extractScalarStepWith (.scalar (.word argument) :: locals) a) :: locals) b) := by
  rw [extractScalarStepWith, scalarResultType_not_step, scalarStepResultType_accepts]

theorem extractScalarStepWith_letUnitStepFn (locals : List ScalarStepBinding)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : Step.ResultAnnotation) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name
      (.forallE unitTypeName (.const ``Unit [])
        (.forallE typeName (.const ``UInt64 []) (Step.resultType type) typeBi) unitTypeBi)
      (.lam unitName (.const ``Unit [])
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarStepWith (.scalar (.word (.u64 0)) :: .scalar .unit :: locals) a
        extractScalarStepWith (.function true (fun argument =>
          extractScalarStepWith (.scalar (.word argument) :: .scalar .unit :: locals) a) :: locals) b) := by
  rw [extractScalarStepWith, scalarResultType_not_step, scalarStepResultType_accepts]

theorem extractScalarStepWith_idRun (locals : List ScalarStepBinding) (type : Step.ResultAnnotation) (a : Lean.Expr) :
    extractScalarStepWith locals (Step.idRun type a) = extractScalarStepWith locals a := by
  rw [Step.idRun, extractScalarStepWith, scalarStepResultType_accepts]

theorem extractScalarStepWith_idPure (locals : List ScalarStepBinding) (type : Step.ResultAnnotation) (a : Lean.Expr) :
    extractScalarStepWith locals (Step.idPure type a) = extractScalarStepWith locals a := by
  rw [Step.idPure, extractScalarStepWith, scalarStepResultType_accepts]

theorem extractScalarStepWith_letResult (locals : List ScalarStepBinding)
    (name : Lean.Name) (type : Step.ResultAnnotation) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarStepWith locals (.letE name (Step.resultType type) a b nondep) = (do
      let bound ← extractScalarStepWith locals a
      extractScalarStepWith (.result bound :: locals) b) := by
  cases type <;> rw [Step.resultType, extractScalarStepWith] <;>
    simp [scalarStepResultType?, scalarStepResultType_accepts]

theorem extractScalarStepWith_bindResult (locals : List ScalarStepBinding)
    (name : Lean.Name) (bi : Lean.BinderInfo) (input output : Step.ResultAnnotation) (a b : Lean.Expr) :
    extractScalarStepWith locals (Step.bindResult name bi input output a b) = (do
      let bound ← extractScalarStepWith locals a
      extractScalarStepWith (.result bound :: locals) b) := by
  cases input <;> rw [Step.bindResult, Step.resultType, extractScalarStepWith] <;>
    simp [scalarStepResultType?, scalarStepResultType_accepts]

end LeanExe.Extract.Core
