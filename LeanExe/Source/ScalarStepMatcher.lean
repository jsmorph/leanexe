import LeanExe.Source.ScalarBooleanStep

namespace LeanExe.Source.Scalar.StepMatcher

/-- Binder names and visibility are retained from the actual declaration. -/
structure Binder where
  name : Lean.Name
  info : Lean.BinderInfo
  deriving Repr

def Binder.forallE (binder : Binder) (domain body : Lean.Expr) : Lean.Expr :=
  .forallE binder.name domain body binder.info

def Binder.lam (binder : Binder) (domain body : Lean.Expr) : Lean.Expr :=
  .lam binder.name domain body binder.info

/-- The signature and forwarding binders of a generated Boolean-step matcher. -/
structure Shape where
  motive : Binder
  motiveArgument : Binder
  scrutinee : Binder
  doneHandler : Binder
  donePayload : Binder
  yieldHandler : Binder
  yieldPayload : Binder
  forwardMotive : Binder
  forwardDone : Binder
  forwardYield : Binder
  deriving Repr

def boolean : Lean.Expr := .const ``Bool []
def step : Lean.Expr := BooleanStep.resultType .boolean

def Shape.motiveType (shape : Shape) (level : Lean.Level) : Lean.Expr :=
  shape.motiveArgument.forallE step (.sort level)

def Shape.doneType (shape : Shape) : Lean.Expr :=
  shape.donePayload.forallE boolean (.app (.bvar 2) (BooleanStep.doneDirect (.bvar 0)))

def Shape.yieldType (shape : Shape) : Lean.Expr :=
  shape.yieldPayload.forallE boolean (.app (.bvar 3) (BooleanStep.yieldDirect (.bvar 0)))

def Shape.type (shape : Shape) (level : Lean.Level) : Lean.Expr :=
  shape.motive.forallE (shape.motiveType level)
    (shape.scrutinee.forallE step (shape.doneHandler.forallE shape.doneType
      (shape.yieldHandler.forallE shape.yieldType (.app (.bvar 3) (.bvar 2)))))

def cases (level : Lean.Level) (motive value doneBody yieldBody : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``ForInStep.casesOn [level, .zero]) #[boolean, motive, value, doneBody, yieldBody]

def Shape.value (shape : Shape) (level : Lean.Level) : Lean.Expr :=
  shape.motive.lam (shape.motiveType level)
    (shape.scrutinee.lam step (shape.doneHandler.lam shape.doneType
      (shape.yieldHandler.lam shape.yieldType
        (cases level
          (shape.forwardMotive.lam step (.app (.bvar 4) (.bvar 0))) (.bvar 2)
          (shape.forwardDone.lam boolean (.app (.bvar 2) (.bvar 0)))
          (shape.forwardYield.lam boolean (.app (.bvar 1) (.bvar 0)))))))

def call (name : Lean.Name) (motive value doneBody yieldBody : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const name [.succ .zero]) #[motive, value, doneBody, yieldBody]

/-- Native meaning of the forwarding body rendered by Shape.value. -/
def denote {motive : ForInStep Bool → Sort u} (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

theorem denote_cases {motive : ForInStep Bool → Sort u} (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) :
    denote value doneBody yieldBody = ForInStep.casesOn value doneBody yieldBody := by
  cases value <;> rfl

/-- A source declaration certificate checks its body, type and safety, without
using its name as evidence that it implements a matcher. -/
inductive Defined (env : Lean.Environment) (name : Lean.Name) : Prop where
  | intro (info : Lean.ConstantInfo) (level : Lean.Name) (shape : Shape)
      (lookup : env.find? name = some info)
      (parameters : info.levelParams = [level])
      (safe : info.isUnsafe = false) (total : info.isPartial = false)
      (type : info.type = shape.type (.param level))
      (value : info.value? = some (shape.value (.param level))) : Defined env name

end LeanExe.Source.Scalar.StepMatcher
