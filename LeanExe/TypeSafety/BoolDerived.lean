import LeanExe.TypeSafety.Typing

/-!
# Strict derived Boolean operations

These are transparent source definitions, not new expressions or machine frames.
Binary operations first build a strict pair, then eliminate both fields in a
closed Boolean body. Both source operands therefore evaluate once, left to right,
including operands whose Boolean value will not affect the result. Conditional
short-circuiting remains available separately through `Expr.ifE`.

The operation enumeration organizes this library; it is not part of the runtime
syntax. The definitions make no claim about compiler recognition or extraction.
-/

namespace LeanExe.TypeSafety

inductive BoolBinOp where
  | and | or | xor | eq
  deriving DecidableEq, Repr

def BoolBinOp.apply : BoolBinOp → Bool → Bool → Bool
  | .and, left, right => left && right
  | .or, left, right => left || right
  | .xor, left, right => Bool.xor left right
  | .eq, left, right => decide (left = right)

abbrev Expr.boolNot (value : Expr) : Expr := .ifE value (.bool false) (.bool true)

/-- Index zero is the left Boolean; index one is the right Boolean. -/
def BoolBinOp.body : BoolBinOp → Expr
  | .and => .ifE (.var 0) (.var 1) (.bool false)
  | .or => .ifE (.var 0) (.bool true) (.var 1)
  | .xor => .ifE (.var 0) (.boolNot (.var 1)) (.var 1)
  | .eq => .ifE (.var 0) (.var 1) (.boolNot (.var 1))

abbrev Expr.boolBin (operation : BoolBinOp) (left right : Expr) : Expr :=
  .split (.pair left right) operation.body

abbrev Expr.boolAnd (left right : Expr) : Expr := .boolBin .and left right
abbrev Expr.boolOr (left right : Expr) : Expr := .boolBin .or left right
abbrev Expr.boolXor (left right : Expr) : Expr := .boolBin .xor left right
abbrev Expr.boolEq (left right : Expr) : Expr := .boolBin .eq left right

variable {declarations : DataDecls} {signatures : Signatures} {Γ : Context}

theorem ExprTyped.boolNot (typed : ExprTyped declarations signatures Γ value .bool) :
    ExprTyped declarations signatures Γ (.boolNot value) .bool := .ifE typed .bool .bool

theorem BoolBinOp.body_typed (operation : BoolBinOp) :
    ExprTyped declarations signatures (.bool :: .bool :: Γ) operation.body .bool := by
  cases operation with
  | and => exact .ifE (.var rfl) (.var rfl) .bool
  | or => exact .ifE (.var rfl) .bool (.var rfl)
  | xor => exact .ifE (.var rfl) (.boolNot (.var rfl)) (.var rfl)
  | eq => exact .ifE (.var rfl) (.var rfl) (.boolNot (.var rfl))

theorem ExprTyped.boolBin (operation : BoolBinOp)
    (left : ExprTyped declarations signatures Γ leftExpr .bool)
    (right : ExprTyped declarations signatures Γ rightExpr .bool) :
    ExprTyped declarations signatures Γ (.boolBin operation leftExpr rightExpr) .bool :=
  .split (.pair left right) operation.body_typed

theorem inferRaw_boolNot : inferRaw declarations signatures Γ (.boolNot value) =
    if inferRaw declarations signatures Γ value = some .bool then some .bool else none := by
  simp [inferRaw]

theorem BoolBinOp.inferRaw_body (operation : BoolBinOp) :
    inferRaw declarations signatures (α :: β :: Γ) operation.body =
      if α = .bool then if β = .bool then some .bool else none else none := by
  by_cases left : α = .bool <;> by_cases right : β = .bool <;>
    cases operation <;> simp [BoolBinOp.body, inferRaw, lookup, left, right, eq_comm]

theorem inferRaw_boolBin : inferRaw declarations signatures Γ (.boolBin operation left right) =
    if inferRaw declarations signatures Γ left = some .bool then
      if inferRaw declarations signatures Γ right = some .bool then some .bool else none
    else none := by
  cases leftType : inferRaw declarations signatures Γ left with
  | none => simp [inferRaw, leftType]
  | some α =>
      cases rightType : inferRaw declarations signatures Γ right with
      | none => simp [inferRaw, leftType, rightType]
      | some β =>
          simp only [inferRaw, leftType, rightType, BoolBinOp.inferRaw_body,
            Option.some.injEq]

theorem uses_boolNot : uses index (.boolNot value) = uses index value := by simp [uses]

theorem admissible_boolNot : admissible (.boolNot value) = admissible value := by simp [admissible]

theorem BoolBinOp.body_uses_left (operation : BoolBinOp) : uses 0 operation.body = true := by
  cases operation <;> rfl

theorem BoolBinOp.body_uses_right (operation : BoolBinOp) : uses 1 operation.body = true := by
  cases operation <;> rfl

/-- The body refers only to its two fields, independently of the captured context. -/
theorem BoolBinOp.body_closed (operation : BoolBinOp) (index : Nat) :
    uses (index + 2) operation.body = false := by
  cases operation <;> rfl

theorem BoolBinOp.body_admissible (operation : BoolBinOp) : admissible operation.body = true := by
  cases operation <;> rfl

theorem uses_boolBin : uses index (.boolBin operation left right) =
    (uses index left || uses index right) := by
  simp [uses, BoolBinOp.body_closed]

theorem admissible_boolBin : admissible (.boolBin operation left right) =
    (admissible left && admissible right) := by
  simp [admissible, BoolBinOp.body_admissible, BoolBinOp.body_uses_left, BoolBinOp.body_uses_right]

/-- The conditional first evaluates the supplied operand in the captured environment. -/
theorem step_boolNot : step program (.eval (.boolNot value) env kont) =
    some (.eval value env (.ifBranches (.bool false) (.bool true) env :: kont)) := rfl

/-- The first stage constructs a strict pair before the Boolean body is entered. -/
theorem step_boolBin : step program (.eval (.boolBin operation left right) env kont) =
    some (.eval (.pair left right) env (.splitBody operation.body env :: kont)) := rfl

/-- After the initial administrative step, evaluation begins with the left operand. -/
theorem boolBin_left_stage :
    Steps program (.eval (.boolBin operation left right) env kont)
      (.eval left env (.pairLeft right env :: .splitBody operation.body env :: kont)) :=
  .tail (.tail .refl rfl) rfl

/-- Completion of the left operand starts the right, retaining the left result exactly once. -/
theorem step_boolBin_right_stage (operation : BoolBinOp) :
    step program (.ret leftValue (.pairLeft right env :: .splitBody operation.body env :: kont)) =
      some (.eval right env (.pairRight leftValue :: .splitBody operation.body env :: kont)) := rfl

/-- These final steps compute negation after its operand has already returned. -/
theorem boolNot_result_steps (value : Bool) :
    Steps program (.ret (.bool value) (.ifBranches (.bool false) (.bool true) env :: kont))
      (.ret (.bool (!value)) kont) := by
  cases value <;> exact .tail (.tail .refl rfl) rfl

/-- Evaluation of the closed body implements the selected truth table in any environment. -/
theorem BoolBinOp.body_result_steps (operation : BoolBinOp) (left right : Bool) :
    Steps program (.eval operation.body (.bool left :: .bool right :: env) kont)
      (.ret (.bool (operation.apply left right)) kont) := by
  cases operation <;> cases left <;> cases right
  all_goals first
    | exact .tail (.tail (.tail (.tail .refl rfl) rfl) rfl) rfl
    | exact .tail (.tail (.tail (.tail (.tail (.tail (.tail .refl rfl) rfl) rfl) rfl) rfl) rfl) rfl

/-- Once both operands return, pair elimination and the closed body produce the Boolean result. -/
theorem boolBin_result_steps (operation : BoolBinOp) (left right : Bool) :
    Steps program
      (.ret (.bool right) (.pairRight (.bool left) :: .splitBody operation.body env :: kont))
      (.ret (.bool (operation.apply left right)) kont) := by
  have enter : Steps program
      (.ret (.bool right) (.pairRight (.bool left) :: .splitBody operation.body env :: kont))
      (.eval operation.body (.bool left :: .bool right :: env) kont) :=
    .tail (.tail .refl rfl) rfl
  exact enter.trans (operation.body_result_steps left right)

/-- Negation's source definition computes the truth table for every supplied Boolean. -/
theorem boolNot_value_steps (value : Bool) :
    Steps program (.eval (.boolNot (.bool value)) env kont) (.ret (.bool (!value)) kont) := by
  have ready : Steps program (.eval (.boolNot (.bool value)) env kont)
      (.ret (.bool value) (.ifBranches (.bool false) (.bool true) env :: kont)) :=
    .tail (.tail .refl rfl) rfl
  exact ready.trans (boolNot_result_steps value)

/-- All four binary source definitions compute their truth tables in arbitrary continuations. -/
theorem boolBin_value_steps (operation : BoolBinOp) (left right : Bool) :
    Steps program (.eval (.boolBin operation (.bool left) (.bool right)) env kont)
      (.ret (.bool (operation.apply left right)) kont) := by
  have ready : Steps program (.eval (.boolBin operation (.bool left) (.bool right)) env kont)
      (.ret (.bool right) (.pairRight (.bool left) :: .splitBody operation.body env :: kont)) :=
    .tail (.tail (.tail (.tail (.tail .refl rfl) rfl) rfl) rfl) rfl
  exact ready.trans (boolBin_result_steps operation left right)

end LeanExe.TypeSafety
