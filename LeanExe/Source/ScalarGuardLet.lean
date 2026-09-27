import LeanExe.Source.ScalarPublicArgument
import LeanExe.Source.ScalarBooleanLet
import LeanExe.Source.ScalarGuardLiteral
import LeanExe.Source.ScalarSavedBooleanGuard

namespace LeanExe.Source.Scalar

/-- Extra syntax for Boolean relation operands and unused predicate validation. -/
noncomputable def guardOperandOverhead : Nat :=
  max (sizeOf (.const ``Bool.toUInt64 [] : Lean.Expr) -
    sizeOf (.const ``Bool [] : Lean.Expr) - sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) + 1)
    (sizeOf (Lean.Expr.app (.const ``UInt64.ofNat []) (.lit (.natVal 0))) -
      sizeOf (.const ``True [] : Lean.Expr) + 1)

theorem guardOperandOverhead_ite : guardOperandOverhead ≤ sizeOf ("ite" : String) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
theorem guardOperandOverhead_dite : guardOperandOverhead ≤ sizeOf ("dite" : String) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
theorem guardOperandOverhead_ite_word : guardOperandOverhead ≤
    sizeOf ("ite" : String) + sizeOf (.const ``UInt64 [] : Lean.Expr) := by decide
theorem guardOperandOverhead_dite_word : guardOperandOverhead ≤
    sizeOf ("dite" : String) + sizeOf (.const ``UInt64 [] : Lean.Expr) := by decide
theorem guardOperandOverhead_decide : guardOperandOverhead ≤ sizeOf ("decide" : String) := by decide

theorem guardOperandOverhead_predicate :
    sizeOf (Lean.Expr.app (.const ``UInt64.ofNat []) (.lit (.natVal 0))) <
      sizeOf (.const ``True [] : Lean.Expr) + guardOperandOverhead := by decide

theorem booleanTruth_min_size (value : Lean.Expr) :
    sizeOf (.const ``True [] : Lean.Expr) ≤
      sizeOf (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value)
        (.const ``Bool.true []) : Lean.Expr) := by
  have heads : sizeOf (.const ``True [] : Lean.Expr) ≤
      sizeOf (.const ``Eq [.succ .zero] : Lean.Expr) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
  simp at *; omega

theorem BooleanGuard.condition_min_size (guard : BooleanGuard) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf guard.condition :=
  booleanTruth_min_size guard.expr

theorem SavedBooleanGuard.condition_min_size (guard : SavedBooleanGuard) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf guard.condition :=
  booleanTruth_min_size guard.expr

theorem Comparison.condition_min_size (op : Comparison) (left right : Lean.Expr) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf (op.condition left right) := by
  induction op with
  | eq type | ne type | lt type | le type | gt type | ge type =>
    have base := type.word_size
    have named : sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf (.const ``UInt64 [] : Lean.Expr) := by decide
    simp [condition, ResultType.expr] at *
    omega
  | beq | bne =>
    have named : sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf (.const ``UInt64 [] : Lean.Expr) := by decide
    simp [condition, boolExpr] at *
    omega
  | boolNot op => exact (BooleanGuard.compare (.negate op) left right).condition_min_size
  | negate op ih => simp [condition] at *; omega

theorem GuardLiteral.condition_min_size (guard : GuardLiteral) :
    sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf guard.condition := by
  cases guard with
  | proposition n value =>
    apply Nat.le_trans _ (GuardNegation.condition_size n _)
    cases value <;> decide
  | boolean m n value =>
    exact Nat.le_trans (BooleanGuard.literal n value).condition_min_size (GuardNegation.condition_size m _)

inductive GuardLetType where
  | boolean (type : BooleanType)
  | word (type : ResultType)
  | predicate (booleanInput : Bool) (inputName : Lean.Name) (info : Lean.BinderInfo) (result : BooleanType)
  | predicateId (kind : PublicArgument) (domain : Lean.Expr) (input : PublicArgument.Domain kind domain)
      (inputName : Lean.Name) (info : Lean.BinderInfo) (result : BooleanType)
  deriving Repr

def GuardLetType.expr : GuardLetType → Lean.Expr
  | .boolean type => type.expr
  | .word type => type.expr
  | .predicate booleanInput inputName info result =>
      .forallE inputName (if booleanInput then .const ``Bool [] else .const ``UInt64 []) result.expr info
  | .predicateId _ domain _ inputName info result =>
      .forallE inputName (.app (.const ``Id [.zero]) domain) result.expr info

/-- A let binding retained in a proposition and in each checked operand. -/
structure GuardLet where
  name : Lean.Name
  type : GuardLetType
  value : Lean.Expr
  nondep : Bool
  deriving Repr

namespace GuardLet

def wrap (binding : GuardLet) (body : Lean.Expr) : Lean.Expr :=
  .letE binding.name binding.type.expr binding.value body binding.nondep

def operand (binding : GuardLet) : Lean.Expr :=
  match binding.type with
  | .boolean _ => .app (.const ``Bool.toUInt64 []) binding.value
  | .word _ => binding.value
  | .predicate .. | .predicateId .. => binding.wrap (.app (.const ``UInt64.ofNat []) (.lit (.natVal 0)))

def evidence (binding : GuardLet) (body : Lean.Expr) : Lean.Expr :=
  body.instantiate1 binding.value

theorem wrap_size (binding : GuardLet) {operand condition : Lean.Expr}
    (smaller : sizeOf operand < sizeOf condition) :
    sizeOf (binding.wrap operand) < sizeOf (binding.wrap condition) := by
  simp [wrap]; omega

theorem operand_size (binding : GuardLet) (condition : Lean.Expr)
    (conditionSize : sizeOf (.const ``True [] : Lean.Expr) ≤ sizeOf condition) :
    sizeOf binding.operand < sizeOf (binding.wrap condition) + guardOperandOverhead := by
  obtain ⟨name, type, value, nondep⟩ := binding
  cases type with
  | word type => simp [operand, wrap]; omega
  | boolean type =>
    have base := type.base_size
    have constants : sizeOf (.const ``Bool.toUInt64 [] : Lean.Expr) <
        sizeOf (.const ``Bool [] : Lean.Expr) + sizeOf (.const ``True [] : Lean.Expr) + guardOperandOverhead := by decide
    simp [operand, wrap, GuardLetType.expr, BooleanType.expr] at *
    omega
  | predicate booleanInput inputName info result | predicateId kind domain input inputName info result =>
    have constants := guardOperandOverhead_predicate
    simp [operand, wrap] at *
    omega

end GuardLet
end LeanExe.Source.Scalar
