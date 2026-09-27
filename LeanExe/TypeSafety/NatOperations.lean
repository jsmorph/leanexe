import LeanExe.TypeSafety.Formation

/-!
# Independent bounded-natural primitives

Operations are defined over mathematical naturals. Addition and multiplication
check representability; subtraction saturates, division by zero yields zero,
and remainder by zero yields the dividend. Raw computation takes no typing
proofs. The separate outcome theorem assumes represented operands.
-/

namespace LeanExe.TypeSafety

/-- The exclusive upper bound on a represented natural number. -/
def nat64Limit : Nat := 2 ^ 64

inductive NatBinOp where
  | add | sub | mul | div | mod | min | max
  deriving DecidableEq, Repr

inductive NatCmpOp where
  | eq | lt | le
  deriving DecidableEq, Repr

inductive NatOverflowOp where
  | add | mul
  deriving DecidableEq, Repr

def NatBinOp.apply : NatBinOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .min, a, b => Nat.min a b
  | .max, a, b => Nat.max a b

def NatCmpOp.apply : NatCmpOp → Nat → Nat → Bool
  | .eq, a, b => decide (a = b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

def NatOverflowOp.apply : NatOverflowOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .mul, a, b => a * b

def NatOverflowOp.toBinOp : NatOverflowOp → NatBinOp
  | .add => .add
  | .mul => .mul

/-- The only permitted arithmetic failures, stated independently of evaluation. -/
def Overflow (operation : NatOverflowOp) (left right : Nat) : Prop :=
  left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ operation.apply left right

inductive NatResult where
  | value (result : Nat)
  | overflow (operation : NatOverflowOp)
  deriving DecidableEq, Repr

def evalNatBin : NatBinOp → Nat → Nat → NatResult
  | .add, a, b => if a + b < nat64Limit then .value (a + b) else .overflow .add
  | .mul, a, b => if a * b < nat64Limit then .value (a * b) else .overflow .mul
  | .sub, a, b => .value (a - b)
  | .div, a, b => .value (a / b)
  | .mod, a, b => .value (a % b)
  | .min, a, b => .value (min a b)
  | .max, a, b => .value (max a b)

theorem evalNatBin_value_iff : evalNatBin operation left right = .value result ↔
    result = operation.apply left right ∧
      ((operation = .add ∨ operation = .mul) → result < nat64Limit) := by
  cases operation <;> simp [evalNatBin, NatBinOp.apply, eq_comm]
  all_goals split <;> simp_all [eq_comm]

theorem evalNatBin_overflow_iff : evalNatBin operation left right = .overflow fault ↔
    operation = fault.toBinOp ∧ nat64Limit ≤ fault.apply left right := by
  cases operation <;> cases fault <;> simp [evalNatBin, NatOverflowOp.toBinOp, NatOverflowOp.apply]
  all_goals split <;> simp_all [Nat.not_lt]

theorem evalNatBin_no_overflow (notAdd : operation ≠ NatBinOp.add)
    (notMul : operation ≠ NatBinOp.mul) : evalNatBin operation left right ≠ .overflow fault := by
  intro overflowed
  have same := (evalNatBin_overflow_iff.mp overflowed).1
  cases fault with
  | add => exact notAdd same
  | mul => exact notMul same

/-- Represented inputs produce a represented result or precisely justified overflow. -/
theorem evalNatBin_bounded (leftBound : left < nat64Limit) (rightBound : right < nat64Limit) :
    match evalNatBin operation left right with
    | .value result => result < nat64Limit
    | .overflow fault => Overflow fault left right := by
  cases operation with
  | add =>
      by_cases bounded : left + right < nat64Limit
      · simp [evalNatBin, bounded]
      · simpa [evalNatBin, bounded, Overflow, NatOverflowOp.apply] using
          And.intro leftBound (And.intro rightBound (Nat.le_of_not_lt bounded))
  | mul =>
      by_cases bounded : left * right < nat64Limit
      · simp [evalNatBin, bounded]
      · simpa [evalNatBin, bounded, Overflow, NatOverflowOp.apply] using
          And.intro leftBound (And.intro rightBound (Nat.le_of_not_lt bounded))
  | sub => exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) leftBound
  | div => exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound
  | mod =>
      cases right with
      | zero => simpa [evalNatBin] using leftBound
      | succ right => exact Nat.lt_trans (Nat.mod_lt _ (Nat.zero_lt_succ _)) rightBound
  | min => exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) leftBound
  | max => exact Nat.max_lt.mpr ⟨leftBound, rightBound⟩

theorem evalNatBin_sub_saturates (ordered : left ≤ right) :
    evalNatBin .sub left right = .value 0 := by
  simp [evalNatBin, Nat.sub_eq_zero_of_le ordered]

theorem evalNatBin_div_zero : evalNatBin .div left 0 = .value 0 := by
  simp [evalNatBin]

theorem evalNatBin_mod_zero : evalNatBin .mod left 0 = .value left := by
  simp [evalNatBin]

theorem NatCmpOp.eq_iff : NatCmpOp.eq.apply left right = true ↔ left = right := by
  simp [NatCmpOp.apply]

theorem NatCmpOp.lt_iff : NatCmpOp.lt.apply left right = true ↔ left < right := by
  simp [NatCmpOp.apply]

theorem NatCmpOp.le_iff : NatCmpOp.le.apply left right = true ↔ left ≤ right := by
  simp [NatCmpOp.apply]

end LeanExe.TypeSafety
