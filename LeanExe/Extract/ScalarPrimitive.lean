import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

/-- The concrete UInt64 primitives handled by the production extractor. -/
inductive ScalarPrimitive where
  | add | sub | mul | div | mod | land | lor | xor | shiftLeft | shiftRight
  deriving BEq, DecidableEq, Repr

namespace ScalarPrimitive

def all : List ScalarPrimitive :=
  [.add, .sub, .mul, .div, .mod, .land, .lor, .xor, .shiftLeft, .shiftRight]

def name : ScalarPrimitive → Lean.Name
  | .add => ``UInt64.add
  | .sub => ``UInt64.sub
  | .mul => ``UInt64.mul
  | .div => ``UInt64.div
  | .mod => ``UInt64.mod
  | .land => ``UInt64.land
  | .lor => ``UInt64.lor
  | .xor => ``UInt64.xor
  | .shiftLeft => ``UInt64.shiftLeft
  | .shiftRight => ``UInt64.shiftRight

/-- The source meanings are Lean's own UInt64 definitions. -/
def denote : ScalarPrimitive → UInt64 → UInt64 → UInt64
  | .add => UInt64.add
  | .sub => UInt64.sub
  | .mul => UInt64.mul
  | .div => UInt64.div
  | .mod => UInt64.mod
  | .land => UInt64.land
  | .lor => UInt64.lor
  | .xor => UInt64.xor
  | .shiftLeft => UInt64.shiftLeft
  | .shiftRight => UInt64.shiftRight

def toIR : ScalarPrimitive → LeanExe.IR.U64Op
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .divU
  | .mod => .modU
  | .land => .bitAnd
  | .lor => .bitOr
  | .xor => .bitXor
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight

def ofName? (n : Lean.Name) : Option ScalarPrimitive :=
  all.find? (fun p => p.name == n)

@[simp] theorem ofName_name (p : ScalarPrimitive) : ofName? p.name = some p := by
  cases p <;> decide

theorem ofName_sound {n : Lean.Name} {p : ScalarPrimitive}
    (h : ofName? n = some p) : p.name = n := by
  have := List.find?_some h
  simpa using this

def lower (p : ScalarPrimitive) (left right : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  .u64Bin p.toIR left right

@[simp] theorem denote_toIR (p : ScalarPrimitive) (x y : UInt64) :
    p.toIR.evalScalar x y = some (p.denote x y) := by
  cases p <;> rfl

/-- Every direct primitive lowering preserves the original Lean operation. -/
theorem lower_correct (p : ScalarPrimitive)
    {a b : LeanExe.IR.Expr} {s s₁ s₂ : LeanExe.IR.ScalarStore} {x y : UInt64}
    (left : a.ScalarEval s x s₁) (right : b.ScalarEval s₁ y s₂) :
    (p.lower a b).ScalarEval s (p.denote x y) s₂ :=
  .bin left right (p.denote_toIR x y)

end ScalarPrimitive
end LeanExe.Extract.Core
