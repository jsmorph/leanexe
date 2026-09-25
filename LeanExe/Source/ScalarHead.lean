import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

inductive Binary : Lean.Name → (UInt64 → UInt64 → UInt64) → Prop where
  | add : Binary ``UInt64.add UInt64.add
  | sub : Binary ``UInt64.sub UInt64.sub
  | mul : Binary ``UInt64.mul UInt64.mul
  | div : Binary ``UInt64.div UInt64.div
  | mod : Binary ``UInt64.mod UInt64.mod
  | land : Binary ``UInt64.land UInt64.land
  | lor : Binary ``UInt64.lor UInt64.lor
  | xor : Binary ``UInt64.xor UInt64.xor
  | shiftLeft : Binary ``UInt64.shiftLeft UInt64.shiftLeft
  | shiftRight : Binary ``UInt64.shiftRight UInt64.shiftRight

/-- The exact canonical class applications produced by Lean elaboration. -/
inductive ClassBinary : (Lean.Name × Lean.Name × Lean.Name) →
    (UInt64 → UInt64 → UInt64) → Prop where
  | add : ClassBinary (``HAdd.hAdd, ``instHAdd, ``instAddUInt64) UInt64.add
  | sub : ClassBinary (``HSub.hSub, ``instHSub, ``instSubUInt64) UInt64.sub
  | mul : ClassBinary (``HMul.hMul, ``instHMul, ``instMulUInt64) UInt64.mul
  | div : ClassBinary (``HDiv.hDiv, ``instHDiv, ``instDivUInt64) UInt64.div
  | mod : ClassBinary (``HMod.hMod, ``instHMod, ``instModUInt64) UInt64.mod
  | land : ClassBinary (``HAnd.hAnd, ``instHAndOfAndOp, ``instAndOpUInt64) UInt64.land
  | lor : ClassBinary (``HOr.hOr, ``instHOrOfOrOp, ``instOrOpUInt64) UInt64.lor
  | xor : ClassBinary (``HXor.hXor, ``instHXorOfXorOp, ``instXorOpUInt64) UInt64.xor
  | shiftLeft : ClassBinary
      (``HShiftLeft.hShiftLeft, ``instHShiftLeftOfShiftLeft, ``instShiftLeftUInt64) UInt64.shiftLeft
  | shiftRight : ClassBinary
      (``HShiftRight.hShiftRight, ``instHShiftRightOfShiftRight, ``instShiftRightUInt64) UInt64.shiftRight

def classHead (names : Lean.Name × Lean.Name × Lean.Name)
    (result : ResultType := .word) : Lean.Expr :=
  let type : Lean.Expr := .const ``UInt64 []
  .app (.app (.app (.app (.const names.1 [.zero, .zero, .zero]) type) type) result.expr)
    (.app (.app (.const names.2.1 [.zero]) type) (.const names.2.2 []))

inductive Head : Lean.Expr → (UInt64 → UInt64 → UInt64) → Prop where
  | direct (operation : Binary name f) : Head (.const name levels) f
  | canonical (operation : ClassBinary names f) (result : ResultType := .word) :
      Head (classHead names result) f

end LeanExe.Source.Scalar
