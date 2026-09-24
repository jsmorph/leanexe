import LeanExe.Wasm.ScalarDescriptor
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Wasm.ScalarDescriptor

def U64Op.apply : U64Op → UInt64 → UInt64 → UInt64
  | .add => UInt64.add
  | .sub => UInt64.sub
  | .mul => UInt64.mul
  | .divU => UInt64.div
  | .remU => UInt64.mod
  | .bitAnd => UInt64.land
  | .bitOr => UInt64.lor
  | .bitXor => UInt64.xor
  | .shiftLeft => UInt64.shiftLeft
  | .shiftRight => UInt64.shiftRight

theorem U64Op.ofIR_apply {operation : LeanExe.IR.U64Op} {descriptor : U64Op}
    (recognized : U64Op.ofIR operation = some descriptor) (x y : UInt64) :
    operation.evalScalar x y = some (descriptor.apply x y) := by
  cases operation <;> simp [U64Op.ofIR] at recognized <;>
    subst descriptor <;> rfl

mutual
  def Expr.eval (store : LeanExe.IR.ScalarStore) : Expr → Option UInt64
    | .get index => store[index]?
    | .const value => some (UInt64.ofNat value)
    | .bin op left right => do
      let x ← left.eval store
      let y ← right.eval store
      pure (op.apply x y)
    | .ite condition thenValue elseValue => do
      let c ← condition.eval store
      if c then thenValue.eval store else elseValue.eval store

  def Cond.eval (store : LeanExe.IR.ScalarStore) : Cond → Option Bool
    | .true => some true
    | .false => some false
    | .eq left right => do
      let x ← left.eval store
      let y ← right.eval store
      pure (x == y)
    | .ne left right => do
      let x ← left.eval store
      let y ← right.eval store
      pure (x != y)
    | .ltU left right => do
      let x ← left.eval store
      let y ← right.eval store
      pure (decide (x < y))
    | .leU left right => do
      let x ← left.eval store
      let y ← right.eval store
      pure (decide (x ≤ y))
    | .not condition => return !(← condition.eval store)
    | .and left right => do
      let x ← left.eval store
      if x then right.eval store else pure false
    | .or left right => do
      let x ← left.eval store
      if x then pure true else right.eval store
end

end LeanExe.Wasm.ScalarDescriptor
