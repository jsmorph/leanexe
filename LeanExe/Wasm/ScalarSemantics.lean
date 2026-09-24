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

mutual
  theorem Expr.ofIR_eval {expression : LeanExe.IR.Expr} {s next : LeanExe.IR.ScalarStore}
      {value : UInt64} (semantics : expression.ScalarEval s value next)
      {descriptor : Expr} (recognized : Expr.ofIR expression = some descriptor) :
      descriptor.eval s = some value ∧ next = s := by
    cases semantics with
    | «local» h =>
      simp only [Expr.ofIR, Option.some.injEq] at recognized
      subst descriptor
      exact ⟨h, rfl⟩
    | const =>
      simp only [Expr.ofIR, Option.some.injEq] at recognized
      subst descriptor
      exact ⟨rfl, rfl⟩
    | bin left right operation =>
      simp only [Expr.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨op, hop, a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hx, hs₁⟩ := Expr.ofIR_eval left ha
      obtain ⟨hy, hs₂⟩ := Expr.ofIR_eval right hb
      subst_vars
      rw [U64Op.ofIR_apply hop] at operation
      have hv := Option.some.inj operation
      exact ⟨by simp [Expr.eval, hx, hy, hv], rfl⟩
    | iteTrue condition branch =>
      simp only [Expr.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hv, hs₁⟩ := Cond.ofIR_eval condition hc
      obtain ⟨hr, hs₂⟩ := Expr.ofIR_eval branch ha
      subst_vars
      exact ⟨by simp [Expr.eval, hv, hr], rfl⟩
    | iteFalse condition branch =>
      simp only [Expr.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hv, hs₁⟩ := Cond.ofIR_eval condition hc
      obtain ⟨hr, hs₂⟩ := Expr.ofIR_eval branch hb
      subst_vars
      exact ⟨by simp [Expr.eval, hv, hr], rfl⟩
    | letE => simp [Expr.ofIR] at recognized
  termination_by sizeOf expression
  decreasing_by all_goals decreasing_tactic

  theorem Cond.ofIR_eval {condition : LeanExe.IR.Cond} {s next : LeanExe.IR.ScalarStore}
      {value : Bool} (semantics : condition.ScalarEval s value next)
      {descriptor : Cond} (recognized : Cond.ofIR condition = some descriptor) :
      descriptor.eval s = some value ∧ next = s := by
    cases semantics with
    | true =>
      simp only [Cond.ofIR, Option.some.injEq] at recognized
      subst descriptor
      exact ⟨rfl, rfl⟩
    | false =>
      simp only [Cond.ofIR, Option.some.injEq] at recognized
      subst descriptor
      exact ⟨rfl, rfl⟩
    | eq left right | lt left right | le left right =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hx, hs₁⟩ := Expr.ofIR_eval left ha
      obtain ⟨hy, hs₂⟩ := Expr.ofIR_eval right hb
      subst_vars
      exact ⟨by simp [Cond.eval, hx, hy], rfl⟩
    | not condition =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨c, hc, rfl⟩ := recognized
      obtain ⟨hv, hs⟩ := Cond.ofIR_eval condition hc
      subst_vars
      exact ⟨by simp [Cond.eval, hv], rfl⟩
    | andTrue left right | orFalse left right =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hx, hs₁⟩ := Cond.ofIR_eval left ha
      obtain ⟨hy, hs₂⟩ := Cond.ofIR_eval right hb
      subst_vars
      exact ⟨by simp [Cond.eval, hx, hy], rfl⟩
    | andFalse left | orTrue left =>
      simp only [Cond.ofIR, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at recognized
      obtain ⟨a, ha, b, hb, rfl⟩ := recognized
      obtain ⟨hx, hs⟩ := Cond.ofIR_eval left ha
      subst_vars
      exact ⟨by simp [Cond.eval, hx], rfl⟩
  termination_by sizeOf condition
  decreasing_by all_goals decreasing_tactic
end

end LeanExe.Wasm.ScalarDescriptor
