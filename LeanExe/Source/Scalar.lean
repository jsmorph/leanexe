import Lean

namespace LeanExe.Source.Scalar

/-! Semantics of concrete, elaborated Lean UInt64 syntax. The constants below
are paired explicitly with their native Lean definitions, independently of the
extractor's dispatch table and the IR operation selected by compilation.
This initial fragment covers primitive expression trees; binders, conditions,
declarations, calls, and iteration remain separate obligations.
-/

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

inductive Eval : Lean.Expr → List UInt64 → UInt64 → Prop where
  | var (h : values[index]? = some value) : Eval (.bvar index) values value
  | literal : Eval (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
      values (UInt64.ofNat n)
  | binary (operation : Binary name f) (left : Eval a values x) (right : Eval b values y) :
      Eval (.app (.app (.const name levels) a) b) values (f x y)
  | metadata (body : Eval e values value) : Eval (.mdata data e) values value

/-- Syntactic support, defined without inspecting compiler output. -/
inductive Supported : Nat → Lean.Expr → Prop where
  | var (h : index < arity) : Supported arity (.bvar index)
  | literal : Supported arity (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
  | binary (operation : Binary name f) (left : Supported arity a) (right : Supported arity b) :
      Supported arity (.app (.app (.const name levels) a) b)
  | metadata (body : Supported arity e) : Supported arity (.mdata data e)

theorem Supported.evaluates {arity : Nat} {expr : Lean.Expr}
    (h : Supported arity expr) (values : List UInt64) (len : values.length = arity) :
    ∃ value, Eval expr values value := by
  induction h with
  | var hi =>
    rename_i index arity
    have hv : index < values.length := by omega
    exact ⟨values[index], .var (List.getElem?_eq_getElem hv)⟩
  | literal => exact ⟨_, .literal⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl len
    obtain ⟨y, hy⟩ := ihr len
    exact ⟨_, .binary op hx hy⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih len
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar
