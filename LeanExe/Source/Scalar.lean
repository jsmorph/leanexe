import LeanExe.Source.ScalarHead
import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar

/-! Semantics of concrete, elaborated Lean UInt64 syntax. The constants below
are paired explicitly with their native Lean definitions, independently of the
extractor's dispatch table and the IR operation selected by compilation.
The fragment covers pure arithmetic, UInt64 let bindings and comparison-based
conditionals and standard Id operations. Calls and iteration remain separate obligations.
-/

def literalExpr (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
    (.app (.const ``UInt64.instOfNat []) (.lit (.natVal n)))

inductive Eval : Lean.Expr → List UInt64 → UInt64 → Prop where
  | var (h : values[index]? = some value) : Eval (.bvar index) values value
  | literal : Eval (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
      values (UInt64.ofNat n)
  | ofNat : Eval (literalExpr n) values (UInt64.ofNat n)
  | binary (operation : Head head f) (left : Eval a values x) (right : Eval b values y) :
      Eval (.app (.app head a) b) values (f x y)
  | choose (op : Comparison) (type : ResultType) (left : Eval a values x) (right : Eval b values y)
      (branch : Eval (if op.denote x y then onTrue else onFalse) values value) :
      Eval (op.branch a b onTrue onFalse type) values value
  | letE (value : Eval a values x) (body : Eval b (x :: values) y) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (body : Eval e values value) : Eval (Identity.run e) values value
  | idPure (body : Eval e values value) : Eval (Identity.pure e) values value
  | idBind (value : Eval a values x) (body : Eval b (x :: values) y) :
      Eval (Identity.bind name bi a b) values y
  | metadata (body : Eval e values value) : Eval (.mdata data e) values value

/-- Syntactic support, defined without inspecting compiler output. -/
inductive Supported : Nat → Lean.Expr → Prop where
  | var (h : index < arity) : Supported arity (.bvar index)
  | literal : Supported arity (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
  | ofNat : Supported arity (literalExpr n)
  | binary (operation : Head head f) (left : Supported arity a) (right : Supported arity b) :
      Supported arity (.app (.app head a) b)
  | choose (op : Comparison) (type : ResultType) (left : Supported arity a) (right : Supported arity b)
      (onTrue : Supported arity t) (onFalse : Supported arity e) :
      Supported arity (op.branch a b t e type)
  | letE (value : Supported arity a) (body : Supported (arity + 1) b) :
      Supported arity (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (body : Supported arity e) : Supported arity (Identity.run e)
  | idPure (body : Supported arity e) : Supported arity (Identity.pure e)
  | idBind (value : Supported arity a) (body : Supported (arity + 1) b) :
      Supported arity (Identity.bind name bi a b)
  | metadata (body : Supported arity e) : Supported arity (.mdata data e)

theorem Supported.evaluates {arity : Nat} {expr : Lean.Expr}
    (h : Supported arity expr) (values : List UInt64) (len : values.length = arity) :
    ∃ value, Eval expr values value := by
  induction h generalizing values with
  | var hi =>
    rename_i index arity
    have hv : index < values.length := by omega
    exact ⟨values[index], .var (List.getElem?_eq_getElem hv)⟩
  | literal => exact ⟨_, .literal⟩
  | ofNat => exact ⟨_, .ofNat⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl values len
    obtain ⟨y, hy⟩ := ihr values len
    exact ⟨_, .binary op hx hy⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨x, hx⟩ := ihl values len
    obtain ⟨y, hy⟩ := ihr values len
    cases flag : op.denote x y with
    | false =>
      obtain ⟨value, hv⟩ := ihe values len
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values len
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
  | letE _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values len
    obtain ⟨y, hy⟩ := ihb (x :: values) (by simp [len])
    exact ⟨y, .letE hx hy⟩
  | idRun _ ih =>
    obtain ⟨value, hv⟩ := ih values len
    exact ⟨value, .idRun hv⟩
  | idPure _ ih =>
    obtain ⟨value, hv⟩ := ih values len
    exact ⟨value, .idPure hv⟩
  | idBind _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values len
    obtain ⟨y, hy⟩ := ihb (x :: values) (by simp [len])
    exact ⟨y, .idBind hx hy⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values len
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar
