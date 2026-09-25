import LeanExe.Source.ScalarHead
import LeanExe.Source.ScalarValues
import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar

/-! Semantics of concrete, elaborated Lean UInt64 syntax. The constants below
are paired explicitly with their native Lean definitions, independently of the
extractor's dispatch table and the IR operation selected by compilation.
The fragment covers pure arithmetic, UInt64 let bindings and comparison-based
conditionals and standard Id operations. Local unary functions capture their lexical environment. Iteration remains a separate obligation.
-/

def literalExpr (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
    (.app (.const ``UInt64.instOfNat []) (.lit (.natVal n)))

inductive EvalWith : Lean.Expr → List Value → UInt64 → Prop where
  | var (h : values[index]? = some (.word value)) : EvalWith (.bvar index) values value
  | literal : EvalWith (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
      values (UInt64.ofNat n)
  | ofNat : EvalWith (literalExpr n) values (UInt64.ofNat n)
  | binary (operation : Head head f) (left : EvalWith a values x) (right : EvalWith b values y) :
      EvalWith (.app (.app head a) b) values (f x y)
  | choose (op : Comparison) (type : ResultType) (left : EvalWith a values x) (right : EvalWith b values y)
      (branch : EvalWith (if op.denote x y then onTrue else onFalse) values value) :
      EvalWith (op.branch a b onTrue onFalse type) values value
  | letE (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (body : EvalWith e values value) : EvalWith (Identity.run e) values value
  | idPure (body : EvalWith e values value) : EvalWith (Identity.pure e) values value
  | idBind (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (Identity.bind name bi a b) values y
  | apply (function : values[index]? = some (.function false f)) (argument : EvalWith a values x) :
      EvalWith (.app (.bvar index) a) values (f x)
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : EvalWith b (.function false f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values value
  | unitApply (function : values[index]? = some (.function true f)) (argument : EvalWith a values x) :
      EvalWith (.app (.app (.bvar index) (.const ``Unit.unit [])) a) values (f x)
  | letUnitFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values) (f x))
      (body : EvalWith b (.function true f :: values) value) :
      EvalWith (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values value
  | metadata (body : EvalWith e values value) : EvalWith (.mdata data e) values value

/-- Syntactic support, defined without inspecting compiler output. -/
inductive SupportedWith : List BindingKind → Lean.Expr → Prop where
  | var (h : types[index]? = some .word) : SupportedWith types (.bvar index)
  | literal : SupportedWith types (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
  | ofNat : SupportedWith types (literalExpr n)
  | binary (operation : Head head f) (left : SupportedWith types a) (right : SupportedWith types b) :
      SupportedWith types (.app (.app head a) b)
  | choose (op : Comparison) (type : ResultType) (left : SupportedWith types a) (right : SupportedWith types b)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (op.branch a b t e type)
  | letE (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (body : SupportedWith types e) : SupportedWith types (Identity.run e)
  | idPure (body : SupportedWith types e) : SupportedWith types (Identity.pure e)
  | idBind (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (Identity.bind name bi a b)
  | apply (function : types[index]? = some (.function false)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.bvar index) a)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : SupportedWith (.function false :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | unitApply (function : types[index]? = some (.function true)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.app (.bvar index) (.const ``Unit.unit [])) a)
  | letUnitFn (type : ResultType) (function : SupportedWith (.word :: .unit :: types) a)
      (body : SupportedWith (.function true :: types) b) :
      SupportedWith types (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | metadata (body : SupportedWith types e) : SupportedWith types (.mdata data e)

theorem SupportedWith.evaluates {types : List BindingKind} {expr : Lean.Expr}
    (h : SupportedWith types expr) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ value, EvalWith expr values value := by
  classical
  induction h generalizing values with
  | var hi =>
    obtain ⟨value, hv⟩ := word_lookup typed hi
    exact ⟨value, .var hv⟩
  | literal => exact ⟨_, .literal⟩
  | ofNat => exact ⟨_, .ofNat⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    exact ⟨_, .binary op hx hy⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    cases flag : op.denote x y with
    | false =>
      obtain ⟨value, hv⟩ := ihe values typed
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values typed
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
  | letE _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values typed
    obtain ⟨y, hy⟩ := ihb (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .letE hx hy⟩
  | idRun _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idRun hv⟩
  | idPure _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idPure hv⟩
  | idBind _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values typed
    obtain ⟨y, hy⟩ := ihb (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .idBind hx hy⟩
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .apply hf hx⟩
  | letFn type _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
  | unitApply present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .unitApply hf hx⟩
  | letUnitFn type _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: .unit :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letUnitFn type (fun x => (total x).choose_spec) hv⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

/-- Public scalar entry semantics: parameters contain words; closures are internal. -/
abbrev Eval (expr : Lean.Expr) (values : List UInt64) (value : UInt64) : Prop :=
  EvalWith expr (values.map Value.word) value

/-- Public declarations begin with only word parameters. -/
abbrev Supported (arity : Nat) (expr : Lean.Expr) : Prop :=
  SupportedWith (List.replicate arity .word) expr

theorem Supported.evaluates {arity : Nat} {expr : Lean.Expr}
    (h : Supported arity expr) (values : List UInt64) (len : values.length = arity) :
    ∃ value, Eval expr values value := by
  apply SupportedWith.evaluates h
  simp [List.map_map, Function.comp_def, Value.kind, List.map_const', len]

end LeanExe.Source.Scalar
