import LeanExe.Source.ScalarUnit
import LeanExe.Source.ScalarHead
import LeanExe.Source.ScalarComplement
import LeanExe.Source.ScalarExtremum
import LeanExe.Source.ScalarValues
import LeanExe.Source.ScalarCompoundGuard
import LeanExe.Source.ScalarRangeSyntax

namespace LeanExe.Source.Scalar

/-! Semantics of concrete, elaborated Lean UInt64 syntax. The constants below
are paired explicitly with their native Lean definitions, independently of the
extractor's dispatch table and the IR operation selected by compilation.
The fragment covers pure arithmetic, UInt64 let bindings and comparison-based
conditionals and standard Id operations. Local functions with one or two UInt64 arguments capture their lexical environment. Iteration remains a separate obligation.
-/

def literalExpr (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
    (.app (.const ``UInt64.instOfNat []) (.lit (.natVal n)))

inductive EvalWith : Lean.Expr → List Value → UInt64 → Prop where
  | var (h : values[index]? = some (.word value)) : EvalWith (.bvar index) values value
  | natural (h : values[index]? = some (.natural value)) :
      EvalWith (.app (.const ``UInt64.ofNat levels) (.bvar index)) values (UInt64.ofNat value)
  | literal : EvalWith (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
      values (UInt64.ofNat n)
  | ofNat : EvalWith (literalExpr n) values (UInt64.ofNat n)
  | complement (head : ComplementHead operation) (argument : EvalWith a values x) :
      EvalWith (.app operation a) values (UInt64.complement x)
  | extremum (op : Extremum) (left : EvalWith a values x) (right : EvalWith b values y) :
      EvalWith (op.expr a b) values (op.denote x y)
  | binary (operation : Head head f) (left : EvalWith a values x) (right : EvalWith b values y) :
      EvalWith (.app (.app head a) b) values (f x y)
  | choose (op : Comparison) (type : ResultType) (left : EvalWith a values x) (right : EvalWith b values y)
      (branch : EvalWith (if op.denote x y then onTrue else onFalse) values value) :
      EvalWith (op.branch a b onTrue onFalse type) values value
  | chooseCompound (guard : CompoundGuard) (type : ResultType) {native : Lean.Expr → UInt64}
      (arguments : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression))
      (branch : EvalWith (if guard.denote native then onTrue else onFalse) values value) :
      EvalWith (guard.branch type.expr onTrue onFalse) values value
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
  | unitApply (unitForm : UnitSyntax) (function : values[index]? = some (.function true f)) (argument : EvalWith a values x) :
      EvalWith (.app (.app (.bvar index) unitForm.value) a) values (f x)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values) (f x))
      (body : EvalWith b (.function true f :: values) value) :
      EvalWith (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values value
  | binaryApply (function : values[index]? = some (.binaryFunction f))
      (first : EvalWith a values x) (second : EvalWith b values y) :
      EvalWith (.app (.app (.bvar index) a) b) values (f x y)
  | letBinaryFn (type : ResultType)
      (function : ∀ x y, EvalWith a (.word y :: .word x :: values) (f x y))
      (body : EvalWith b (.binaryFunction f :: values) value) :
      EvalWith (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values value
  | range (countValue : EvalWith count values stop) (initialValue : EvalWith initial values start)
      (yielding : Range.YieldScalar stepBody scalarBody)
      (steps : ∀ index value, EvalWith scalarBody (.word value :: .natural index :: values) (step index value)) :
      EvalWith (Range.call count initial indexName accumulatorName indexBi accumulatorBi stepBody)
        values (Range.iterate step stop.toNat 0 start)
  | metadata (body : EvalWith e values value) : EvalWith (.mdata data e) values value

/-- Syntactic support, defined without inspecting compiler output. -/
inductive SupportedWith : List BindingKind → Lean.Expr → Prop where
  | var (h : types[index]? = some .word) : SupportedWith types (.bvar index)
  | natural (h : types[index]? = some .natural) :
      SupportedWith types (.app (.const ``UInt64.ofNat levels) (.bvar index))
  | literal : SupportedWith types (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
  | ofNat : SupportedWith types (literalExpr n)
  | complement (head : ComplementHead operation) (argument : SupportedWith types a) :
      SupportedWith types (.app operation a)
  | extremum (op : Extremum) (left : SupportedWith types a) (right : SupportedWith types b) :
      SupportedWith types (op.expr a b)
  | binary (operation : Head head f) (left : SupportedWith types a) (right : SupportedWith types b) :
      SupportedWith types (.app (.app head a) b)
  | choose (op : Comparison) (type : ResultType) (left : SupportedWith types a) (right : SupportedWith types b)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (op.branch a b t e type)
  | chooseCompound (guard : CompoundGuard) (type : ResultType)
      (arguments : ∀ expression, expression ∈ guard.operands → SupportedWith types expression)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (guard.branch type.expr t e)
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
  | unitApply (unitForm : UnitSyntax) (function : types[index]? = some (.function true)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.app (.bvar index) unitForm.value) a)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax) (function : SupportedWith (.word :: .unit :: types) a)
      (body : SupportedWith (.function true :: types) b) :
      SupportedWith types (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | binaryApply (function : types[index]? = some .binaryFunction)
      (first : SupportedWith types a) (second : SupportedWith types b) :
      SupportedWith types (.app (.app (.bvar index) a) b)
  | letBinaryFn (type : ResultType) (function : SupportedWith (.word :: .word :: types) a)
      (body : SupportedWith (.binaryFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | metadata (body : SupportedWith types e) : SupportedWith types (.mdata data e)

theorem SupportedWith.evaluates {types : List BindingKind} {expr : Lean.Expr}
    (h : SupportedWith types expr) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ value, EvalWith expr values value := by
  classical
  induction h generalizing values with
  | var hi =>
    obtain ⟨value, hv⟩ := word_lookup typed hi
    exact ⟨value, .var hv⟩
  | natural hi =>
    obtain ⟨value, hv⟩ := natural_lookup typed hi
    exact ⟨UInt64.ofNat value, .natural hv⟩
  | literal => exact ⟨_, .literal⟩
  | ofNat => exact ⟨_, .ofNat⟩
  | complement head _ ih =>
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨UInt64.complement x, .complement head hx⟩
  | extremum op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    exact ⟨op.denote x y, .extremum op hx hy⟩
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
  | chooseCompound guard type _ _ _ ihArgs iht ihe =>
    let native : Lean.Expr → UInt64 := fun expression =>
      if member : expression ∈ guard.operands then (ihArgs expression member values typed).choose else 0
    have meanings : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression) := by
      intro expression member
      simpa [native, member] using (ihArgs expression member values typed).choose_spec
    cases flag : guard.denote native with
    | false =>
      obtain ⟨value, hv⟩ := ihe values typed
      exact ⟨value, .chooseCompound guard type meanings (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values typed
      exact ⟨value, .chooseCompound guard type meanings (by simpa [flag] using hv)⟩
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
  | unitApply unitForm present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .unitApply unitForm hf hx⟩
  | letUnitFn type unitForm _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: .unit :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letUnitFn type unitForm (fun x => (total x).choose_spec) hv⟩
  | binaryApply present _ _ ihFirst ihSecond =>
    obtain ⟨f, hf⟩ := binaryFunction_lookup typed present
    obtain ⟨x, hx⟩ := ihFirst values typed
    obtain ⟨y, hy⟩ := ihSecond values typed
    exact ⟨f x y, .binaryApply hf hx hy⟩
  | letBinaryFn type _ _ ihf ihb =>
    have total := fun x y => ihf (.word y :: .word x :: values) (by simp [Value.kind, typed])
    let f := fun x y => (total x y).choose
    obtain ⟨value, hv⟩ := ihb (.binaryFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBinaryFn type (fun x y => (total x y).choose_spec) hv⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

theorem EvalWith.not_unit {expression values value} (evaluated : EvalWith expression values value) (unitForm : UnitSyntax) :
    expression ≠ unitForm.value := by
  intro same
  subst expression
  cases unitForm <;> cases evaluated

theorem SupportedWith.not_unit {types expression} (supported : SupportedWith types expression) (unitForm : UnitSyntax) :
    expression ≠ unitForm.value := by
  intro same
  subst expression
  cases unitForm <;> cases supported

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
