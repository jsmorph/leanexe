import LeanExe.Extract.ScalarHead
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

/-- Compile pure, total scalar expressions with an environment of already
compiled bindings. Substitution removes source lets without introducing effects.
Bindings may be duplicated or unused in the output; this is valid only for this
pure arithmetic fragment. The source semantics still evaluates each binding. -/
def extractScalarExprWith (locals : List LeanExe.IR.Expr) : Lean.Expr → Option LeanExe.IR.Expr
  | .bvar index => locals[index]?
  | .app (.const ``UInt64.ofNat _) (.lit (.natVal n)) => some (.u64 n)
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
      (.app (.const ``UInt64.instOfNat []) (.lit (.natVal m))) =>
      if n == m then some (.u64 n) else none
  | .app (.app head left) right => do
      let op ← ScalarPrimitive.ofHead? head
      let a ← extractScalarExprWith locals left
      let b ← extractScalarExprWith locals right
      pure (op.lower a b)
  | .letE _ (.const ``UInt64 []) value body _ => do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (bound :: locals) body
  | .mdata _ body => extractScalarExprWith locals body
  | _ => none

/-- Source argument indices map to the production IR's materialized slots. -/
def extractScalarExpr (locals : List Nat) (source : Lean.Expr) : Option LeanExe.IR.Expr :=
  extractScalarExprWith (locals.map LeanExe.IR.Expr.local) source

theorem extractScalarExprWith_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List LeanExe.IR.Expr) (a b : Lean.Expr) :
    extractScalarExprWith locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      pure (p.lower left right)) := by
  cases h with
  | direct op => cases op <;> rfl
  | canonical op => cases op <;> rfl

@[simp] theorem extractScalarExprWith_literalExpr (locals : List LeanExe.IR.Expr) (n : Nat) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) := by
  simp [extractScalarExprWith, LeanExe.Source.Scalar.literalExpr]

theorem extractScalarExpr_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List Nat) (a b : Lean.Expr) :
    extractScalarExpr locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExpr locals a
      let right ← extractScalarExpr locals b
      pure (p.lower left right)) :=
  extractScalarExprWith_binary h _ a b

@[simp] theorem extractScalarExpr_literalExpr (locals : List Nat) (n : Nat) :
    extractScalarExpr locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) :=
  extractScalarExprWith_literalExpr _ n

/-- Existing slots contain the values of the corresponding source binders. -/
def ScalarLocalsMatch (locals : List Nat) (values : List UInt64)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index slot : Nat), locals[index]? = some slot → store[slot]? = values[index]?

/-- Symbolic bindings denote source values without changing the input store. -/
def ScalarBindingsMatch (locals : List LeanExe.IR.Expr) (values : List UInt64)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index : Nat) (target : LeanExe.IR.Expr) (value : UInt64), locals[index]? = some target → values[index]? = some value →
    target.ScalarEval store value store

theorem extractScalarExprWith_correct {source : Lean.Expr} {values : List UInt64} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval source values value)
    {locals : List LeanExe.IR.Expr} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ScalarBindingsMatch locals values store) :
    target.ScalarEval store value store := by
  induction semantics generalizing locals target with
  | var h => exact bindings _ _ _ compiled h
  | literal => cases compiled; exact .const
  | ofNat =>
    simp only [extractScalarExprWith_literalExpr, Option.some.injEq] at compiled
    subst target
    exact .const
  | @binary head f a values x b y op left right ihl ihr =>
    rw [extractScalarExprWith_binary op] at compiled
    obtain ⟨p, hp, hf⟩ := sourceHead_recognized op
    cases ha : extractScalarExprWith locals a with
    | none => simp [hp, ha] at compiled
    | some aIR =>
      cases hb : extractScalarExprWith locals b with
      | none => simp [hp, ha, hb] at compiled
      | some bIR =>
        have heq : p.lower aIR bIR = target := by simpa [hp, ha, hb] using compiled
        subst target
        rw [← hf]
        exact p.lower_correct (ihl ha bindings) (ihr hb bindings)
  | letE value body ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    apply ihb hc
    intro index expression result he hv
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he hv
      subst expression
      subst result
      exact ihv hb bindings
    | succ index => exact bindings index expression result he hv
  | metadata _ ih => exact ih compiled bindings

/-- General preservation for the production expression traversal. -/
theorem extractScalarExpr_correct {source : Lean.Expr} {values : List UInt64} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval source values value)
    {locals : List Nat} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExpr locals source = some target)
    (bindings : ScalarLocalsMatch locals values store) :
    target.ScalarEval store value store := by
  apply extractScalarExprWith_correct semantics compiled
  intro index expression result he hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he
  obtain ⟨slot, hs, rfl⟩ := he
  exact .local ((bindings _ _ hs).trans hv)

theorem extractScalarExprWith_accepts {source : Lean.Expr} {arity : Nat}
    (supported : LeanExe.Source.Scalar.Supported arity source)
    (locals : List LeanExe.IR.Expr) (len : locals.length = arity) :
    ∃ target, extractScalarExprWith locals source = some target := by
  induction supported generalizing locals with
  | var hi =>
    rename_i index arity
    have hv : index < locals.length := by omega
    exact ⟨locals[index], by simp [extractScalarExprWith, List.getElem?_eq_getElem hv]⟩
  | literal => exact ⟨.u64 _, rfl⟩
  | ofNat => exact ⟨.u64 _, extractScalarExprWith_literalExpr _ _⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceHead_recognized op
    obtain ⟨a, ha⟩ := ihl locals len
    obtain ⟨b, hb⟩ := ihr locals len
    exact ⟨p.lower a b, by rw [extractScalarExprWith_binary op]; simp [hp, ha, hb]⟩
  | letE _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals len
    obtain ⟨target, ht⟩ := ihb (bound :: locals) (by simp [len])
    exact ⟨target, by simp [extractScalarExprWith, hb, ht]⟩
  | metadata _ ih => exact ih locals len

theorem extractScalarExpr_accepts {source : Lean.Expr} {arity : Nat}
    (supported : LeanExe.Source.Scalar.Supported arity source)
    (locals : List Nat) (len : locals.length = arity) :
    ∃ target, extractScalarExpr locals source = some target :=
  extractScalarExprWith_accepts supported _ (by simpa using len)

/-- Success admits only the independently specified source grammar. -/
theorem extractScalarExprWith_supported {source : Lean.Expr} {locals : List LeanExe.IR.Expr}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExprWith locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  induction locals, source using extractScalarExprWith.induct generalizing target with
  | case1 locals index => exact .var (List.getElem?_eq_some_iff.mp compiled).1
  | case2 => exact .literal
  | case3 locals n m heq =>
    have h : n = m := by simpa using heq
    subst m
    exact .ofNat
  | case4 locals n m hne => simp [extractScalarExprWith, hne] at compiled
  | case5 locals head left right excluded ihl ihr =>
    cases hp : ScalarPrimitive.ofHead? head with
    | none =>
      simp only [extractScalarExprWith] at compiled
      simp [hp] at compiled
    | some p =>
      have meaning := ScalarPrimitive.ofHead_sound hp
      rw [extractScalarExprWith_binary meaning] at compiled
      cases ha : extractScalarExprWith locals left with
      | none => simp [hp, ha] at compiled
      | some a =>
        cases hb : extractScalarExprWith locals right with
        | none => simp [hp, ha, hb] at compiled
        | some b => exact .binary meaning (ihl ha) (ihr hb)
  | case6 locals name value body nondep ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (ihv hb) (by simpa using ihb bound ht)
  | case7 locals data body ih => exact .metadata (ih compiled)
  | case8 locals expr hvar hliteral hofNat hbin hlet hmetadata =>
    unfold extractScalarExprWith at compiled
    split at compiled <;> simp_all
    all_goals first
      | exact (hbin _ _ _ rfl rfl rfl).elim
      | exact (hofNat _ _ rfl rfl).elim
      | (have ht := (hlet _ _ _).1 rfl rfl rfl
         have hf := (hlet _ _ _).2 rfl rfl rfl
         simp_all)

theorem extractScalarExpr_supported {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  simpa using extractScalarExprWith_supported compiled

/-- A reusable closure property for the unchanged arithmetic backend. -/
theorem extractScalarExprWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    {source : Lean.Expr} {locals : List LeanExe.IR.Expr} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ∀ expression ∈ locals, P expression) : P target := by
  have supported := extractScalarExprWith_supported compiled
  generalize hlen : locals.length = arity at supported
  induction supported generalizing locals target with
  | var hi => exact bindings target (List.mem_of_getElem? compiled)
  | literal => cases compiled; exact literal _
  | ofNat =>
    simp only [extractScalarExprWith_literalExpr, Option.some.injEq] at compiled
    subst target
    exact literal _
  | binary op _ _ ihl ihr =>
    rw [extractScalarExprWith_binary op] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := compiled
    exact binary p a b (ihl ha bindings hlen) (ihr hb bindings hlen)
  | letE _ _ ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [hlen])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings hlen
    · exact bindings expression member
  | metadata _ ih => exact ih compiled bindings hlen

/-- Source support guarantees both admission and source/IR agreement. -/
theorem extractScalarExpr_total_correct {source : Lean.Expr} {locals : List Nat}
    (supported : LeanExe.Source.Scalar.Supported locals.length source)
    (values : List UInt64) (store : LeanExe.IR.ScalarStore)
    (len : values.length = locals.length)
    (bindings : ScalarLocalsMatch locals values store) :
    ∃ target value, extractScalarExpr locals source = some target ∧
      LeanExe.Source.Scalar.Eval source values value ∧ target.ScalarEval store value store := by
  obtain ⟨target, compiled⟩ := extractScalarExpr_accepts supported locals rfl
  obtain ⟨value, semantics⟩ := supported.evaluates values len
  exact ⟨target, value, compiled, semantics, extractScalarExpr_correct semantics compiled bindings⟩

end LeanExe.Extract.Core
