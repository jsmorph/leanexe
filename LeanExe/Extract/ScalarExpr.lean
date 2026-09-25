import LeanExe.Extract.ScalarHead
import LeanExe.Extract.ScalarDo
import LeanExe.Extract.ScalarComparison
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
  | .app (.app (.const ``Id.run [.zero]) (.const ``UInt64 [])) body =>
      extractScalarExprWith locals body
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) (.const ``UInt64 [])) body =>
      extractScalarExprWith locals body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) (.const ``UInt64 [])) (.const ``UInt64 [])) value)
      (.lam _ (.const ``UInt64 []) body _) => do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (bound :: locals) body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
      condition) evidence) onTrue) onFalse =>
      match scalarResultType? type with
      | none => none
      | some _ =>
        match _h : comparison? condition evidence with
        | none => none
        | some (op, left, right) => do
            let a ← extractScalarExprWith locals left
            let b ← extractScalarExprWith locals right
            let t ← extractScalarExprWith locals onTrue
            let e ← extractScalarExprWith locals onFalse
            pure (.ite (lowerComparison op a b) t e)
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
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have bounds := comparison_size _h; omega)

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
  | direct op => cases op <;> rw [extractScalarExprWith] <;> simp
  | canonical op => cases op <;> dsimp only [LeanExe.Source.Scalar.classHead] <;> rw [extractScalarExprWith] <;> simp

theorem extractScalarExprWith_branch (op : LeanExe.Source.Scalar.Comparison)
    (locals : List LeanExe.IR.Expr) (a b t e : Lean.Expr) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (op.branch a b t e type) = (do
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite (lowerComparison op left right) onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.Comparison.branch, extractScalarExprWith]
  rw [scalarResultType_accepts, comparison_accepts]

@[simp] theorem extractScalarExprWith_idRun (locals : List LeanExe.IR.Expr) (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.run body) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.run, extractScalarExprWith]

@[simp] theorem extractScalarExprWith_idPure (locals : List LeanExe.IR.Expr) (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.pure body) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.pure, extractScalarExprWith]

@[simp] theorem extractScalarExprWith_idBind (locals : List LeanExe.IR.Expr)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.bind name bi value body) = (do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (bound :: locals) body) := by
  rw [LeanExe.Source.Scalar.Identity.bind, extractScalarExprWith]

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
  | var h => exact bindings _ _ _ (by simpa only [extractScalarExprWith] using compiled) h
  | literal =>
    simp only [extractScalarExprWith, Option.some.injEq] at compiled
    subst target
    exact .const
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
  | @choose a values x b y t e value op type left right branch ihl ihr ihb =>
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, rfl⟩ := compiled
    have condition := lowerComparison_correct op (ihl ha bindings) (ihr hb bindings)
    cases flag : op.denote x y with
    | false =>
      exact .iteFalse (by simpa [flag] using condition)
        (ihb (by simpa [flag] using he) bindings)
    | true =>
      exact .iteTrue (by simpa [flag] using condition)
        (ihb (by simpa [flag] using ht) bindings)
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
  | idRun _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings
  | idPure _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings
  | idBind value body ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
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
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings

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
  | literal => exact ⟨.u64 _, by rw [extractScalarExprWith]⟩
  | ofNat => exact ⟨.u64 _, extractScalarExprWith_literalExpr _ _⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceHead_recognized op
    obtain ⟨a, ha⟩ := ihl locals len
    obtain ⟨b, hb⟩ := ihr locals len
    exact ⟨p.lower a b, by rw [extractScalarExprWith_binary op]; simp [hp, ha, hb]⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨a, ha⟩ := ihl locals len
    obtain ⟨b, hb⟩ := ihr locals len
    obtain ⟨t, ht⟩ := iht locals len
    obtain ⟨e, he⟩ := ihe locals len
    exact ⟨.ite (lowerComparison op a b) t e, by
      rw [extractScalarExprWith_branch]; simp [ha, hb, ht, he]⟩
  | letE _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals len
    obtain ⟨target, ht⟩ := ihb (bound :: locals) (by simp [len])
    exact ⟨target, by simp [extractScalarExprWith, hb, ht]⟩
  | idRun _ ih => simpa only [extractScalarExprWith_idRun] using ih locals len
  | idPure _ ih => simpa only [extractScalarExprWith_idPure] using ih locals len
  | idBind _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals len
    obtain ⟨target, ht⟩ := ihb (bound :: locals) (by simp [len])
    exact ⟨target, by simp [hb, ht]⟩
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals len

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
  | case1 locals index =>
    exact .var (List.getElem?_eq_some_iff.mp (by simpa only [extractScalarExprWith] using compiled)).1
  | case2 => exact .literal
  | case3 locals n m heq =>
    have h : n = m := by simpa using heq
    subst m
    exact .ofNat
  | case4 locals n m hne => simp [extractScalarExprWith, hne] at compiled
  | case5 locals body ih =>
    exact .idRun (ih (by simpa only [extractScalarExprWith] using compiled))
  | case6 locals body ih =>
    exact .idPure (ih (by simpa only [extractScalarExprWith] using compiled))
  | case7 locals value name body bi ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .idBind (ihv hb) (by simpa using ihb bound ht)
  | case8 locals sourceType condition evidence t e rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case9 locals sourceType condition evidence t e type typeMatched rejected =>
    rw [extractScalarExprWith] at compiled
    rw [typeMatched, rejected] at compiled
    contradiction
  | case10 locals sourceType condition evidence t e type typeMatched op a b matched ihl ihr iht ihe =>
    have typeEq := scalarResultType_sound typeMatched
    subst sourceType
    obtain ⟨hc, he⟩ := comparison_sound matched
    subst condition evidence
    change LeanExe.Source.Scalar.Supported locals.length (op.branch a b t e type)
    change extractScalarExprWith locals (op.branch a b t e type) = some target at compiled
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, _⟩ := compiled
    exact .choose op type (ihl ha) (ihr hb) (iht ht) (ihe he)
  | case11 locals head left right excluded excludedRun excludedPure excludedBind excludedIf ihl ihr =>
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
  | case12 locals name value body nondep ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (ihv hb) (by simpa using ihb bound ht)
  | case13 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarExprWith] using compiled))
  | case14 locals expr hvar hliteral hofNat hrun hpure hbind hchoice hbin hlet hmetadata =>
    rw [extractScalarExprWith] at compiled <;> first | assumption | contradiction

theorem extractScalarExpr_supported {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  simpa using extractScalarExprWith_supported compiled

/-- A reusable closure property for the unchanged arithmetic backend. -/
theorem extractScalarExprWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {source : Lean.Expr} {locals : List LeanExe.IR.Expr} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ∀ expression ∈ locals, P expression) : P target := by
  have supported := extractScalarExprWith_supported compiled
  generalize hlen : locals.length = arity at supported
  induction supported generalizing locals target with
  | var hi => exact bindings target (List.mem_of_getElem? (by simpa only [extractScalarExprWith] using compiled))
  | literal =>
    simp only [extractScalarExprWith, Option.some.injEq] at compiled
    subst target
    exact literal _
  | ofNat =>
    simp only [extractScalarExprWith_literalExpr, Option.some.injEq] at compiled
    subst target
    exact literal _
  | binary op _ _ ihl ihr =>
    rw [extractScalarExprWith_binary op] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨p, hp, a, ha, b, hb, rfl⟩ := compiled
    exact binary p a b (ihl ha bindings hlen) (ihr hb bindings hlen)
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := compiled
    exact choice op a b t e (ihl ha bindings hlen) (ihr hb bindings hlen)
      (iht ht bindings hlen) (ihe he bindings hlen)
  | letE _ _ ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [hlen])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings hlen
    · exact bindings expression member
  | idRun _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings hlen
  | idPure _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings hlen
  | idBind _ _ ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [hlen])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings hlen
    · exact bindings expression member
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings hlen

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
