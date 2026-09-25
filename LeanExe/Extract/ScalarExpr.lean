import LeanExe.Extract.ScalarHead
import LeanExe.Extract.ScalarDo
import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarComparison
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

/-- Compile pure, total scalar expressions with an environment of already
compiled bindings. Substitution removes source lets without introducing effects.
Bindings may be duplicated or unused in the output; this is valid only for this
pure arithmetic fragment. The source semantics still evaluates each binding. -/
def extractScalarExprWith (locals : List ScalarBinding) : Lean.Expr → Option LeanExe.IR.Expr
  | .bvar index => locals[index]?.bind ScalarBinding.word?
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
      extractScalarExprWith (.word bound :: locals) body
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
  | .app (.app (.bvar index) (.const ``Unit.unit [])) argument => do
      let function ← locals[index]?.bind (ScalarBinding.function? true)
      let value ← extractScalarExprWith locals argument
      function value
  | .app (.app head left) right => do
      let op ← ScalarPrimitive.ofHead? head
      let a ← extractScalarExprWith locals left
      let b ← extractScalarExprWith locals right
      pure (op.lower a b)
  | .letE _ (.const ``UInt64 []) value body _ => do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (.word bound :: locals) body
  | .letE _ (.forallE _ (.const ``UInt64 []) resultType _)
      (.lam _ (.const ``UInt64 []) value _) body _ =>
      match scalarResultType? resultType with
      | none => none
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: locals) value
          let function := ScalarBinding.function false fun argument =>
            extractScalarExprWith (.word argument :: locals) value
          extractScalarExprWith (function :: locals) body
  | .letE _ (.forallE _ (.const ``Unit [])
      (.forallE _ (.const ``UInt64 []) resultType _) _)
      (.lam _ (.const ``Unit []) (.lam _ (.const ``UInt64 []) value _) _) body _ =>
      match scalarResultType? resultType with
      | none => none
      | some _ => do
          let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) value
          let function := ScalarBinding.function true fun argument =>
            extractScalarExprWith (.word argument :: .unit :: locals) value
          extractScalarExprWith (function :: locals) body
  | .app (.bvar index) argument => do
      let function ← locals[index]?.bind (ScalarBinding.function? false)
      let value ← extractScalarExprWith locals argument
      function value
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
  extractScalarExprWith (locals.map fun slot => .word (.local slot)) source

theorem extractScalarExprWith_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List ScalarBinding) (a b : Lean.Expr) :
    extractScalarExprWith locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      pure (p.lower left right)) := by
  cases h with
  | direct op => cases op <;> rw [extractScalarExprWith] <;> simp
  | canonical op => cases op <;> dsimp only [LeanExe.Source.Scalar.classHead] <;> rw [extractScalarExprWith] <;> simp

theorem extractScalarExprWith_branch (op : LeanExe.Source.Scalar.Comparison)
    (locals : List ScalarBinding) (a b t e : Lean.Expr) (type : LeanExe.Source.Scalar.ResultType) :
    extractScalarExprWith locals (op.branch a b t e type) = (do
      let left ← extractScalarExprWith locals a
      let right ← extractScalarExprWith locals b
      let onTrue ← extractScalarExprWith locals t
      let onFalse ← extractScalarExprWith locals e
      pure (.ite (lowerComparison op left right) onTrue onFalse)) := by
  rw [LeanExe.Source.Scalar.Comparison.branch, extractScalarExprWith]
  rw [scalarResultType_accepts, comparison_accepts]

@[simp] theorem extractScalarExprWith_idRun (locals : List ScalarBinding) (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.run body) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.run, extractScalarExprWith]

@[simp] theorem extractScalarExprWith_idPure (locals : List ScalarBinding) (body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.pure body) =
      extractScalarExprWith locals body := by
  rw [LeanExe.Source.Scalar.Identity.pure, extractScalarExprWith]

@[simp] theorem extractScalarExprWith_idBind (locals : List ScalarBinding)
    (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) :
    extractScalarExprWith locals (LeanExe.Source.Scalar.Identity.bind name bi value body) = (do
      let bound ← extractScalarExprWith locals value
      extractScalarExprWith (.word bound :: locals) body) := by
  rw [LeanExe.Source.Scalar.Identity.bind, extractScalarExprWith]

theorem extractScalarExprWith_letFn (locals : List ScalarBinding)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
      (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: locals) a
        extractScalarExprWith (.function false (fun argument =>
          extractScalarExprWith (.word argument :: locals) a) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_accepts]

theorem extractScalarExprWith_letUnitFn (locals : List ScalarBinding)
    (name unitTypeName typeName unitName paramName : Lean.Name)
    (unitTypeBi typeBi unitBi paramBi : Lean.BinderInfo)
    (type : LeanExe.Source.Scalar.ResultType) (a b : Lean.Expr) (nondep : Bool) :
    extractScalarExprWith locals (.letE name
      (.forallE unitTypeName (.const ``Unit [])
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
      (.lam unitName (.const ``Unit [])
        (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) = (do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .unit :: locals) a
        extractScalarExprWith (.function true (fun argument =>
          extractScalarExprWith (.word argument :: .unit :: locals) a) :: locals) b) := by
  rw [extractScalarExprWith, scalarResultType_accepts]

@[simp] theorem extractScalarExprWith_literalExpr (locals : List ScalarBinding) (n : Nat) :
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

theorem extractScalarExprWith_correct {source : Lean.Expr} {values : List LeanExe.Source.Scalar.Value} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.EvalWith source values value)
    {locals : List ScalarBinding} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ScalarBindingsMatch locals values store) :
    target.ScalarEval store value store := by
  induction semantics generalizing locals target with
  | var h => exact bindings.word (by simpa only [extractScalarExprWith] using compiled) h
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
    exact ihb hc (bindings.cons (ihv hb bindings))
  | idRun _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings
  | idPure _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings
  | idBind value body ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hc⟩ := compiled
    exact ihb hc (bindings.cons (ihv hb bindings))
  | apply function argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    exact bindings.function (Option.bind_eq_some_iff.mpr hf) function arg _ target (ih ha bindings) ht
  | letFn type function body ihf ihb =>
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    exact ihf value compiled (bindings.cons ha)
  | unitApply function argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    exact bindings.function (Option.bind_eq_some_iff.mpr hf) function arg _ target (ih ha bindings) ht
  | letUnitFn type function body ihf ihb =>
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht
    apply bindings.cons
    intro argument value target ha compiled
    exact ihf value compiled ((bindings.cons (binding := .unit) (value := .unit) trivial).cons ha)
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings

/-- General preservation for the production expression traversal. -/
theorem extractScalarExpr_correct {source : Lean.Expr} {values : List UInt64} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval source values value)
    {locals : List Nat} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExpr locals source = some target)
    (bindings : ScalarLocalsMatch locals values store) :
    target.ScalarEval store value store := by
  apply extractScalarExprWith_correct semantics compiled
  intro index binding value he hv
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he hv
  obtain ⟨slot, hs, rfl⟩ := he
  obtain ⟨word, hw, rfl⟩ := hv
  exact LeanExe.IR.Expr.ScalarEval.local ((bindings _ _ hs).trans hw)

theorem extractScalarExprWith_accepts {source : Lean.Expr} {types : List LeanExe.Source.Scalar.BindingKind}
    (supported : LeanExe.Source.Scalar.SupportedWith types source)
    (locals : List ScalarBinding) (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ target, extractScalarExprWith locals source = some target := by
  induction supported generalizing locals with
  | var hi =>
    obtain ⟨target, found⟩ := scalarWord_lookup (typed ▸ hi)
    exact ⟨target, by simpa only [extractScalarExprWith] using found⟩
  | literal => exact ⟨.u64 _, by rw [extractScalarExprWith]⟩
  | ofNat => exact ⟨.u64 _, extractScalarExprWith_literalExpr _ _⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceHead_recognized op
    obtain ⟨a, ha⟩ := ihl locals typed total
    obtain ⟨b, hb⟩ := ihr locals typed total
    exact ⟨p.lower a b, by rw [extractScalarExprWith_binary op]; simp [hp, ha, hb]⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨a, ha⟩ := ihl locals typed total
    obtain ⟨b, hb⟩ := ihr locals typed total
    obtain ⟨t, ht⟩ := iht locals typed total
    obtain ⟨e, he⟩ := ihe locals typed total
    exact ⟨.ite (lowerComparison op a b) t e, by
      rw [extractScalarExprWith_branch]; simp [ha, hb, ht, he]⟩
  | letE _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member; rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨target, by simp [extractScalarExprWith, hb, ht]⟩
  | idRun _ ih => simpa only [extractScalarExprWith_idRun] using ih locals typed total
  | idPure _ ih => simpa only [extractScalarExprWith_idPure] using ih locals typed total
  | idBind _ _ ihv ihb =>
    obtain ⟨bound, hb⟩ := ihv locals typed total
    obtain ⟨target, ht⟩ := ihb (.word bound :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member; rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨target, by simp [hb, ht]⟩
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := scalarFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := ih locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarExprWith]; simp [hf, ScalarBinding.function?, ha, ht]⟩
  | @letFn types a b name typeName typeBi paramName paramBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.word argument :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function false f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarExprWith_letFn]; simp [hc, ht, f]⟩
  | unitApply present _ ih =>
    obtain ⟨f, hf⟩ := scalarFunction_lookup (typed ▸ present)
    obtain ⟨arg, ha⟩ := ih locals typed total
    obtain ⟨target, ht⟩ := total _ (List.mem_of_getElem? hf) arg
    exact ⟨target, by rw [extractScalarExprWith]; simp [hf, ScalarBinding.function?, ha, ht]⟩
  | @letUnitFn types a b name unitTypeName typeName typeBi unitTypeBi unitName paramName paramBi unitBi nondep type _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.word argument :: .unit :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: .unit :: locals) a
    obtain ⟨target, ht⟩ := ihb (.function true f :: locals)
      (by simp [ScalarBinding.kind, typed]) (by
        intro binding member; rcases List.mem_cons.mp member with rfl | member
        · exact accepts
        · exact total binding member)
    exact ⟨target, by rw [extractScalarExprWith_letUnitFn]; simp [hc, ht, f]⟩
  | metadata _ ih => simpa only [extractScalarExprWith] using ih locals typed total

theorem extractScalarExpr_accepts {source : Lean.Expr} {arity : Nat}
    (supported : LeanExe.Source.Scalar.Supported arity source)
    (locals : List Nat) (len : locals.length = arity) :
    ∃ target, extractScalarExpr locals source = some target :=
  extractScalarExprWith_accepts supported _
    (by simp [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const', len])
    (by intro binding member; obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member; trivial)

/-- Success admits only the independently specified source grammar. -/
theorem extractScalarExprWith_supported {source : Lean.Expr} {locals : List ScalarBinding}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExprWith locals source = some target) :
    LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) source := by
  induction locals, source using extractScalarExprWith.induct generalizing target with
  | case1 locals index =>
    exact .var (scalarWord_kind (by simpa only [extractScalarExprWith] using compiled))
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
    exact .idBind (ihv hb) (by simpa [ScalarBinding.kind] using ihb bound ht)
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
    change LeanExe.Source.Scalar.SupportedWith (locals.map ScalarBinding.kind) (op.branch a b t e type)
    change extractScalarExprWith locals (op.branch a b t e type) = some target at compiled
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨ai, ha, bi, hb, ti, ht, ei, he, _⟩ := compiled
    exact .choose op type (ihl ha) (ihr hb) (iht ht) (ihe he)
  | case11 locals index argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .unitApply (scalarFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case12 locals head left right excluded excludedRun excludedPure excludedBind excludedIf excludedUnit ihl ihr =>
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
  | case13 locals name value body nondep ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    exact .letE (ihv hb) (by simpa [ScalarBinding.kind] using ihb bound ht)
  | case14 locals name typeName resultType typeBi paramName value paramBi body nondep rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case15 locals name typeName resultType typeBi paramName value paramBi body nondep type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letFn type (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case16 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep rejected =>
    rw [extractScalarExprWith] at compiled
    rw [rejected] at compiled
    contradiction
  | case17 locals name unitTypeName typeName resultType typeBi unitTypeBi unitName paramName value paramBi unitBi body nondep type matched ih0 ihf ihb =>
    have typeEq := scalarResultType_sound matched
    subst resultType
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, hc, ht⟩ := compiled
    exact .letUnitFn type (by simpa [ScalarBinding.kind] using ih0 hc)
      (by simpa [ScalarBinding.kind] using ihb ht)
  | case18 locals index argument ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, _⟩ := compiled
    exact .apply (scalarFunction_kind (Option.bind_eq_some_iff.mpr hf)) (ih ha)
  | case19 locals data body ih =>
    exact .metadata (ih (by simpa only [extractScalarExprWith] using compiled))
  | case20 locals expr hvar hliteral hofNat hrun hpure hbind hchoice hunitApp hbin hlet hletFn hletUnitFn happ hmetadata =>
    rw [extractScalarExprWith] at compiled <;> first | assumption | contradiction

theorem extractScalarExpr_supported {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  simpa [List.map_map, Function.comp_def, ScalarBinding.kind, List.map_const'] using extractScalarExprWith_supported compiled

/-- A reusable closure property for the unchanged arithmetic backend. -/
theorem extractScalarExprWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {source : Lean.Expr} {locals : List ScalarBinding} {target : LeanExe.IR.Expr}
    (compiled : extractScalarExprWith locals source = some target)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : P target := by
  have supported := extractScalarExprWith_supported compiled
  generalize htypes : locals.map ScalarBinding.kind = types at supported
  induction supported generalizing locals target with
  | @var types index hi =>
    have found : (locals[index]?.bind ScalarBinding.word?) = some target := by
      simpa only [extractScalarExprWith] using compiled
    obtain ⟨binding, hb, matched⟩ := Option.bind_eq_some_iff.mp found
    cases binding with
    | word expression => cases matched; exact bindings _ (List.mem_of_getElem? hb)
    | unit | function _ _ => contradiction
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
    exact binary p a b (ihl ha bindings htypes) (ihr hb bindings htypes)
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    rw [extractScalarExprWith_branch] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨a, ha, b, hb, t, ht, e, he, rfl⟩ := compiled
    exact choice op a b t e (ihl ha bindings htypes) (ihr hb bindings htypes)
      (iht ht bindings htypes) (ihe he bindings htypes)
  | letE _ _ ihv ihb =>
    simp only [extractScalarExprWith, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings htypes
    · exact bindings expression member
  | idRun _ ih => exact ih (by simpa only [extractScalarExprWith_idRun] using compiled) bindings htypes
  | idPure _ ih => exact ih (by simpa only [extractScalarExprWith_idPure] using compiled) bindings htypes
  | idBind _ _ ihv ihb =>
    simp only [extractScalarExprWith_idBind, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv hb bindings htypes
    · exact bindings expression member
  | apply present _ ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    obtain ⟨binding, hb, matched⟩ := hf
    cases binding with
    | word _ => contradiction
    | unit => contradiction
    | function shape g =>
      have same := ScalarBinding.function?_some.mp matched
      cases same
      exact bindings _ (List.mem_of_getElem? hb) arg target (ih ha bindings htypes) ht
  | letFn type _ _ ihf ihb =>
    rw [extractScalarExprWith_letFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      · exact bindings binding member
    · exact bindings binding member
  | unitApply present _ ih =>
    rw [extractScalarExprWith] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, hf, arg, ha, ht⟩ := compiled
    obtain ⟨binding, hb, matched⟩ := hf
    have same := ScalarBinding.function?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? hb) arg target (ih ha bindings htypes) ht
  | letUnitFn type _ _ ihf ihb =>
    rw [extractScalarExprWith_letUnitFn] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, ht⟩ := compiled
    apply ihb ht _ (by simp [ScalarBinding.kind, htypes])
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target ha compiled
      apply ihf compiled _ (by simp [ScalarBinding.kind, htypes])
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact bindings binding member
    · exact bindings binding member
  | metadata _ ih => exact ih (by simpa only [extractScalarExprWith] using compiled) bindings htypes

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
