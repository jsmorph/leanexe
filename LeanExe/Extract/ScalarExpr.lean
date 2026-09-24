import LeanExe.Extract.ScalarHead
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

/-- Total primitive-expression traversal used by the production extractor.
The local map translates source de Bruijn indices into existing IR slots. -/
def extractScalarExpr (locals : List Nat) : Lean.Expr → Option LeanExe.IR.Expr
  | .bvar index => (locals[index]?).map LeanExe.IR.Expr.local
  | .app (.const ``UInt64.ofNat _) (.lit (.natVal n)) => some (.u64 n)
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
      (.app (.const ``UInt64.instOfNat []) (.lit (.natVal m))) =>
      if n == m then some (.u64 n) else none
  | .app (.app head left) right => do
      let op ← ScalarPrimitive.ofHead? head
      let a ← extractScalarExpr locals left
      let b ← extractScalarExpr locals right
      pure (op.lower a b)
  | .mdata _ body => extractScalarExpr locals body
  | _ => none

theorem extractScalarExpr_binary {head : Lean.Expr} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Head head f) (locals : List Nat) (a b : Lean.Expr) :
    extractScalarExpr locals (.app (.app head a) b) = (do
      let p ← ScalarPrimitive.ofHead? head
      let left ← extractScalarExpr locals a
      let right ← extractScalarExpr locals b
      pure (p.lower left right)) := by
  cases h with
  | direct op => cases op <;> rfl
  | canonical op => cases op <;> rfl

@[simp] theorem extractScalarExpr_literalExpr (locals : List Nat) (n : Nat) :
    extractScalarExpr locals (LeanExe.Source.Scalar.literalExpr n) = some (.u64 n) := by
  simp [extractScalarExpr, LeanExe.Source.Scalar.literalExpr]

/-- Existing slots contain the values of the corresponding source binders. -/
def ScalarLocalsMatch (locals : List Nat) (values : List UInt64)
    (store : LeanExe.IR.ScalarStore) : Prop :=
  ∀ (index slot : Nat), locals[index]? = some slot → store[slot]? = values[index]?

/-- General semantic preservation for this production expression traversal. -/
theorem extractScalarExpr_correct {source : Lean.Expr} {values : List UInt64} {value : UInt64}
    (semantics : LeanExe.Source.Scalar.Eval source values value)
    {locals : List Nat} {target : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (compiled : extractScalarExpr locals source = some target)
    (bindings : ScalarLocalsMatch locals values store) :
    target.ScalarEval store value store := by
  induction semantics generalizing target with
  | var h =>
    simp only [extractScalarExpr, Option.map_eq_some_iff] at compiled
    obtain ⟨slot, hslot, rfl⟩ := compiled
    exact .local ((bindings _ _ hslot).trans h)
  | literal =>
    cases compiled
    exact .const
  | ofNat =>
    simp only [extractScalarExpr_literalExpr, Option.some.injEq] at compiled
    subst target
    exact .const
  | @binary head f a values x b y op left right ihl ihr =>
    rw [extractScalarExpr_binary op] at compiled
    obtain ⟨p, hp, hf⟩ := sourceHead_recognized op
    cases ha : extractScalarExpr locals a with
    | none => simp [hp, ha] at compiled
    | some aIR =>
      cases hb : extractScalarExpr locals b with
      | none => simp [hp, ha, hb] at compiled
      | some bIR =>
        have heq : p.lower aIR bIR = target := by
          simpa [hp, ha, hb] using compiled
        subst target
        rw [← hf]
        exact p.lower_correct (ihl ha bindings) (ihr hb bindings)
  | metadata _ ih => exact ih compiled bindings

/-- Support implies success; this theorem does not assume successful compilation. -/
theorem extractScalarExpr_accepts {source : Lean.Expr} {arity : Nat}
    (supported : LeanExe.Source.Scalar.Supported arity source)
    (locals : List Nat) (len : locals.length = arity) :
    ∃ target, extractScalarExpr locals source = some target := by
  induction supported with
  | var hi =>
    rename_i index arity
    have hv : index < locals.length := by omega
    exact ⟨.local locals[index], by simp [extractScalarExpr, List.getElem?_eq_getElem hv]⟩
  | literal => exact ⟨.u64 _, rfl⟩
  | ofNat => exact ⟨.u64 _, extractScalarExpr_literalExpr _ _⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceHead_recognized op
    obtain ⟨a, ha⟩ := ihl len
    obtain ⟨b, hb⟩ := ihr len
    exact ⟨p.lower a b, by rw [extractScalarExpr_binary op]; simp [hp, ha, hb]⟩
  | metadata _ ih => exact ih len

/-- Success cannot admit syntax outside the independently specified fragment. -/
theorem extractScalarExpr_supported {source : Lean.Expr} {locals : List Nat}
    {target : LeanExe.IR.Expr} (compiled : extractScalarExpr locals source = some target) :
    LeanExe.Source.Scalar.Supported locals.length source := by
  induction source using extractScalarExpr.induct generalizing target with
  | case1 index =>
    cases hslot : locals[index]? with
    | none => simp [extractScalarExpr, hslot] at compiled
    | some slot => exact .var (List.getElem?_eq_some_iff.mp hslot).1
  | case2 => exact .literal
  | case3 n m heq =>
    have h : n = m := by simpa using heq
    subst m
    exact .ofNat
  | case4 n m hne => simp [extractScalarExpr, hne] at compiled
  | case5 head left right excluded ihl ihr =>
    cases hp : ScalarPrimitive.ofHead? head with
    | none =>
      simp only [extractScalarExpr] at compiled
      simp [hp] at compiled
    | some p =>
      have meaning := ScalarPrimitive.ofHead_sound hp
      rw [extractScalarExpr_binary meaning] at compiled
      cases ha : extractScalarExpr locals left with
      | none => simp [hp, ha] at compiled
      | some a =>
        cases hb : extractScalarExpr locals right with
        | none => simp [hp, ha, hb] at compiled
        | some b => exact .binary meaning (ihl ha) (ihr hb)
  | case6 data body ih => exact .metadata (ih compiled)
  | case7 expr hvar hliteral hofNat hbin hmetadata =>
    unfold extractScalarExpr at compiled
    split at compiled <;> simp_all
    all_goals first
      | exact (hbin _ _ _ rfl rfl rfl).elim
      | exact (hofNat _ _ rfl rfl).elim

/-- Every source in this fragment compiles and has the same source/IR result
for every related input store. This is an extraction theorem, not yet a theorem
about declarations, the complete compiler, or emitted WebAssembly bytes. -/
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
