import LeanExe.Extract.ScalarPrimitive
import LeanExe.Source.Scalar

namespace LeanExe.Extract.Core

/-- Total primitive-expression traversal used by the production extractor.
The local map translates source de Bruijn indices into existing IR slots. -/
def extractScalarExpr (locals : List Nat) : Lean.Expr → Option LeanExe.IR.Expr
  | .bvar index => (locals[index]?).map LeanExe.IR.Expr.local
  | .app (.const ``UInt64.ofNat _) (.lit (.natVal n)) => some (.u64 n)
  | .app (.app (.const name _) left) right => do
      let op ← ScalarPrimitive.ofName? name
      let a ← extractScalarExpr locals left
      let b ← extractScalarExpr locals right
      pure (op.lower a b)
  | .mdata _ body => extractScalarExpr locals body
  | _ => none

theorem ScalarPrimitive.source_meaning (p : ScalarPrimitive) :
    LeanExe.Source.Scalar.Binary p.name p.denote := by
  cases p <;> constructor

theorem sourceBinary_recognized {name : Lean.Name} {f : UInt64 → UInt64 → UInt64}
    (h : LeanExe.Source.Scalar.Binary name f) :
    ∃ p : ScalarPrimitive, ScalarPrimitive.ofName? name = some p ∧ p.denote = f := by
  cases h
  all_goals first
    | exact ⟨.add, by decide, rfl⟩
    | exact ⟨.sub, by decide, rfl⟩
    | exact ⟨.mul, by decide, rfl⟩
    | exact ⟨.div, by decide, rfl⟩
    | exact ⟨.mod, by decide, rfl⟩
    | exact ⟨.land, by decide, rfl⟩
    | exact ⟨.lor, by decide, rfl⟩
    | exact ⟨.xor, by decide, rfl⟩
    | exact ⟨.shiftLeft, by decide, rfl⟩
    | exact ⟨.shiftRight, by decide, rfl⟩

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
  | @binary name f a values x b y levels op left right ihl ihr =>
    obtain ⟨p, hp, hf⟩ := sourceBinary_recognized op
    cases ha : extractScalarExpr locals a with
    | none => simp [extractScalarExpr, hp, ha] at compiled
    | some aIR =>
      cases hb : extractScalarExpr locals b with
      | none => simp [extractScalarExpr, hp, ha, hb] at compiled
      | some bIR =>
        have heq : p.lower aIR bIR = target := by
          simpa [extractScalarExpr, hp, ha, hb] using compiled
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
  | binary op _ _ ihl ihr =>
    obtain ⟨p, hp, _⟩ := sourceBinary_recognized op
    obtain ⟨a, ha⟩ := ihl len
    obtain ⟨b, hb⟩ := ihr len
    exact ⟨p.lower a b, by simp [extractScalarExpr, hp, ha, hb]⟩
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
  | case3 name levels left right ihl ihr =>
    cases hp : ScalarPrimitive.ofName? name with
    | none => simp [extractScalarExpr, hp] at compiled
    | some p =>
      cases ha : extractScalarExpr locals left with
      | none => simp [extractScalarExpr, hp, ha] at compiled
      | some a =>
        cases hb : extractScalarExpr locals right with
        | none => simp [extractScalarExpr, hp, ha, hb] at compiled
        | some b =>
          have meaning := p.source_meaning
          rw [ScalarPrimitive.ofName_sound hp] at meaning
          exact .binary meaning (ihl ha) (ihr hb)
  | case4 data body ih => exact .metadata (ih compiled)
  | case5 expr hvar hliteral hbin hmetadata =>
    unfold extractScalarExpr at compiled
    split at compiled <;> simp_all
    exact (hbin _ _ _ _ rfl rfl rfl rfl).elim

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
