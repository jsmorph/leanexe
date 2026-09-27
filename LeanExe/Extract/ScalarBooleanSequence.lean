import LeanExe.Extract.ScalarSequence
import LeanExe.Source.ScalarBooleanSequence

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Extend single-loop extraction with word prefixes and Boolean results. -/
def extractScalarBooleanSequenceWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarSequencePlan :=
  match extractScalarBooleanRangeWith locals slot source with
  | some plan => some (.leaf plan)
  | none =>
    match source with
    | .letE _ type value body _ => do
        let _ ← scalarResultType? type
        let first ← extractScalarSequenceWith locals slot value
        let second ← extractScalarBooleanSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
          (slot + first.width) body
        pure (.bind first second)
    | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))) input) output) value)
        (.lam _ domain body _) => do
        let _ ← booleanRangeBindTypes? input domain output
        let first ← extractScalarSequenceWith locals slot value
        let second ← extractScalarBooleanSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
          (slot + first.width) body
        pure (.bind first second)
    | .app (.app (.const ``Id.run [.zero]) type) body => do
        let _ ← booleanType? type
        extractScalarBooleanSequenceWith locals slot body
    | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero])))) type) body => do
        let _ ← booleanType? type
        extractScalarBooleanSequenceWith locals slot body
    | .mdata _ body => extractScalarBooleanSequenceWith locals slot body
    | _ => none
termination_by sizeOf source

/-- Existing word computations keep their original extraction plan. -/
theorem extractScalarBooleanSequenceWith_boolean {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarBooleanRangeWith locals slot source = some plan) :
    extractScalarBooleanSequenceWith locals slot source = some (.leaf plan) := by
  rw [extractScalarBooleanSequenceWith.eq_def, compiled]

theorem extractScalarBooleanSequenceWith_let (locals : List ScalarBinding) (slot : Nat)
    (input : ResultType) (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool)
    (rejected : extractScalarBooleanRangeWith locals slot (.letE name input.expr value body nondep) = none) :
    extractScalarBooleanSequenceWith locals slot (.letE name input.expr value body nondep) = (do
      let first ← extractScalarSequenceWith locals slot value
      let second ← extractScalarBooleanSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
        (slot + first.width) body
      pure (.bind first second)) := by
  rw [extractScalarBooleanSequenceWith.eq_def, rejected]
  simp [scalarResultType_accepts]

theorem extractScalarBooleanSequenceWith_bind (locals : List ScalarBinding) (slot : Nat)
    (input : ResultType) (output : BooleanType) (name : Lean.Name) (binder : Lean.BinderInfo) (value body : Lean.Expr)
    (rejected : extractScalarBooleanRangeWith locals slot (BooleanRange.bind name binder input output value body) = none) :
    extractScalarBooleanSequenceWith locals slot (BooleanRange.bind name binder input output value body) = (do
      let first ← extractScalarSequenceWith locals slot value
      let second ← extractScalarBooleanSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
        (slot + first.width) body
      pure (.bind first second)) := by
  rw [extractScalarBooleanSequenceWith.eq_def, rejected]
  simp [BooleanRange.bind, BooleanBindingForm.expr, booleanRangeBindTypes_accepts]

theorem extractScalarBooleanSequenceWith_run (locals : List ScalarBinding) (slot : Nat)
    (type : BooleanType) (body : Lean.Expr)
    (rejected : extractScalarBooleanRangeWith locals slot (BooleanIdentity.run body type) = none) :
    extractScalarBooleanSequenceWith locals slot (BooleanIdentity.run body type) = extractScalarBooleanSequenceWith locals slot body := by
  rw [extractScalarBooleanSequenceWith.eq_def, rejected]
  simp [BooleanIdentity.run, booleanType_accepts]

theorem extractScalarBooleanSequenceWith_pure (locals : List ScalarBinding) (slot : Nat)
    (type : BooleanType) (body : Lean.Expr)
    (rejected : extractScalarBooleanRangeWith locals slot (BooleanIdentity.pure body type) = none) :
    extractScalarBooleanSequenceWith locals slot (BooleanIdentity.pure body type) = extractScalarBooleanSequenceWith locals slot body := by
  rw [extractScalarBooleanSequenceWith.eq_def, rejected]
  simp [BooleanIdentity.pure, booleanType_accepts]

theorem extractScalarBooleanSequenceWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr)
    (rejected : extractScalarBooleanRangeWith locals slot (.mdata data body) = none) :
    extractScalarBooleanSequenceWith locals slot (.mdata data body) = extractScalarBooleanSequenceWith locals slot body := by
  rw [extractScalarBooleanSequenceWith.eq_def, rejected]

private theorem accepts_fallback {locals : List ScalarBinding} {slot : Nat} {source : Lean.Expr}
    (fallback : extractScalarBooleanRangeWith locals slot source = none →
      ∃ plan, extractScalarBooleanSequenceWith locals slot source = some plan) :
    ∃ plan, extractScalarBooleanSequenceWith locals slot source = some plan := by
  cases compiled : extractScalarBooleanRangeWith locals slot source with
  | none => exact fallback compiled
  | some plan => exact ⟨.leaf plan, extractScalarBooleanSequenceWith_boolean compiled⟩

/-- Every independently supported sequence is accepted in every typed, total environment. -/
theorem extractScalarBooleanSequenceWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanSequence.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarBooleanSequenceWith locals slot source = some plan := by
  induction supported generalizing locals slot with
  | boolean supported =>
    obtain ⟨plan, compiled⟩ := extractScalarBooleanRangeWith_accepts supported locals slot typed total
    exact ⟨.leaf plan, extractScalarBooleanSequenceWith_boolean compiled⟩
  | letWord input value _ secondIH =>
    apply accepts_fallback
    intro rejected
    obtain ⟨first, compiledFirst⟩ := extractScalarSequenceWith_accepts value locals slot typed total
    obtain ⟨second, compiledSecond⟩ := secondIH (.word (.local (first.resultSlot slot)) :: locals)
      (slot + first.width) (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨.bind first second, by rw [extractScalarBooleanSequenceWith_let _ _ _ _ _ _ _ rejected]; simp [compiledFirst, compiledSecond]⟩
  | bindWord input output value _ secondIH =>
    apply accepts_fallback
    intro rejected
    obtain ⟨first, compiledFirst⟩ := extractScalarSequenceWith_accepts value locals slot typed total
    obtain ⟨second, compiledSecond⟩ := secondIH (.word (.local (first.resultSlot slot)) :: locals)
      (slot + first.width) (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨.bind first second, by rw [extractScalarBooleanSequenceWith_bind _ _ _ _ _ _ _ _ rejected]; simp [compiledFirst, compiledSecond]⟩
  | run type _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarBooleanSequenceWith_run _ _ _ _ rejected]; exact compiled⟩
  | pure type _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarBooleanSequenceWith_pure _ _ _ _ rejected]; exact compiled⟩
  | metadata _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarBooleanSequenceWith_metadata _ _ _ _ rejected]; exact compiled⟩

/-- Every successful extraction reconstructs the independent source contract. -/
theorem extractScalarBooleanSequenceWith_supported {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarBooleanSequenceWith locals slot source = some plan) :
    BooleanSequence.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarBooleanSequenceWith locals slot source generalizing plan with
  | case1 locals slot source before matched =>
    exact .boolean (extractScalarBooleanRangeWith_supported matched)
  | case2 locals slot name type value body nondep rejected secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letWord input (extractScalarSequenceWith_supported compiledFirst) (secondIH first compiledSecond)
  | case3 locals slot input output value name domain body binder rejected secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨⟨inputType, outputType⟩, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .bindWord inputType outputType (extractScalarSequenceWith_supported compiledFirst) (secondIH first compiledSecond)
  | case4 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    exact .run input (ih compiled)
  | case5 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    exact .pure input (ih compiled)
  | case6 locals slot data body rejected ih => exact .metadata (ih compiled)
  | case7 => contradiction

end LeanExe.Extract.Core
