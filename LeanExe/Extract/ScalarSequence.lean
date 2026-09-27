import LeanExe.Extract.ScalarWordRange
import LeanExe.Extract.ScalarSequencePlan
import LeanExe.Source.ScalarSequence

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Extend single-loop extraction with sequential word bindings and standard Id operations. -/
def extractScalarSequenceWith (locals : List ScalarBinding) (slot : Nat)
    (source : Lean.Expr) : Option ScalarSequencePlan :=
  match extractScalarWordRangeWith locals slot source with
  | some plan => some (.leaf plan)
  | none =>
    match source with
    | .letE _ type value body _ => do
        let _ ← scalarResultType? type
        let first ← extractScalarSequenceWith locals slot value
        let second ← extractScalarSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
          (slot + first.width) body
        pure (.bind first second)
    | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))) input) output) value)
        (.lam _ domain body _) => do
        let _ ← scalarBindTypes? input domain output
        let first ← extractScalarSequenceWith locals slot value
        let second ← extractScalarSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
          (slot + first.width) body
        pure (.bind first second)
    | .app (.app (.const ``Id.run [.zero]) type) body => do
        let _ ← scalarResultType? type
        extractScalarSequenceWith locals slot body
    | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
            (.const ``Id.instMonad [.zero])))) type) body => do
        let _ ← scalarResultType? type
        extractScalarSequenceWith locals slot body
    | .mdata _ body => extractScalarSequenceWith locals slot body
    | _ => none
termination_by sizeOf source

/-- Existing word computations keep their original extraction plan. -/
theorem extractScalarSequenceWith_word {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarWordRangeWith locals slot source = some plan) :
    extractScalarSequenceWith locals slot source = some (.leaf plan) := by
  rw [extractScalarSequenceWith.eq_def, compiled]

theorem extractScalarSequenceWith_let (locals : List ScalarBinding) (slot : Nat)
    (input : ResultType) (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool)
    (rejected : extractScalarWordRangeWith locals slot (.letE name input.expr value body nondep) = none) :
    extractScalarSequenceWith locals slot (.letE name input.expr value body nondep) = (do
      let first ← extractScalarSequenceWith locals slot value
      let second ← extractScalarSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
        (slot + first.width) body
      pure (.bind first second)) := by
  rw [extractScalarSequenceWith.eq_def, rejected]
  simp [scalarResultType_accepts]

theorem extractScalarSequenceWith_bind (locals : List ScalarBinding) (slot : Nat)
    (input output : ResultType) (name : Lean.Name) (binder : Lean.BinderInfo) (value body : Lean.Expr)
    (rejected : extractScalarWordRangeWith locals slot (Identity.bind name binder value body input output) = none) :
    extractScalarSequenceWith locals slot (Identity.bind name binder value body input output) = (do
      let first ← extractScalarSequenceWith locals slot value
      let second ← extractScalarSequenceWith (.word (.local (first.resultSlot slot)) :: locals)
        (slot + first.width) body
      pure (.bind first second)) := by
  rw [extractScalarSequenceWith.eq_def, rejected]
  simp [Identity.bind, scalarBindTypes_accepts]

theorem extractScalarSequenceWith_run (locals : List ScalarBinding) (slot : Nat)
    (type : ResultType) (body : Lean.Expr)
    (rejected : extractScalarWordRangeWith locals slot (Identity.run body type) = none) :
    extractScalarSequenceWith locals slot (Identity.run body type) = extractScalarSequenceWith locals slot body := by
  rw [extractScalarSequenceWith.eq_def, rejected]
  simp [Identity.run, scalarResultType_accepts]

theorem extractScalarSequenceWith_pure (locals : List ScalarBinding) (slot : Nat)
    (type : ResultType) (body : Lean.Expr)
    (rejected : extractScalarWordRangeWith locals slot (Identity.pure body type) = none) :
    extractScalarSequenceWith locals slot (Identity.pure body type) = extractScalarSequenceWith locals slot body := by
  rw [extractScalarSequenceWith.eq_def, rejected]
  simp [Identity.pure, scalarResultType_accepts]

theorem extractScalarSequenceWith_metadata (locals : List ScalarBinding) (slot : Nat)
    (data : Lean.MData) (body : Lean.Expr)
    (rejected : extractScalarWordRangeWith locals slot (.mdata data body) = none) :
    extractScalarSequenceWith locals slot (.mdata data body) = extractScalarSequenceWith locals slot body := by
  rw [extractScalarSequenceWith.eq_def, rejected]

private theorem accepts_fallback {locals : List ScalarBinding} {slot : Nat} {source : Lean.Expr}
    (fallback : extractScalarWordRangeWith locals slot source = none →
      ∃ plan, extractScalarSequenceWith locals slot source = some plan) :
    ∃ plan, extractScalarSequenceWith locals slot source = some plan := by
  cases compiled : extractScalarWordRangeWith locals slot source with
  | none => exact fallback compiled
  | some plan => exact ⟨.leaf plan, extractScalarSequenceWith_word compiled⟩

/-- Every independently supported sequence is accepted in every typed, total environment. -/
theorem extractScalarSequenceWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : Sequence.Supported types source) (locals : List ScalarBinding) (slot : Nat)
    (typed : locals.map ScalarBinding.kind = types)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ plan, extractScalarSequenceWith locals slot source = some plan := by
  induction supported generalizing locals slot with
  | word supported =>
    obtain ⟨plan, compiled⟩ := extractScalarWordRangeWith_accepts supported locals slot typed total
    exact ⟨.leaf plan, extractScalarSequenceWith_word compiled⟩
  | letWord input _ _ firstIH secondIH =>
    apply accepts_fallback
    intro rejected
    obtain ⟨first, compiledFirst⟩ := firstIH locals slot typed total
    obtain ⟨second, compiledSecond⟩ := secondIH (.word (.local (first.resultSlot slot)) :: locals)
      (slot + first.width) (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨.bind first second, by rw [extractScalarSequenceWith_let _ _ _ _ _ _ _ rejected]; simp [compiledFirst, compiledSecond]⟩
  | bindWord input output _ _ firstIH secondIH =>
    apply accepts_fallback
    intro rejected
    obtain ⟨first, compiledFirst⟩ := firstIH locals slot typed total
    obtain ⟨second, compiledSecond⟩ := secondIH (.word (.local (first.resultSlot slot)) :: locals)
      (slot + first.width) (by simp [ScalarBinding.kind, typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact total binding member)
    exact ⟨.bind first second, by rw [extractScalarSequenceWith_bind _ _ _ _ _ _ _ _ rejected]; simp [compiledFirst, compiledSecond]⟩
  | run type _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarSequenceWith_run _ _ _ _ rejected]; exact compiled⟩
  | pure type _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarSequenceWith_pure _ _ _ _ rejected]; exact compiled⟩
  | metadata _ ih =>
    apply accepts_fallback
    intro rejected
    obtain ⟨plan, compiled⟩ := ih locals slot typed total
    exact ⟨plan, by rw [extractScalarSequenceWith_metadata _ _ _ _ rejected]; exact compiled⟩

/-- Every successful extraction reconstructs the independent source contract. -/
theorem extractScalarSequenceWith_supported {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarSequenceWith locals slot source = some plan) :
    Sequence.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractScalarSequenceWith locals slot source generalizing plan with
  | case1 locals slot source before matched =>
    exact .word (extractScalarWordRangeWith_supported matched)
  | case2 locals slot name type value body nondep rejected firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .letWord input (firstIH compiledFirst) (secondIH first compiledSecond)
  | case3 locals slot input output value name domain body binder rejected firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨⟨inputType, outputType⟩, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    exact .bindWord inputType outputType (firstIH compiledFirst) (secondIH first compiledSecond)
  | case4 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .run input (ih compiled)
  | case5 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    exact .pure input (ih compiled)
  | case6 locals slot data body rejected ih => exact .metadata (ih compiled)
  | case7 => contradiction

end LeanExe.Extract.Core
