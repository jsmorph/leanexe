import LeanExe.Extract.ScalarRange

namespace LeanExe.Extract.Core

def ScalarRangePlan.Holds (P : LeanExe.IR.Expr → Prop) (plan : ScalarRangePlan) : Prop :=
  P plan.count ∧ P plan.initial ∧ P plan.step ∧ P plan.result

/-- All four range expressions inherit every scalar invariant preserved by
literals, operations, conditionals and the two fresh readable loop locals. -/
theorem extractScalarRangeWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangePlan}
    (compiled : extractScalarRangeWith locals slot source = some plan)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  have expression {locals : List ScalarBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith locals source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled bindings
  have extend {locals : List ScalarBinding} {target : LeanExe.IR.Expr}
      (bindings : ∀ binding ∈ locals, binding.Holds P) (value : P target) :
      ∀ binding ∈ ScalarBinding.word target :: locals, binding.Holds P := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact value
    · exact bindings binding member
  induction locals, source using extractScalarRangeWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRange_sound matched
    subst source
    rw [extractScalarRangeWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨count, hc, initial, hi, scalar, hy, step, hs, rfl⟩ := compiled
    refine ⟨expression hc bindings, expression hi bindings, expression hs ?_, accumulator⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact accumulator
    rcases List.mem_cons.mp member with rfl | member
    · exact index
    · exact bindings binding member
  | case2 locals sourceType body invalid rejected =>
    rw [extractScalarRangeWith] at compiled
    simp [rejected, invalid] at compiled
  | case3 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeWith locals slot (LeanExe.Source.Scalar.Identity.run body type) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeWith_idRun] using compiled) bindings
  | case4 locals sourceType body invalid rejected =>
    rw [extractScalarRangeWith] at compiled
    simp [rejected, invalid] at compiled
  | case5 locals sourceType body type matched rejected ih =>
    have same := scalarResultType_sound matched
    subst sourceType
    change extractScalarRangeWith locals slot (LeanExe.Source.Scalar.Identity.pure body type) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeWith_idPure] using compiled) bindings
  | case6 locals name value body nondep rejected ih =>
    rw [extractScalarRangeWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    exact ih bound hp (extend bindings (expression hb bindings))
  | case7 locals input output value name domain body bi invalid rejected =>
    rw [extractScalarRangeWith] at compiled
    simp [rejected, invalid] at compiled
  | case8 locals input output value name domain body bi annotations typesMatched bound matched rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeWith_idBind, matched] at compiled
    exact ih compiled (extend bindings (expression matched bindings))
  | case9 locals input output value name domain body bi annotations typesMatched notPure rejected ih =>
    obtain ⟨inputType, outputType⟩ := annotations
    obtain ⟨hi, hd, ho⟩ := scalarBindTypes_sound typesMatched
    subst input domain output
    change extractScalarRangeWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body inputType outputType) = some plan at compiled
    rw [extractScalarRangeWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, rfl⟩ := compiled
    obtain ⟨pc, pi, ps, pr⟩ := ih hb bindings
    exact ⟨pc, pi, ps, expression hr (extend bindings pr)⟩
  | case10 locals data body rejected ih =>
    exact ih (by simpa only [extractScalarRangeWith_metadata] using compiled) bindings
  | case11 locals source rejected hrun hpure hlet hbind hmetadata =>
    rw [extractScalarRangeWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
