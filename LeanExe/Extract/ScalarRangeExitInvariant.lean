import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarStepInvariant

namespace LeanExe.Extract.Core

def ScalarRangeExitPlan.Holds (P : LeanExe.IR.Expr → Prop) (plan : ScalarRangeExitPlan) : Prop :=
  P plan.count ∧ P plan.initial ∧ P plan.step ∧ P plan.done ∧ P plan.result

/-- All five range expressions inherit every scalar invariant preserved by
literals, operations, conditionals and the two fresh readable loop locals. -/
theorem extractScalarRangeExitWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {slot : Nat} (accumulator : P (.local slot)) (index : P (.local (slot + 1)))
    {source : Lean.Expr} {locals : List ScalarBinding} {plan : ScalarRangeExitPlan}
    (compiled : extractScalarRangeExitWith locals slot source = some plan)
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
  induction locals, source using extractScalarRangeExitWith.induct generalizing plan with
  | case1 locals source view matched =>
    have same := scalarRange_sound matched
    subst source
    rw [extractScalarRangeExitWith_call] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨count, hc, initial, hi, code, hs, rfl⟩ := compiled
    have pair := extractScalarStepWith_invariant P literal binary choice hs
    have both : code.Holds P := pair (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact accumulator
      rcases List.mem_cons.mp member with rfl | member
      · exact index
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact bindings original present)
    exact ⟨expression hc bindings, expression hi bindings, both.1, both.2, accumulator⟩
  | case2 locals body rejected ih =>
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.run body) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeExitWith_idRun] using compiled) bindings
  | case3 locals body rejected ih =>
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.pure body) = some plan at compiled
    exact ih (by simpa only [extractScalarRangeExitWith_idPure] using compiled) bindings
  | case4 locals name value body nondep rejected ih =>
    rw [extractScalarRangeExitWith_letE] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, hb, hp⟩ := compiled
    exact ih bound hp (extend bindings (expression hb bindings))
  | case5 locals value name body bi bound matched rejected ih =>
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, matched] at compiled
    exact ih compiled (extend bindings (expression matched bindings))
  | case6 locals value name body bi notPure rejected ih =>
    change extractScalarRangeExitWith locals slot (LeanExe.Source.Scalar.Identity.bind name bi value body) = some plan at compiled
    rw [extractScalarRangeExitWith_idBind, notPure] at compiled
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨before, hb, result, hr, rfl⟩ := compiled
    obtain ⟨pc, pi, ps, pd, pr⟩ := ih hb bindings
    exact ⟨pc, pi, ps, pd, expression hr (extend bindings pr)⟩
  | case7 locals data body rejected ih =>
    exact ih (by simpa only [extractScalarRangeExitWith_metadata] using compiled) bindings
  | case8 locals source rejected hrun hpure hlet hbind hmetadata =>
    rw [extractScalarRangeExitWith] at compiled <;> first | assumption | (simp [rejected] at compiled)

end LeanExe.Extract.Core
