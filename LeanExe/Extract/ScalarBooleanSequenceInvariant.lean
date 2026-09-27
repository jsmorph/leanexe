import LeanExe.Extract.ScalarBooleanSequence
import LeanExe.Extract.ScalarSequenceInvariant

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Sequence extraction preserves scalar invariants within its complete local allocation. -/
theorem extractScalarBooleanSequenceWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (limit : Nat) (get : ∀ index, index < limit → P (.local index))
    {locals : List ScalarBinding} {slot : Nat} {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarBooleanSequenceWith locals slot source = some plan)
    (room : slot + plan.width ≤ limit)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarBooleanSequenceWith locals slot source generalizing plan with
  | case1 locals slot source before matched =>
    cases compiled
    have size : slot + 4 ≤ limit := room
    exact extractScalarBooleanRangeWith_invariant P literal binary choice
      (get slot (by omega)) (get (slot + 1) (by omega)) matched bindings
  | case2 locals slot source rejected shape parsed ih =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    have allRoom : slot + (4 + second.width) ≤ limit := room
    refine ⟨extractScalarBooleanRangeWith_invariant P literal binary choice
      (get slot (by omega)) (get (slot + 1) (by omega)) compiledFirst bindings,
      ih compiledSecond (by omega) ?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact get slot (by omega)
    · exact bindings binding member
  | case3 locals slot name type value body nondep rejected noPrefix secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    have allRoom : slot + (first.width + second.width) ≤ limit := room
    refine ⟨extractScalarSequenceWith_invariant P literal binary choice limit get compiledFirst (by omega) bindings, secondIH first compiledSecond (by omega) ?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact get (first.resultSlot slot) (by have := (first.resultSlot_bounds slot).2; omega)
    · exact bindings binding member
  | case4 locals slot input output value name domain body binder rejected noPrefix secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨types, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    have allRoom : slot + (first.width + second.width) ≤ limit := room
    refine ⟨extractScalarSequenceWith_invariant P literal binary choice limit get compiledFirst (by omega) bindings, secondIH first compiledSecond (by omega) ?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact get (first.resultSlot slot) (by have := (first.resultSlot_bounds slot).2; omega)
    · exact bindings binding member
  | case5 locals slot type body rejected noPrefix ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    exact ih compiled room bindings
  | case6 locals slot type body rejected noPrefix ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    exact ih compiled room bindings
  | case7 locals slot data body rejected noPrefix ih => exact ih compiled room bindings
  | case8 => contradiction

end LeanExe.Extract.Core
