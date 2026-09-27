import LeanExe.Extract.ScalarSequence

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Every scalar expression occurring in the leaves satisfies the same property. -/
def ScalarSequencePlan.Holds (P : LeanExe.IR.Expr → Prop) : ScalarSequencePlan → Prop
  | .leaf plan => plan.Holds P
  | .bind first second => first.Holds P ∧ second.Holds P

/-- Sequence extraction preserves scalar invariants within its complete local allocation. -/
theorem extractScalarSequenceWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (limit : Nat) (get : ∀ index, index < limit → P (.local index))
    {locals : List ScalarBinding} {slot : Nat} {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarSequenceWith locals slot source = some plan)
    (room : slot + plan.width ≤ limit)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : plan.Holds P := by
  fun_induction extractScalarSequenceWith locals slot source generalizing plan with
  | case1 locals slot source before matched =>
    cases compiled
    have size : slot + 4 ≤ limit := room
    exact extractScalarWordRangeWith_invariant P literal binary choice
      (get slot (by omega)) (get (slot + 1) (by omega)) matched bindings
  | case2 locals slot name type value body nondep rejected firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    have allRoom : slot + (first.width + second.width) ≤ limit := room
    refine ⟨firstIH compiledFirst (by omega) bindings, secondIH first compiledSecond (by omega) ?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact get (first.resultSlot slot) (by have := (first.resultSlot_bounds slot).2; omega)
    · exact bindings binding member
  | case3 locals slot input output value name domain body binder rejected firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨types, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    have allRoom : slot + (first.width + second.width) ≤ limit := room
    refine ⟨firstIH compiledFirst (by omega) bindings, secondIH first compiledSecond (by omega) ?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact get (first.resultSlot slot) (by have := (first.resultSlot_bounds slot).2; omega)
    · exact bindings binding member
  | case4 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    exact ih compiled room bindings
  | case5 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    exact ih compiled room bindings
  | case6 locals slot data body rejected ih => exact ih compiled room bindings
  | case7 => contradiction

end LeanExe.Extract.Core
