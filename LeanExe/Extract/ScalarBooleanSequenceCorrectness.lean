import LeanExe.Extract.ScalarBooleanSequence
import LeanExe.Extract.ScalarSequenceCorrectness
import LeanExe.Extract.ScalarSequenceBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Every extracted sequence executes with a source value and preserves its captured locals. -/
theorem extractScalarBooleanSequenceWith_correct {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarBooleanSequenceWith locals slot source = some plan)
    (saved : List UInt64) (values : List Value) (length : saved.length = slot)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : SequenceBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, BooleanSequence.Eval source values value ∧ plan.Meaning saved value.toUInt64 := by
  fun_induction extractScalarBooleanSequenceWith locals slot source generalizing saved values plan with
  | case1 locals slot source before matched =>
    cases compiled
    subst slot
    obtain ⟨value, evaluated, meaning⟩ := extractScalarBooleanRangeWith_correct saved values matched typed
      (fun accumulator index stop flag => bindings [accumulator, UInt64.ofNat index, stop, flag]) total
    exact ⟨value, .boolean evaluated, ScalarSequencePlan.Meaning.leaf meaning⟩
  | case2 locals slot name type value body nondep rejected secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨word, evaluated, scratch, size, firstEval, result⟩ :=
      extractScalarSequenceWith_correct compiledFirst saved values length typed bindings total
    have extended := (bindings.extend scratch).result result
    have nextLength : (saved ++ scratch).length = slot + first.width := by simp [length, size]
    have nextTyped : (Value.word word :: values).map Value.kind =
        (ScalarBinding.word (.local (first.resultSlot slot)) :: locals).map ScalarBinding.kind := by
      simp [Value.kind, ScalarBinding.kind, typed]
    have nextTotal : ∀ binding ∈ ScalarBinding.word (.local (first.resultSlot slot)) :: locals, binding.Total := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member
    obtain ⟨value, continuation, secondMeaning⟩ := secondIH first compiledSecond (saved ++ scratch)
      (.word word :: values) nextLength nextTyped (by simpa only [length] using extended) nextTotal
    exact ⟨value, .letWord input evaluated continuation, ScalarSequencePlan.Meaning.bind size firstEval secondMeaning⟩
  | case3 locals slot input output value name domain body binder rejected secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨⟨inputType, outputType⟩, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    obtain ⟨word, evaluated, scratch, size, firstEval, result⟩ :=
      extractScalarSequenceWith_correct compiledFirst saved values length typed bindings total
    have extended := (bindings.extend scratch).result result
    have nextLength : (saved ++ scratch).length = slot + first.width := by simp [length, size]
    have nextTyped : (Value.word word :: values).map Value.kind =
        (ScalarBinding.word (.local (first.resultSlot slot)) :: locals).map ScalarBinding.kind := by
      simp [Value.kind, ScalarBinding.kind, typed]
    have nextTotal : ∀ binding ∈ ScalarBinding.word (.local (first.resultSlot slot)) :: locals, binding.Total := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member
    obtain ⟨value, continuation, secondMeaning⟩ := secondIH first compiledSecond (saved ++ scratch)
      (.word word :: values) nextLength nextTyped (by simpa only [length] using extended) nextTotal
    exact ⟨value, .bindWord inputType outputType evaluated continuation,
      ScalarSequencePlan.Meaning.bind size firstEval secondMeaning⟩
  | case4 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .run input evaluated, meaning⟩
  | case5 locals slot type body rejected ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [booleanType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .pure input evaluated, meaning⟩
  | case6 locals slot data body rejected ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .metadata evaluated, meaning⟩
  | case7 => contradiction

end LeanExe.Extract.Core
