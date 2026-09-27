import LeanExe.Extract.ScalarSequence
import LeanExe.Extract.ScalarSequenceBindings

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Every extracted sequence executes with a source value and preserves its captured locals. -/
theorem extractScalarSequenceWith_correct {locals : List ScalarBinding} {slot : Nat}
    {source : Lean.Expr} {plan : ScalarSequencePlan}
    (compiled : extractScalarSequenceWith locals slot source = some plan)
    (saved : List UInt64) (values : List Value) (length : saved.length = slot)
    (typed : values.map Value.kind = locals.map ScalarBinding.kind)
    (bindings : SequenceBindingsMatch locals values saved)
    (total : ∀ binding ∈ locals, binding.Total) :
    ∃ value, Sequence.Eval source values value ∧ plan.Meaning saved value := by
  fun_induction extractScalarSequenceWith locals slot source generalizing saved values plan with
  | case1 locals slot source before matched =>
    cases compiled
    subst slot
    obtain ⟨value, evaluated, meaning⟩ := extractScalarWordRangeWith_correct saved values matched typed
      (fun accumulator index stop flag => bindings [accumulator, UInt64.ofNat index, stop, flag]) total
    exact ⟨value, .word evaluated, ScalarSequencePlan.Meaning.leaf meaning⟩
  | case2 locals slot source rejected shape parsed ih =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    subst slot
    obtain ⟨flag, evaluated, firstMeaning⟩ := extractScalarBooleanRangeWith_correct saved values
      compiledFirst typed (fun accumulator index stop exitFlag =>
        bindings [accumulator, UInt64.ofNat index, stop, exitFlag]) total
    obtain ⟨scratch, size, firstEval, present⟩ := ScalarSequencePlan.Meaning.leaf firstMeaning
    have extended := (bindings.extend scratch).booleanResult present
    have nextLength : (saved ++ scratch).length = saved.length + 4 := by simp [size, ScalarSequencePlan.width]
    have nextTyped : (Value.boolean flag :: values).map Value.kind =
        (ScalarBinding.boolean (.local saved.length) :: locals).map ScalarBinding.kind := by
      simp [Value.kind, ScalarBinding.kind, typed]
    have nextTotal : ∀ binding ∈ ScalarBinding.boolean (.local saved.length) :: locals, binding.Total := by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member
    obtain ⟨result, continuation, secondMeaning⟩ := ih compiledSecond (saved ++ scratch)
      (.boolean flag :: values) nextLength nextTyped extended nextTotal
    refine ⟨result, ?_, ScalarSequencePlan.Meaning.bind size firstEval secondMeaning⟩
    rw [booleanSequencePrefix_sound parsed]
    exact .booleanPrefix shape evaluated continuation
  | case3 locals slot name type value body nondep rejected noPrefix firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨input, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨word, evaluated, scratch, size, firstEval, result⟩ :=
      firstIH compiledFirst saved values length typed bindings total
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
  | case4 locals slot input output value name domain body binder rejected noPrefix firstIH secondIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨⟨inputType, outputType⟩, parsed, first, compiledFirst, second, compiledSecond, rfl⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    obtain ⟨word, evaluated, scratch, size, firstEval, result⟩ :=
      firstIH compiledFirst saved values length typed bindings total
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
  | case5 locals slot type body rejected noPrefix ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .run input evaluated, meaning⟩
  | case6 locals slot type body rejected noPrefix ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨input, parsed, compiled⟩ := compiled
    rw [scalarResultType_sound parsed]
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .pure input evaluated, meaning⟩
  | case7 locals slot data body rejected noPrefix ih =>
    obtain ⟨value, evaluated, meaning⟩ := ih compiled saved values length typed bindings total
    exact ⟨value, .metadata evaluated, meaning⟩
  | case8 => contradiction

end LeanExe.Extract.Core
