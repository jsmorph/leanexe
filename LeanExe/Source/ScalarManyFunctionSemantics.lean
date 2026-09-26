import LeanExe.Source.Scalar

namespace LeanExe.Source.Scalar

/-- Supported helper bodies supply one native total closure for every argument
list of the declared length. Calls cannot observe the unused lengths. -/
theorem SupportedWith.manyFunction_evaluates {types : List BindingKind} {shape : ManyFunction}
    (supported : SupportedWith (List.replicate shape.arity .word ++ types) shape.body)
    (values : List Value) (typed : values.map Value.kind = types) :
    ∃ f : List UInt64 → UInt64, ∀ arguments, arguments.length = shape.arity →
      EvalWith shape.body (arguments.reverse.map Value.word ++ values) (f arguments) := by
  classical
  have total := fun (arguments : List UInt64) (len : arguments.length = shape.arity) =>
    supported.evaluates (arguments.reverse.map Value.word ++ values)
      (by simp [List.map_map, Function.comp_def, Value.kind, List.map_const', len, typed])
  let f : List UInt64 → UInt64 := fun arguments =>
    if len : arguments.length = shape.arity then (total arguments len).choose else 0
  refine ⟨f, ?_⟩
  intro arguments len
  simpa only [f, dite_eq_left len] using (total arguments len).choose_spec

end LeanExe.Source.Scalar
