import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar.BooleanLocal

structure VariablesTyped (value : BooleanLocal) (types : List BindingKind) : Prop where
  wellScoped : value.WellScoped
  flags : ∀ index ∈ value.variables, types[index]? = some .boolean
  functions : ∀ index ∈ value.functions, types[index]? = some .predicateFunction

structure VariablesMean (value : BooleanLocal) (values : List Value) (native : BooleanEnvironment) : Prop where
  flags : ∀ index ∈ value.variables, values[index]? = some (.boolean (native index))
  functions : ∀ index ∈ value.functions, values[index]? = some (.predicateFunction (native.predicates index))

theorem VariablesTyped.evaluates {value : BooleanLocal} {types : List BindingKind}
    (supported : value.VariablesTyped types) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ native, value.VariablesMean values native := by
  classical
  have flags := fun index member => boolean_lookup typed (supported.flags index member)
  have functions := fun index member => predicateFunction_lookup typed (supported.functions index member)
  let native := fun index => if member : index ∈ value.variables then (flags index member).choose else false
  let predicates := fun index => if member : index ∈ value.functions then (functions index member).choose else fun _ => false
  refine ⟨⟨native, predicates⟩, ?_, ?_⟩
  · intro index member
    simpa only [native, dite_eq_left member] using (flags index member).choose_spec
  · intro index member
    simpa only [predicates, dite_eq_left member] using (functions index member).choose_spec

end LeanExe.Source.Scalar.BooleanLocal
