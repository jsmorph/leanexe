import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar.BooleanLocal

def VariablesTyped (value : BooleanLocal) (types : List BindingKind) : Prop :=
  value.WellScoped ∧ ∀ index ∈ value.variables, types[index]? = some .boolean

def VariablesMean (value : BooleanLocal) (values : List Value) (native : BooleanEnvironment) : Prop :=
  ∀ index ∈ value.variables, values[index]? = some (.boolean (native index))

theorem VariablesTyped.evaluates {value : BooleanLocal} {types : List BindingKind}
    (supported : value.VariablesTyped types) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ native, value.VariablesMean values native := by
  classical
  have present := fun index member => boolean_lookup typed (supported.2 index member)
  let native := fun index => if member : index ∈ value.variables then (present index member).choose else false
  refine ⟨BooleanEnvironment.ofFlags native, ?_⟩
  intro index member
  simpa only [BooleanEnvironment.ofFlags, native, dite_eq_left member] using (present index member).choose_spec

end LeanExe.Source.Scalar.BooleanLocal
