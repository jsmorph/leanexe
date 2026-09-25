import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar.Step

/-- A step-valued continuation is distinct from a scalar-valued function. -/
inductive BindingKind where
  | resultFunction
  | result
  | scalar (kind : LeanExe.Source.Scalar.BindingKind)
  | function (withUnit : Bool)
  deriving DecidableEq, Repr

inductive Value where
  | resultFunction (apply : ForInStep UInt64 → ForInStep UInt64)
  | result (outcome : ForInStep UInt64)
  | scalar (value : LeanExe.Source.Scalar.Value)
  | function (withUnit : Bool) (apply : UInt64 → ForInStep UInt64)

def Value.kind : Value → BindingKind
  | .resultFunction _ => .resultFunction
  | .result _ => .result
  | .scalar value => .scalar value.kind
  | .function withUnit _ => .function withUnit

/-- Scalar subexpressions cannot call step-valued continuations. A Unit
placeholder preserves de Bruijn positions without making such calls available
to the scalar grammar. Actual step calls use the separate lookup below. -/
def Value.toScalar : Value → LeanExe.Source.Scalar.Value
  | .resultFunction _ => .unit
  | .result _ => .unit
  | .scalar value => value
  | .function _ _ => .unit

def BindingKind.toScalar : BindingKind → LeanExe.Source.Scalar.BindingKind
  | .resultFunction => .unit
  | .result => .unit
  | .scalar kind => kind
  | .function _ => .unit

@[simp] theorem Value.toScalar_kind (value : Value) :
    value.toScalar.kind = value.kind.toScalar := by cases value <;> rfl

theorem typed_projection {values : List Value} {types : List BindingKind}
    (typed : values.map Value.kind = types) :
    (values.map Value.toScalar).map LeanExe.Source.Scalar.Value.kind = types.map BindingKind.toScalar := by
  rw [← typed]
  simp [List.map_map, Function.comp_def]

theorem function_lookup {values : List Value} {types : List BindingKind} {index : Nat} {withUnit : Bool}
    (typed : values.map Value.kind = types) (present : types[index]? = some (.function withUnit)) :
    ∃ f, values[index]? = some (.function withUnit f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | resultFunction _ => cases kind
  | result _ => cases kind
  | scalar _ => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

theorem result_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .result) :
    ∃ outcome, values[index]? = some (.result outcome) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | resultFunction _ => cases kind
  | result outcome => exact ⟨outcome, found⟩
  | scalar _ => cases kind
  | function _ _ => cases kind

theorem resultFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .resultFunction) :
    ∃ f, values[index]? = some (.resultFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | resultFunction f => exact ⟨f, found⟩
  | result _ => cases kind
  | scalar _ => cases kind
  | function _ _ => cases kind

end LeanExe.Source.Scalar.Step
