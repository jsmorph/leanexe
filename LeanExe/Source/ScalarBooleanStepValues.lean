import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar.BooleanStep

inductive BindingKind where
  | scalar (kind : Scalar.BindingKind)
  | wordFunction
  | booleanFunction
  deriving DecidableEq, Repr

inductive Value where
  | scalar (value : Scalar.Value)
  | wordFunction (apply : UInt64 → ForInStep Bool)
  | booleanFunction (apply : Bool → ForInStep Bool)

def Value.kind : Value → BindingKind
  | .scalar value => .scalar value.kind
  | .wordFunction _ => .wordFunction
  | .booleanFunction _ => .booleanFunction

def Value.toScalar : Value → Scalar.Value
  | .scalar value => value
  | .wordFunction _ | .booleanFunction _ => .unit

def BindingKind.toScalar : BindingKind → Scalar.BindingKind
  | .scalar kind => kind
  | .wordFunction | .booleanFunction => .unit

@[simp] theorem Value.toScalar_kind (value : Value) :
    value.toScalar.kind = value.kind.toScalar := by cases value <;> rfl

@[simp] theorem Value.scalar_kind (value : Scalar.Value) :
    (Value.scalar value).kind = .scalar value.kind := rfl

@[simp] theorem Value.toScalar_scalar (value : Scalar.Value) :
    (Value.scalar value).toScalar = value := rfl

theorem typed_projection {values : List Value} {types : List BindingKind}
    (typed : values.map Value.kind = types) :
    (values.map Value.toScalar).map Scalar.Value.kind = types.map BindingKind.toScalar := by
  rw [← typed]
  simp [List.map_map, Function.comp_def]

theorem wordFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .wordFunction) :
    ∃ f, values[index]? = some (.wordFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | wordFunction f => exact ⟨f, found⟩
  | scalar _ | booleanFunction _ => cases kind

theorem booleanFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .booleanFunction) :
    ∃ f, values[index]? = some (.booleanFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction f => exact ⟨f, found⟩
  | scalar _ | wordFunction _ => cases kind

end LeanExe.Source.Scalar.BooleanStep
