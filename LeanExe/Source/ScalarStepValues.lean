import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar.Step

/-- A step-valued continuation is distinct from a scalar-valued function. -/
inductive BindingKind where
  | scalar (kind : LeanExe.Source.Scalar.BindingKind)
  | function (withUnit : Bool)
  deriving DecidableEq, Repr

inductive Value where
  | scalar (value : LeanExe.Source.Scalar.Value)
  | function (withUnit : Bool) (apply : UInt64 → ForInStep UInt64)

def Value.kind : Value → BindingKind
  | .scalar value => .scalar value.kind
  | .function withUnit _ => .function withUnit

/-- Scalar subexpressions cannot call step-valued continuations. A Unit
placeholder preserves de Bruijn positions without making such calls available
to the scalar grammar. Actual step calls use the separate lookup below. -/
def Value.toScalar : Value → LeanExe.Source.Scalar.Value
  | .scalar value => value
  | .function _ _ => .unit

def BindingKind.toScalar : BindingKind → LeanExe.Source.Scalar.BindingKind
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
  | scalar _ => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

end LeanExe.Source.Scalar.Step
