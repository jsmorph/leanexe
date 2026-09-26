import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

inductive BindingKind where
  | word | boolean | natural | unit | function (withUnit : Bool)
  | booleanFunction
  | predicateFunction
  | binaryFunction
  | manyFunction (arity : Nat)
  deriving DecidableEq, Repr

/-- Internal lexical values. Exported functions still accept and return UInt64.
Local functions are pure, total scalar maps with their captured values fixed. -/
inductive Value where
  | word (value : UInt64)
  | boolean (value : Bool)
  | natural (value : Nat)
  | unit
  | function (withUnit : Bool) (apply : UInt64 → UInt64)
  | booleanFunction (apply : Bool → UInt64)
  | predicateFunction (apply : UInt64 → Bool)
  | binaryFunction (apply : UInt64 → UInt64 → UInt64)
  | manyFunction (arity : Nat) (apply : List UInt64 → UInt64)

def Value.kind : Value → BindingKind
  | .word _ => .word
  | .boolean _ => .boolean
  | .natural _ => .natural
  | .unit => .unit
  | .function withUnit _ => .function withUnit
  | .booleanFunction _ => .booleanFunction
  | .predicateFunction _ => .predicateFunction
  | .binaryFunction _ => .binaryFunction
  | .manyFunction arity _ => .manyFunction arity

theorem word_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .word) :
    ∃ value, values[index]? = some (.word value) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean _ => cases kind
  | word value => exact ⟨value, found⟩
  | natural _ | unit => cases kind
  | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem boolean_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .boolean) :
    ∃ value, values[index]? = some (.boolean value) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean value => exact ⟨value, found⟩
  | word _ | natural _ | unit => cases kind
  | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem natural_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .natural) :
    ∃ value, values[index]? = some (.natural value) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean _ => cases kind
  | natural value => exact ⟨value, found⟩
  | word _ | unit => cases kind
  | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem function_lookup {values : List Value} {types : List BindingKind} {index : Nat} {withUnit : Bool}
    (typed : values.map Value.kind = types) (present : types[index]? = some (.function withUnit)) :
    ∃ f, values[index]? = some (.function withUnit f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean _ => cases kind
  | word _ => cases kind
  | natural _ | unit | binaryFunction _ | manyFunction _ _ => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

theorem booleanFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .booleanFunction) :
    ∃ f, values[index]? = some (.booleanFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | boolean _ => cases kind
  | booleanFunction f => exact ⟨f, found⟩
  | predicateFunction _ => cases kind
  | word _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem predicateFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .predicateFunction) :
    ∃ f, values[index]? = some (.predicateFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | boolean _ => cases kind
  | predicateFunction f => exact ⟨f, found⟩
  | booleanFunction _ => cases kind
  | word _ | natural _ | unit | function _ _ | binaryFunction _ | manyFunction _ _ => cases kind

theorem binaryFunction_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .binaryFunction) :
    ∃ f, values[index]? = some (.binaryFunction f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean _ => cases kind
  | binaryFunction f => exact ⟨f, found⟩
  | word _ | natural _ | unit | function _ _ | manyFunction _ _ => cases kind

theorem manyFunction_lookup {values : List Value} {types : List BindingKind} {index arity : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some (.manyFunction arity)) :
    ∃ f, values[index]? = some (.manyFunction arity f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | booleanFunction _ | predicateFunction _ => cases kind
  | boolean _ => cases kind
  | manyFunction count f => cases kind; exact ⟨f, found⟩
  | word _ | natural _ | unit | function _ _ | binaryFunction _ => cases kind

end LeanExe.Source.Scalar
