import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

inductive BindingKind where
  | word | natural | unit | function (withUnit : Bool)
  deriving DecidableEq, Repr

/-- Internal lexical values. Exported functions still accept and return UInt64.
Local functions are pure, total scalar maps with their captured values fixed. -/
inductive Value where
  | word (value : UInt64)
  | natural (value : Nat)
  | unit
  | function (withUnit : Bool) (apply : UInt64 → UInt64)

def Value.kind : Value → BindingKind
  | .word _ => .word
  | .natural _ => .natural
  | .unit => .unit
  | .function withUnit _ => .function withUnit

theorem word_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .word) :
    ∃ value, values[index]? = some (.word value) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | word value => exact ⟨value, found⟩
  | natural _ | unit => cases kind
  | function _ _ => cases kind

theorem natural_lookup {values : List Value} {types : List BindingKind} {index : Nat}
    (typed : values.map Value.kind = types) (present : types[index]? = some .natural) :
    ∃ value, values[index]? = some (.natural value) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | natural value => exact ⟨value, found⟩
  | word _ | unit => cases kind
  | function _ _ => cases kind

theorem function_lookup {values : List Value} {types : List BindingKind} {index : Nat} {withUnit : Bool}
    (typed : values.map Value.kind = types) (present : types[index]? = some (.function withUnit)) :
    ∃ f, values[index]? = some (.function withUnit f) := by
  rw [← typed, List.getElem?_map] at present
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp present
  cases value with
  | word _ => cases kind
  | natural _ | unit => cases kind
  | function shape f => cases kind; exact ⟨f, found⟩

end LeanExe.Source.Scalar
