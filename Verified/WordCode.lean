import Verified.State
import Verified.LocalFrame
import Verified.TreeFieldsCode

/-! The specifications of the code that turns the i64 that holds a word in memory into a value of
its type and back. -/

namespace Verified

open Wasm LeanExe.Pipeline

theorem wp_ofWordCode {m : Module} {st : Store Unit} {env' : HostEnv Unit} {s : Locals}
    {vs : List Value} {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wp m (ofWordCode ty ++ rest) Q st { s with values := .i64 w :: vs } env' ↔
      wp m rest Q st { s with values := typedValue ty w :: vs } env' := by
  cases ty <;> simp [ofWordCode, typedValue, wrap_toUInt32_num]

theorem wp_toWordCode {m : Module} {st : Store Unit} {env' : HostEnv Unit} {s : Locals}
    {vs : List Value} {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wp m (toWordCode ty ++ rest) Q st { s with values := typedValue ty w :: vs } env' ↔
      wp m rest Q st { s with values := .i64 (Value.word (typedValue ty w)) :: vs } env' := by
  cases ty <;> simp [toWordCode, typedValue, Value.word]
  rw [UInt64.ofNat_mod w.toNat_lt (by decide), UInt64.ofNat_toNat]
  rfl

private theorem Elem.width_ne_one_prod (a b : Elem) : (Elem.prod a b).width ≠ 1 := by
  have := a.width_pos
  have := b.width_pos
  simp only [Elem.width]
  omega

/-- An element of one word has one value, of its slot type. -/
theorem Elem.types_one : (e : Elem) → e.width = 1 → e.types = [e.slotType]
  | .word, _ | .bool, _ | .float, _ | .float32, _ => rfl
  | .prod a b, h => absurd h (Elem.width_ne_one_prod a b)

/-- The value of an element of one word is the value of its slot type that holds its word. -/
theorem Elem.values_one : (e : Elem) → e.width = 1 → (v : e.denote) →
    e.values v = [typedValue e.slotType (e.slotWord v)]
  | .word, _, _ | .bool, _, _ | .float, _, _ => rfl
  | .float32, _, v => by
    simp only [Elem.values, Elem.slotType, Elem.slotWord, typedValue, List.cons.injEq,
      Value.f32.injEq, and_true]
    exact (UInt32.toUInt32_toUInt64 v.toBits).symm
  | .prod a b, h, _ => absurd h (Elem.width_ne_one_prod a b)

/-- The value that holds the word of an element of one word gives back that word. -/
theorem Elem.word_slotWord : (e : Elem) → e.width = 1 → (v : e.denote) →
    Value.word (typedValue e.slotType (e.slotWord v)) = e.slotWord v
  | .word, _, _ | .bool, _, _ | .float, _, _ => rfl
  | .float32, _, v => by
    simp only [Elem.slotType, Elem.slotWord, typedValue, Value.word]
    rw [UInt32.toUInt32_toUInt64]
  | .prod a b, h, _ => absurd h (Elem.width_ne_one_prod a b)

/-- The values that hold the word fields of record constructor `r` in locals: each word as a value
of its slot type. -/
def TreeShape.wordValues (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote) : List Value :=
  List.ofFn fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i)

theorem TreeShape.wordValues_rep (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote) (i : Fin (shape.words r)) :
    [typedValue (shape.elem r i).slotType (shape.slotWords r words i)] =
      (shape.elem r i).values (words i) :=
  (Elem.values_one _ (shape.elem_width r i) (words i)).symm

end Verified
