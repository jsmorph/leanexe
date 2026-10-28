/-! The element types of the verified compiler's source language: the values that hold no
arrays and that an array, a tuple, or a word slot of a record may hold. -/

namespace Verified

/-- The types of the values that hold no arrays and that an array may hold: words, `Bool`s,
floats, and tuples of these. -/
inductive Elem where
  | word | bool | float | float32
  | prod (first second : Elem)
  deriving Repr, DecidableEq, Inhabited

/-- The Lean type of an element. -/
abbrev Elem.denote : Elem → Type
  | .word => UInt64
  | .bool => Bool
  | .float => Float
  | .float32 => Float32
  | .prod a b => a.denote × b.denote

/-- Lean's default value of an element type, which a read past the end of an array gives. -/
instance Elem.instInhabited : (e : Elem) → Inhabited e.denote
  | .word => inferInstanceAs (Inhabited UInt64)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .float => inferInstanceAs (Inhabited Float)
  | .float32 => inferInstanceAs (Inhabited Float32)
  | .prod a b => ⟨(@default _ a.instInhabited, @default _ b.instInhabited)⟩

/-- The word that holds a `Bool`: 1 or 0, as `Implements` passes a `Bool`. -/
def boolWord (b : Bool) : UInt64 := cond b 1 0

/-- The number of words that hold an element. -/
def Elem.width : Elem → Nat
  | .word | .bool | .float | .float32 => 1
  | .prod a b => a.width + b.width

@[simp] theorem Elem.width_word : Elem.width .word = 1 := rfl
@[simp] theorem Elem.width_bool : Elem.width .bool = 1 := rfl
@[simp] theorem Elem.width_float : Elem.width .float = 1 := rfl
@[simp] theorem Elem.width_float32 : Elem.width .float32 = 1 := rfl

/-- The words that hold an element in an array, in order: a word as itself, a `Bool` as 1 or 0,
a float as its bit pattern, and a tuple as its first part's words followed by its second's. -/
def Elem.toWords : (e : Elem) → e.denote → List UInt64
  | .word, x => [x]
  | .bool, b => [boolWord b]
  | .float, x => [x.toBits]
  | .float32, x => [x.toBits.toUInt64]
  | .prod a b, v => a.toWords v.1 ++ b.toWords v.2

/-- The word of an element of one word: a word as itself, a `Bool` as 1 or 0, and a float as its
bit pattern, a binary32 pattern in the low 32 bits.  A tuple has no single word. -/
def Elem.slotWord : (e : Elem) → e.denote → UInt64
  | .word, x => x
  | .bool, b => boolWord b
  | .float, x => x.toBits
  | .float32, x => x.toBits.toUInt64
  | .prod _ _, _ => 0

private theorem Elem.one_le_width : (e : Elem) → 1 ≤ e.width
  | .word | .bool | .float | .float32 => Nat.le_refl 1
  | .prod a b => Nat.le_trans a.one_le_width (Nat.le_add_right _ _)

theorem Elem.toWords_slotWord : (e : Elem) → e.width = 1 → (v : e.denote) →
    e.toWords v = [e.slotWord v]
  | .word, _, _ | .bool, _, _ | .float, _, _ | .float32, _, _ => rfl
  | .prod a b, h, _ => by
    have ha := a.one_le_width
    have hb := b.one_le_width
    simp only [Elem.width] at h
    omega

end Verified
