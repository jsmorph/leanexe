import Project.Artifact.Binary.Proof.Cursor
import Mathlib.Tactic

namespace Project.Compiler.Parsing

open Wasm.Binary

def cursor (bytes : List UInt8) (pos limit : Nat) : Cursor :=
  { bytes := ByteArray.mk bytes.toArray, pos, limit }

/-- A parser consumes exactly the given bytes at any valid position, with any
surrounding bytes and any enclosing section/body limit. -/
def Parses (parser : Parser α) (bytes : List UInt8) (value : α) : Prop :=
  ∀ (before after : List UInt8) (limit : Nat),
    before.length + bytes.length ≤ limit →
    limit ≤ before.length + bytes.length + after.length →
    parser (cursor (before ++ bytes ++ after) before.length limit) =
      .ok (value, cursor (before ++ bytes ++ after) (before.length + bytes.length) limit)

theorem pure_parses (value : α) : Parses (pure value) [] value := by
  intro before after limit _ _
  rfl

theorem bind_parses {p : Parser α} {q : α → Parser β}
    {a b : List UInt8} {x : α} {y : β}
    (first : Parses p a x) (second : Parses (q x) b y) :
    Parses (p >>= q) (a ++ b) y := by
  intro before after limit enough within
  have one := first before (b ++ after) limit (by simp_all; omega) (by simpa [List.length_append, Nat.add_assoc] using within)
  have two := second (before ++ a) after limit (by simpa [List.length_append, Nat.add_assoc] using enough)
    (by simpa [List.length_append, Nat.add_assoc] using within)
  simp only [List.append_assoc, List.length_append, Nat.add_assoc] at one two ⊢
  change Except.bind (p (cursor (before ++ (a ++ (b ++ after))) before.length limit))
    (fun pair => q pair.1 pair.2) = _
  rw [one]
  exact two

theorem map_parses {p : Parser α} {bytes : List UInt8} {value : α}
    (h : Parses p bytes value) (f : α → β) :
    Parses (p >>= fun x => pure (f x)) bytes (f value) := by
  simpa using bind_parses (q := fun x => pure (f x)) h (pure_parses (f value))

theorem read_byte (value : UInt8) : Parses Wasm.Binary.Parser.readByte [value] value := by
  intro before after limit enough within
  have available : before.length < limit := by simp at enough; omega
  simp [Wasm.Binary.Parser.readByte, cursor, available, List.getElem?_append_right,
    List.length_append]

theorem peek_byte (before after : List UInt8) (value : UInt8) (limit : Nat)
    (available : before.length < limit) :
    Wasm.Binary.Parser.peekByte (cursor (before ++ value :: after) before.length limit) =
      .ok (value, cursor (before ++ value :: after) before.length limit) := by
  simp [Wasm.Binary.Parser.peekByte, cursor, available, List.getElem?_append_right]

end Project.Compiler.Parsing
