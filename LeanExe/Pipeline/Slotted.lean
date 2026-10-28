import LeanExe.Pipeline.Implements

/-! Every record of an encoded value has at least one slot, so every slot region has positive
length, which `Heap.Keeps.nodeBorrowed` requires.  The compiler builds records only for the
constructor with fields of a recursive type, so each encoding it matches has the property.

`RecordHeader` and `RecordSlots` also have conditions on the value alone: a record has at most
64 slots, and a word slot that holds a buffer's length follows each buffer slot.  An encoding
that breaks either condition makes `Represent.borrowed` and `Represent.owned` false for its
values in every store, so an `Implements` statement over its type holds for every module.
`EncodeWellFormed` states the two conditions for every record of every value of a type, which
rules this out. -/

namespace LeanExe.Pipeline

open Wasm

mutual
/-- Every record of `n` has at least one slot. -/
def Node.Slotted : Node → Prop
  | .null => True
  | .record slots => slots ≠ [] ∧ slotsSlotted slots

/-- Every record of the children among `slots` has at least one slot. -/
def slotsSlotted : List Slot → Prop
  | [] => True
  | .word _ :: rest => slotsSlotted rest
  | .child n :: rest => n.Slotted ∧ slotsSlotted rest
  | .array _ :: rest => slotsSlotted rest
  | .bytes _ :: rest => slotsSlotted rest
end

mutual
theorem Node.slotted_pos (store : Store Unit) :
    ∀ (p : UInt64) (n : Node), n.Slotted → ∀ b ∈ n.slotRegions store p, 0 < b.2
  | _, .null, _, _, hb => nomatch hb
  | p, .record slots, h, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · have := List.length_pos_of_ne_nil h.1
        show 0 < 8 * slots.length
        omega
      · exact slotsSlotted_pos store p 0 slots h.2 b hb

theorem slotsSlotted_pos (store : Store Unit) :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), slotsSlotted slots →
      ∀ b ∈ slotsRegions store p i slots, 0 < b.2
  | _, _, [], _, _, hb => nomatch hb
  | p, i, .word _ :: rest, h, b, hb => slotsSlotted_pos store p (i + 1) rest h b hb
  | p, i, .child n :: rest, h, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact Node.slotted_pos store _ n h.1 b hb
      · exact slotsSlotted_pos store p (i + 1) rest h.2 b hb
  | p, i, .array words :: rest, h, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · show 0 < 8 * (words.size + 1)
        omega
      · exact slotsSlotted_pos store p (i + 1) rest h b hb
  | p, i, .bytes _ :: rest, h, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hb
        show 0 < 48 + capacityAt store q
        omega
      · exact slotsSlotted_pos store p (i + 1) rest h b hb
end

/-- Every slot region of a value whose records have slots has positive length. -/
theorem Node.slotRegions_pos {store : Store Unit} {p : UInt64} {n : Node} (h : n.Slotted) :
    ∀ b ∈ n.slotRegions store p, 0 < b.2 :=
  Node.slotted_pos store p n h

/-- An encoding whose records all have at least one slot. -/
class EncodeSlotted (α : Type) [Encode α] : Prop where
  slotted : ∀ x : α, (Encode.encode x).Slotted

/-- Every slot region of an encoded value has positive length. -/
theorem EncodeSlotted.slotRegions_pos [Encode α] [EncodeSlotted α] (x : α) {store : Store Unit}
    {p : UInt64} : ∀ b ∈ (Encode.encode x).slotRegions store p, 0 < b.2 :=
  Node.slotRegions_pos (EncodeSlotted.slotted x)

theorem encodeList_slotted : ∀ xs : List UInt64, (encodeList xs).Slotted
  | [] => trivial
  | _ :: xs => ⟨List.cons_ne_nil _ _, encodeList_slotted xs, trivial⟩

instance : EncodeSlotted (List UInt64) := ⟨encodeList_slotted⟩

mutual
/-- Every record of `n` has at most 64 slots, and each of its buffer slots is followed by a word
slot that holds the buffer's length: the conditions of `RecordHeader` and `RecordSlots` that
depend on the value alone. -/
def Node.WellFormed : Node → Prop
  | .null => True
  | .record slots => slots.length ≤ 64 ∧ BufferLengths slots ∧ slotsWellFormed slots

/-- Every record of the children among `slots` is well formed. -/
def slotsWellFormed : List Slot → Prop
  | [] => True
  | .word _ :: rest => slotsWellFormed rest
  | .child n :: rest => n.WellFormed ∧ slotsWellFormed rest
  | .array _ :: rest => slotsWellFormed rest
  | .bytes _ :: rest => slotsWellFormed rest
end

/-- An encoding whose records all meet the conditions of `RecordHeader` and `RecordSlots` that
depend on the value alone. -/
class EncodeWellFormed (α : Type) [Encode α] : Prop where
  wellFormed : ∀ x : α, (Encode.encode x).WellFormed

theorem encodeList_wellFormed : ∀ xs : List UInt64, (encodeList xs).WellFormed
  | [] => trivial
  | _ :: xs => ⟨by simp, trivial, encodeList_wellFormed xs, trivial⟩

instance : EncodeWellFormed (List UInt64) := ⟨encodeList_wellFormed⟩

end LeanExe.Pipeline
