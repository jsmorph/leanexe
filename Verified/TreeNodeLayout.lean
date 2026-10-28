import Verified.TreeLayout
import Verified.TreeCopyWork

namespace Verified

open LeanExe.Pipeline

mutual
theorem Node.blocks_length (store : Wasm.Store Unit) (ptr : UInt64) :
    (value : Node) → (value.blocks store ptr).length = value.records
  | .null => rfl
  | .record slots => by
    simp only [Node.blocks, List.length_cons, Node.records, slotsBlocks_length]
    omega

theorem slotsBlocks_length (store : Wasm.Store Unit) (ptr : UInt64) (i : Nat) :
    (slots : List Slot) → (slotsBlocks store ptr i slots).length = slotsRecords slots
  | [] => rfl
  | .word _ :: rest => slotsBlocks_length store ptr (i + 1) rest
  | .child value :: rest => by
    simp only [slotsBlocks, List.length_append, Node.blocks_length, slotsBlocks_length, slotsRecords]
  | .array _ :: rest => by
    simp only [slotsBlocks, List.length_cons, slotsBlocks_length, slotsRecords]
    omega
  | .bytes data :: rest => by
    simp only [slotsBlocks, List.length_append, List.length_map, slotsBlocks_length, slotsRecords]
    unfold bufferRoots
    split <;> rfl
end

mutual
def NodeLayout (shape : TreeShape) : Node → Prop
  | .null => True
  | .record slots => ∃ r, slots.length = shape.width r ∧ maskOf slots = shape.mask r ∧
      slots.take (shape.tagSlots r).length = shape.tagSlots r ∧ SlotsLayout shape slots ∧
      arrayMaskOf slots = shape.arrayMask r

def SlotsLayout (shape : TreeShape) : List Slot → Prop
  | [] => True
  | .word _ :: rest => SlotsLayout shape rest
  | .child value :: rest => NodeLayout shape value ∧ SlotsLayout shape rest
  | .array _ :: rest => SlotsLayout shape rest
  | .bytes _ :: _ => False
end

mutual
theorem NodeLayout.slotted {shape : TreeShape} :
    ∀ {value : Node}, NodeLayout shape value → value.Slotted
  | .null, _ => trivial
  | .record slots, h => by
    obtain ⟨r, hLength, -, -, hSlots, -⟩ := h
    refine ⟨?_, SlotsLayout.slotted (slots := slots) hSlots⟩
    intro hEmpty
    rw [hEmpty] at hLength
    exact absurd hLength.symm (Nat.ne_of_gt (shape.width_pos r))

theorem SlotsLayout.slotted {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots → slotsSlotted slots
  | [], _ => trivial
  | .word _ :: rest, h => SlotsLayout.slotted (slots := rest) h
  | .child value :: rest, h =>
    ⟨NodeLayout.slotted (value := value) h.1, SlotsLayout.slotted (slots := rest) h.2⟩
  | .array _ :: rest, h => SlotsLayout.slotted (slots := rest) h
  | .bytes _ :: _, h => False.elim h
end

theorem treeSlots_layout (shape : TreeShape) (fields : List Bool) :
    ∀ words children, (∀ i, NodeLayout shape (children i)) →
      SlotsLayout shape (treeSlots fields words children) := by
  induction fields with
  | nil => intros; trivial
  | cons bit rest ih =>
    cases bit <;> intro words children hc <;> simp only [treeSlots, SlotsLayout]
    · exact ih _ _ (fun i => hc _)
    · exact ⟨hc _, ih _ _ (fun i => hc _)⟩

theorem tagSlots_layout (shape : TreeShape) (r : Fin shape.records) (rest : List Slot)
    (h : SlotsLayout shape rest) : SlotsLayout shape (shape.tagSlots r ++ rest) := by
  unfold TreeShape.tagSlots
  split
  · exact h
  · exact h

theorem SlotsLayout.append {shape : TreeShape} :
    ∀ {first second : List Slot}, SlotsLayout shape first → SlotsLayout shape second →
      SlotsLayout shape (first ++ second)
  | [], _, _, h => h
  | .word _ :: rest, _, h1, h2 => SlotsLayout.append (first := rest) h1 h2
  | .child _ :: rest, _, h1, h2 => ⟨h1.1, SlotsLayout.append (first := rest) h1.2 h2⟩
  | .array _ :: rest, _, h1, h2 => SlotsLayout.append (first := rest) h1 h2
  | .bytes _ :: _, _, h1, _ => False.elim h1

/-- The array slots of fields none of which is a buffer have the copy loop's layout. -/
theorem heapSlots_layout (shape : TreeShape) (fields : List TreeField)
    (hNoBytes : fields.count .bytes = 0) :
    ∀ arrays buffers, SlotsLayout shape (heapSlots fields arrays buffers) := by
  induction fields with
  | nil => intros; trivial
  | cons field rest ih =>
    intro arrays buffers
    cases field with
    | word e => exact ih (by simpa using hNoBytes) _ _
    | child => exact ih (by simpa using hNoBytes) _ _
    | array e => exact ih (by simpa using hNoBytes) _ _
    | bytes => simp at hNoBytes

/-- The records of a value have the copy loop's layout. -/
theorem Tree.toNode_layout {shape : TreeShape} (value : Tree shape) :
    NodeLayout shape value.toNode := by
  induction value with
  | nil => trivial
  | node r words arrays buffers children ih =>
    refine ⟨r, shape.recordSlots_length .., shape.mask_eq .., by simp [TreeShape.recordSlots], ?_,
      shape.arrayMask_eq ..⟩
    show SlotsLayout shape (shape.tagSlots r ++ treeSlots (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers)
    rw [List.append_assoc]
    exact tagSlots_layout shape r _ (SlotsLayout.append (treeSlots_layout shape _ _ _ ih)
      (heapSlots_layout shape _ (shape.buffers_eq_zero r) _ _))

theorem SlotsLayout.child {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots →
      ∀ i (hi : i < slots.length) value, slots[i] = .child value → NodeLayout shape value
  | [], _, i, hi, _, _ => by simp at hi
  | .word _ :: rest, h, 0, _, _, he => by cases he
  | .word _ :: rest, h, i + 1, hi, value, he =>
    SlotsLayout.child (slots := rest) h i (by simpa using hi) value he
  | .child _ :: _, h, 0, _, _, he => by cases he; exact h.1
  | .child _ :: rest, h, i + 1, hi, value, he =>
    SlotsLayout.child (slots := rest) h.2 i (by simpa using hi) value he
  | .array _ :: _, _, 0, _, _, he => by cases he
  | .array _ :: rest, h, i + 1, hi, value, he =>
    SlotsLayout.child (slots := rest) h i (by simpa using hi) value he
  | .bytes _ :: _, h, _, _, _, _ => False.elim h

theorem SlotsLayout.lengths {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots → BufferLengths slots
  | [], _ => trivial
  | .word _ :: rest, h => SlotsLayout.lengths (slots := rest) h
  | .child _ :: rest, h => SlotsLayout.lengths (slots := rest) h.2
  | .array _ :: rest, h => SlotsLayout.lengths (slots := rest) h
  | .bytes _ :: _, h => False.elim h

theorem NodeLayout.lengths {shape : TreeShape} {slots : List Slot}
    (h : NodeLayout shape (.record slots)) : BufferLengths slots := by
  obtain ⟨_, -, -, -, hSlots, -⟩ := h
  exact SlotsLayout.lengths hSlots

/-- No slot of a record laid out by a shape is a buffer. -/
theorem SlotsLayout.not_bytes {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots → ∀ i (hi : i < slots.length) data,
      slots[i] ≠ .bytes data
  | [], _, i, hi, _ => by simp at hi
  | .word _ :: _, _, 0, _, _ => nofun
  | .word _ :: rest, h, i + 1, hi, data =>
    SlotsLayout.not_bytes (slots := rest) h i (by simpa using hi) data
  | .child _ :: _, _, 0, _, _ => nofun
  | .child _ :: rest, h, i + 1, hi, data =>
    SlotsLayout.not_bytes (slots := rest) h.2 i (by simpa using hi) data
  | .array _ :: _, _, 0, _, _ => nofun
  | .array _ :: rest, h, i + 1, hi, data =>
    SlotsLayout.not_bytes (slots := rest) h i (by simpa using hi) data
  | .bytes _ :: _, h, _, _, _ => False.elim h

theorem _root_.LeanExe.Pipeline.Slot.arrayBit_le (s : Slot) : s.arrayBit.toNat ≤ 1 := by
  cases s <;> simp [Slot.arrayBit]

/-- The array mask of at most 64 slots is below `2 ^ length`, and its bit `i` is slot `i`'s array
bit. -/
theorem arrayMaskOf_toNat : ∀ (slots : List Slot), slots.length ≤ 64 →
    (arrayMaskOf slots).toNat < 2 ^ slots.length ∧
    ∀ i (h : i < slots.length), (arrayMaskOf slots).toNat / 2 ^ i % 2 = (slots[i].arrayBit).toNat
  | [], _ => ⟨by decide, fun i h => absurd h (by simp)⟩
  | s :: rest, hLen => by
      simp only [List.length_cons] at hLen
      obtain ⟨hLt, hBits⟩ := arrayMaskOf_toNat rest (by omega)
      have hb := Slot.arrayBit_le s
      have hPow : 2 ^ rest.length ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have hEq : (arrayMaskOf (s :: rest)).toNat =
          2 * (arrayMaskOf rest).toNat + s.arrayBit.toNat := by
        change (2 * arrayMaskOf rest + s.arrayBit).toNat = _
        rw [UInt64.toNat_add, UInt64.toNat_mul]
        have : (2 : UInt64).toNat = 2 := rfl
        rw [this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      refine ⟨by rw [hEq, List.length_cons, Nat.pow_succ]; omega, fun i h => ?_⟩
      rw [hEq]
      cases i with
      | zero => simp; omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [← hBits j (by simp at h; omega), Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        congr 2
        omega

/-- The copy loop's array test for slot `i`, a shift by `i` modulo 64 and a mask of the low bit,
reads the slot's array bit. -/
theorem arrayMaskOf_test (slots : List Slot) (hLen : slots.length ≤ 64) (i : Nat)
    (h : i < slots.length) :
    ((arrayMaskOf slots >>> (UInt64.ofNat i % 64)) &&& 1) = slots[i].arrayBit := by
  obtain ⟨-, hBits⟩ := arrayMaskOf_toNat slots hLen
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hi : (UInt64.ofNat i % 64).toNat % 64 = i := by
    rw [UInt64.toNat_mod, UInt64.toNat_ofNat']
    have : (64 : UInt64).toNat = 64 := rfl
    rw [this]
    omega
  rw [hi, Nat.shiftRight_eq_div_pow]
  have : (1 : UInt64).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod, hBits i h]

/-- A record of a shape without array fields has no array slot. -/
theorem NodeLayout.not_array {shape : TreeShape} {slots : List Slot}
    (h : NodeLayout shape (.record slots)) (hNone : shape.hasArrays = false) (i : Nat)
    (hi : i < slots.length) (words : Array UInt64) : slots[i] ≠ .array words := by
  obtain ⟨r, hLength, -, -, -, hArrays⟩ := h
  intro hSlot
  have hBit := arrayMaskOf_test slots (by rw [hLength]; exact shape.width_le r) i hi
  rw [hArrays, shape.arrayMask_zero hNone r, hSlot] at hBit
  simp [Slot.arrayBit] at hBit

theorem treeSlots_records (fields : List Bool) :
    ∀ words children, slotsRecords (treeSlots fields words children) =
      (List.ofFn fun i => (children i).records).sum := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro words children
    cases bit
    · simp only [treeSlots, slotsRecords]
      rw [ih]
      rfl
    · simp only [treeSlots, slotsRecords]
      rw [ih]
      simp only [List.count_cons, beq_self_eq_true, ite_true, List.ofFn_succ, List.sum_cons]
      rfl

theorem slotsRecords_append : ∀ (s t : List Slot),
    slotsRecords (s ++ t) = slotsRecords s + slotsRecords t
  | [], _ => by simp [slotsRecords]
  | .word _ :: rest, t => by
    simp only [List.cons_append, slotsRecords]
    exact slotsRecords_append rest t
  | .child _ :: rest, t => by
    simp only [List.cons_append, slotsRecords, slotsRecords_append rest t]
    omega
  | .array _ :: rest, t => by
    simp only [List.cons_append, slotsRecords, slotsRecords_append rest t]
    omega
  | .bytes _ :: rest, t => by
    simp only [List.cons_append, slotsRecords, slotsRecords_append rest t]
    omega

theorem tagSlots_records (shape : TreeShape) (r : Fin shape.records) (words arrays buffers
    children) :
    slotsRecords (shape.recordSlots r words arrays buffers children) =
      slotsRecords (treeSlots (shape.fields r) words children) +
        slotsRecords (heapSlots (shape.kinds r) arrays buffers) := by
  unfold TreeShape.recordSlots
  rw [slotsRecords_append, slotsRecords_append]
  unfold TreeShape.tagSlots
  split <;> simp [slotsRecords]

private theorem records_arith {x a b c : Nat} (h1 : x = a + b) (h2 : a = c) :
    1 + x = 1 + b + c := by
  omega

theorem Tree.toNode_records {shape : TreeShape} (value : Tree shape) :
    value.toNode.records = value.nodes := by
  induction value with
  | nil => rfl
  | node r words arrays buffers children ih =>
    change 1 + slotsRecords (shape.recordSlots r (shape.slotWords r words)
        (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)) =
      1 + slotsRecords (heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) +
        (List.ofFn fun i => (children i).nodes).sum
    exact records_arith (tagSlots_records shape r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))
      ((treeSlots_records (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode)).trans
        (congrArg (fun f : Fin (shape.children r) → Nat => (List.ofFn f).sum) (funext ih)))

theorem treeSlots_copyCost (fields : List Bool) :
    ∀ words children, slotsCopyCost (treeSlots fields words children) =
      (List.ofFn fun i => nodeCopyCost (children i)).sum := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro words children
    cases bit
    · simp only [treeSlots, slotsCopyCost]
      rw [ih]
      rfl
    · simp only [treeSlots, slotsCopyCost]
      rw [ih]
      simp only [List.count_cons, beq_self_eq_true, ite_true, List.ofFn_succ, List.sum_cons]
      rfl

theorem slotsCopyCost_append : ∀ (s t : List Slot),
    slotsCopyCost (s ++ t) = slotsCopyCost s + slotsCopyCost t
  | [], _ => by simp [slotsCopyCost]
  | .word _ :: rest, t => by
    simp only [List.cons_append, slotsCopyCost]
    exact slotsCopyCost_append rest t
  | .child _ :: rest, t => by
    simp only [List.cons_append, slotsCopyCost, slotsCopyCost_append rest t]
    omega
  | .array _ :: rest, t => by
    simp only [List.cons_append, slotsCopyCost, slotsCopyCost_append rest t]
    omega
  | .bytes _ :: rest, t => by
    simp only [List.cons_append, slotsCopyCost, slotsCopyCost_append rest t]
    omega

theorem tagSlots_copyCost (shape : TreeShape) (r : Fin shape.records) (words arrays buffers
    children) :
    slotsCopyCost (shape.recordSlots r words arrays buffers children) =
      slotsCopyCost (treeSlots (shape.fields r) words children) +
        slotsCopyCost (heapSlots (shape.kinds r) arrays buffers) := by
  unfold TreeShape.recordSlots
  rw [slotsCopyCost_append, slotsCopyCost_append]
  unfold TreeShape.tagSlots
  split <;> simp [slotsCopyCost]

private theorem copyCost_arith {k x a b c d : Nat} (h1 : x = a + b) (h2 : a = c)
    (h3 : d = c) : k + b + d = k + x := by
  omega

theorem Tree.copyCost_eq {shape : TreeShape} (value : Tree shape) :
    value.copyCost = nodeCopyCost value.toNode := by
  induction value with
  | nil => rfl
  | node r words arrays buffers children ih =>
    change allocCost (8 * shape.width r) +
        slotsCopyCost (heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) +
        (List.ofFn fun i => (children i).copyCost).sum =
      allocCost (8 * (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays)
          buffers (fun i => (children i).toNode)).length) +
        slotsCopyCost (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays)
          buffers (fun i => (children i).toNode))
    rw [shape.recordSlots_length]
    exact copyCost_arith (tagSlots_copyCost shape r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))
      (treeSlots_copyCost (shape.fields r) (shape.slotWords r words)
        (fun i => (children i).toNode))
      (congrArg (fun f : Fin (shape.children r) → Nat => (List.ofFn f).sum) (funext ih))

#print axioms Tree.toNode_layout
#print axioms Tree.toNode_records
#print axioms Tree.copyCost_eq
#print axioms NodeLayout.slotted
#print axioms SlotsLayout.not_bytes
#print axioms arrayMaskOf_test

end Verified
