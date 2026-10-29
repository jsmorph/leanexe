import Verified.LocalFrame
import Verified.TreeCopyCode
import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- `code` pushes the word `v` onto any operand stack of the locals `s` at the store `store`, and
changes nothing else. -/
def PushesWord (m : Module) (host : HostEnv Unit) (code : Program) (store : Store Unit)
    (s : Locals) (v : UInt64) : Prop :=
  ∀ (vs : List Value) (rest : Program) (Q : Assertion Unit),
    wp m rest Q store { s with values := .i64 v :: vs } host →
      wp m (code ++ rest) Q store { s with values := vs } host

theorem PushesWord.const {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {v : UInt64} : PushesWord m host [.constI64 v] store s v := by
  intro vs rest Q h
  simpa only [List.singleton_append, wp_constI64_cons] using h

theorem PushesWord.selectChain {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {tag : Program} {t : UInt64} (hTag : PushesWord m host tag store s t) :
    ∀ pairs : List (UInt64 × UInt64),
      PushesWord m host (Verified.selectChain tag pairs) store s (chainPick t 0 pairs)
  | [] => PushesWord.const
  | [(_, _)] => PushesWord.const
  | (i, v) :: p :: rest => by
    intro vs code Q h
    have hRest := PushesWord.selectChain hTag (p :: rest)
    rw [Verified.selectChain, List.append_assoc]
    apply hTag
    simp only [List.cons_append, List.nil_append, wp_constI64_cons, wp_eqI64_cons,
      wp_iff_control_types]
    apply wp_iff_cons rfl
    rw [chainPick] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      simpa [wp_constI64_cons] using h
    · rw [ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0),
        ← List.append_nil (Verified.selectChain tag (p :: rest))]
      apply hRest vs []
      simpa using h

/-- `selectCode` pushes the entry of record constructor `r` when the tag code pushes `t` and, for a
tagged shape, `t` is `r`'s tag. -/
theorem PushesWord.selectCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} (r : Fin shape.records) {tag : Program} {t : UInt64}
    (value : Fin shape.records → UInt64) (hTag : PushesWord m host tag store s t)
    (ht : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r)) :
    PushesWord m host (shape.selectCode tag value) store s (value r) := by
  have h := PushesWord.selectChain hTag (shape.tagPairs value)
  rwa [shape.chainPick_tag r value 0 t ht] at h

theorem TreeShape.selectCode_untagged (shape : TreeShape) (h : shape.tagged = false)
    (r : Fin shape.records) (tag : Program) (value : Fin shape.records → UInt64) :
    shape.selectCode tag value = [.constI64 (value r)] := by
  have hOne : shape.records = 1 := by
    simp only [TreeShape.tagged, decide_eq_false_iff_not, Nat.not_lt] at h
    have := r.isLt
    omega
  have hMem : (UInt64.ofNat (shape.ctorIndex r), value r) ∈ shape.tagPairs value :=
    List.mem_map.mpr ⟨r, List.mem_finRange r, rfl⟩
  have hLength : (shape.tagPairs value).length = 1 := by
    simp only [TreeShape.tagPairs, List.length_map, List.length_finRange, hOne]
  unfold TreeShape.selectCode
  match hPairs : shape.tagPairs value, hLength with
  | [(i, y)], _ =>
    rw [hPairs] at hMem
    simp only [List.mem_singleton, Prod.mk.injEq] at hMem
    rw [hMem.2]
    rfl

/-- A record whose slots begin with the tag slots of record constructor `r` holds `r`'s tag in
slot 0 when the shape is tagged. -/
theorem tagSlots_head {shape : TreeShape} {r : Fin shape.records} {slots : List Slot}
    (hPrefix : slots.take (shape.tagSlots r).length = shape.tagSlots r)
    (ht : shape.tagged = true) :
    ∃ rest, slots = .word (UInt64.ofNat (shape.ctorIndex r)) :: rest := by
  rw [TreeShape.tagSlots, ite_eq_left ht] at hPrefix
  cases slots with
  | nil => simp at hPrefix
  | cons slot rest =>
    simp only [List.length_singleton, List.take_succ_cons, List.take_zero, List.cons.injEq,
      and_true] at hPrefix
    exact ⟨rest, by rw [hPrefix]⟩

theorem NodeBorrowed.tag {heap : Heap} {store : Store Unit} {q : UInt64} {slots : List Slot}
    {shape : TreeShape} {r : Fin shape.records} (hNode : NodeBorrowed heap store q (.record slots))
    (hPrefix : slots.take (shape.tagSlots r).length = shape.tagSlots r)
    (ht : shape.tagged = true) :
    store.mem.read64 q.toUInt32 = UInt64.ofNat (shape.ctorIndex r) := by
  obtain ⟨rest, rfl⟩ := tagSlots_head hPrefix ht
  simp only [NodeBorrowed, SlotsBorrowed] at hNode
  simpa [slotAddress] using hNode.2.1

theorem SlotsOwned.tag {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    {shape : TreeShape} {r : Fin shape.records} (hSlots : SlotsOwned heap store p 0 slots)
    (hPrefix : slots.take (shape.tagSlots r).length = shape.tagSlots r)
    (ht : shape.tagged = true) :
    store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r) := by
  obtain ⟨rest, rfl⟩ := tagSlots_head hPrefix ht
  simp only [SlotsOwned] at hSlots
  simpa [slotAddress] using hSlots.1

/-- The tag of a borrowed record lies in memory. -/
theorem NodeBorrowed.tagRoom {heap : Heap} {store : Store Unit} {q : UInt64} {slots : List Slot}
    (hNode : NodeBorrowed heap store q (.record slots)) (hHeap : heap.At store)
    (hSlotted : slots ≠ []) :
    q.toUInt32.toNat = q.toNat ∧ q.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
  simp only [NodeBorrowed] at hNode
  have hAddress := hNode.1.address
  have hBelow := hNode.1.below
  have hTop := hHeap.top
  have hLength : 1 ≤ slots.length := List.length_pos_of_ne_nil hSlotted
  have hNat : q.toUInt32.toNat = q.toNat := by
    rw [UInt64.toNat_toUInt32]
    omega
  exact ⟨hNat, by omega⟩

/-- The header writes of a record leave its slot 0 unchanged. -/
theorem RecordStorage.readSlot_write {width : Nat} {heap : Heap} {store : Store Unit}
    {p back value : UInt64} (h : RecordStorage width heap store p)
    (hBack : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 40) :
    (recordHeaderWrite store p back value).mem.read64 p.toUInt32 = store.mem.read64 p.toUInt32 := by
  have hBase := h.base
  have hAddress := h.address
  have hRange := h.writeHeader_range (value := value) hBack
  apply hRange.read64
  right
  rw [UInt64.toNat_toUInt32]
  omega

#print axioms PushesWord.selectChain
#print axioms PushesWord.selectCode
#print axioms TreeShape.selectCode_untagged
#print axioms NodeBorrowed.tag
#print axioms SlotsOwned.tag
#print axioms NodeBorrowed.tagRoom
#print axioms RecordStorage.readSlot_write

end Verified
