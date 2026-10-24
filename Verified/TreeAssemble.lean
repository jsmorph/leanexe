import Verified.TreeFieldBlocks
import Verified.TreeFieldsState

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def recordSeal (width : Nat) (store : Store Unit) (ptr mask : UInt64) : Store Unit :=
  recordHeaderWrite
    (recordHeaderWrite (recordHeaderWrite store ptr 24 1) ptr 16
      (UInt64.ofNat width)) ptr 8 mask

def recordAssemble (width : Nat) (store : Store Unit) (ptr : UInt64)
    (words : List UInt64) (mask : UInt64) : Store Unit :=
  recordSeal width (recordWriteValues ptr 0 words store) ptr mask

theorem RecordStorage.seal_range {width : Nat} {heap : Heap} {store : Store Unit}
    {ptr mask : UInt64} (h : RecordStorage width heap store ptr) :
    Memory.WritesRange store (recordSeal width store ptr mask) (ptr.toNat - 24) ptr.toNat := by
  have hBase := h.base
  have hAddress := h.address
  have hAddr (back : UInt64) (hLow : 8 ≤ back.toNat) (hHigh : back.toNat ≤ 24) :
      (ptr - back).toUInt32.toNat = ptr.toNat - back.toNat :=
    headerAddress_toNat (by omega) (by omega)
  have hWrite (st : Store Unit) (back value : UInt64)
      (hLow : 8 ≤ back.toNat) (hHigh : back.toNat ≤ 24) :
      Memory.WritesRange st (recordHeaderWrite st ptr back value) (ptr.toNat - 24) ptr.toNat :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr back hLow hHigh]; omega)
      (by rw [hAddr back hLow hHigh]; omega)
  exact (hWrite store 24 1 (by decide) (by decide)).trans
    ((hWrite _ 16 (UInt64.ofNat width) (by decide) (by decide)).trans
      (hWrite _ 8 mask (by decide) (by decide)))

theorem RecordStorage.seal {width : Nat} {heap : Heap} {store : Store Unit}
    {ptr : UInt64} {slots : List LeanExe.Pipeline.Slot}
    (h : RecordStorage width heap store ptr) (hAt : heap.At store)
    (hLength : slots.length = width) (hShort : width ≤ 64)
    (hCount : store.mem.read64 (ptr - 40).toUInt32 = 1)
    (hSlots : SlotsOwned heap store ptr 0 slots)
    (hApart : (block store ptr :: slotsBlocks store ptr 0 slots).Pairwise regionsDisjoint) :
    let store' := recordSeal width store ptr (maskOf slots)
    heap.At store' ∧ NodeOwned heap store' ptr (.record slots) ∧
      Node.blocks store' ptr (.record slots) = Node.blocks store ptr (.record slots) ∧
      Step heap store (fun r => regionsDisjoint r (block store ptr)) heap store' [] := by
  have hBase := h.base
  have hAddress := h.address
  have hRoom := h.capacity
  let st3 := recordSeal width store ptr (maskOf slots)
  obtain ⟨hAt1, hRaw1, hCap1⟩ := h.writeHeader hAt (back := 24) (value := 1)
    (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hAt2, hRaw2, hCap2⟩ := hRaw1.writeHeader hAt1 (back := 16)
    (value := UInt64.ofNat width) (Or.inr (Or.inl rfl))
  obtain ⟨hAt3, hRaw3, hCap3⟩ := hRaw2.writeHeader hAt2 (back := 8) (value := maskOf slots)
    (Or.inl rfl)
  have hWrites := h.seal_range (mask := maskOf slots)
  have hCap : capacityAt st3 ptr = capacityAt store ptr := hCap3.trans (hCap2.trans hCap1)
  have hCount3 : st3.mem.read64 (ptr - 40).toUInt32 = 1 := by
    rw [hWrites.read64 _ (Or.inl (by
      rw [headerAddress_toNat (by change 40 ≤ ptr.toNat; omega) (by omega)]
      change ptr.toNat - 40 + 8 ≤ ptr.toNat - 24
      omega))]
    exact hCount
  have hKind3 : st3.mem.read64 (ptr - 24).toUInt32 = 1 := by
    dsimp only [st3, recordSeal]
    rw [hRaw2.readHeader_write (value := maskOf slots) (Or.inl rfl)
      (Or.inr (Or.inr (Or.inl rfl))) (by decide),
      hRaw1.readHeader_write (value := UInt64.ofNat width)
        (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (by decide)]
    exact Memory.read64_write64 ..
  have hWidth3 : st3.mem.read64 (ptr - 16).toUInt32 = UInt64.ofNat width := by
    dsimp only [st3, recordSeal]
    rw [hRaw2.readHeader_write (value := maskOf slots) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (by decide)]
    exact Memory.read64_write64 ..
  have hMask3 : st3.mem.read64 (ptr - 8).toUInt32 = maskOf slots := Memory.read64_write64 ..
  obtain ⟨hSlots3, hBlocks3⟩ := SlotsOwned.frame ptr 0 slots hSlots (by omega)
    (fun a ha _ => hWrites.2.2 a (Or.inr (by omega)))
    (fun b hb => ⟨fun a ha hHigh => hWrites.2.2 a (by
      have := (List.pairwise_cons.mp hApart).1 b hb
      simp only [regionsDisjoint, block] at this
      omega), SlotsOwned.regions ptr 0 slots hSlots b hb⟩)
  refine ⟨hAt3, hRaw3.record hLength hCount3 hKind3 hWidth3 hMask3 hShort hSlots3, ?_,
    Step.ofWritesRange hAt3 hWrites (by simp only [block]; omega)
      (by simp only [block]; omega)⟩
  change block st3 ptr :: slotsBlocks st3 ptr 0 slots = _
  rw [block_eq hCap, hBlocks3]
  rfl

theorem RecordStorage.assemble {width : Nat} {heap : Heap} {store : Store Unit}
    {ptr : UInt64} {words : List UInt64} {slots : List LeanExe.Pipeline.Slot}
    (h : RecordStorage width heap store ptr) (hAt : heap.At store)
    (hLength : words.length = width) (hShort : width ≤ 64)
    (hCount : store.mem.read64 (ptr - 40).toUInt32 = 1)
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots)
    (hApart : (block store ptr :: fieldBlocks store words slots).Pairwise regionsDisjoint) :
    let store' := recordAssemble width store ptr words (maskOf slots)
    heap.At store' ∧ NodeOwned heap store' ptr (.record slots) ∧
      Node.blocks store' ptr (.record slots) = block store ptr :: fieldBlocks store words slots ∧
      Step heap store (fun r => regionsDisjoint r (block store ptr)) heap store' [] := by
  have hBase := h.base
  have hAddress := h.address
  have hRoom := h.capacity
  let st := recordWriteValues ptr 0 words store
  obtain ⟨hAt1, hRaw1, hCap1, hStep1⟩ := h.writeValues hAt 0 words (by omega)
  have hWrites := recordWriteValues_range ptr 0 words store (by omega)
  obtain ⟨hValues1, hBlocks1⟩ := fieldValues_frame hValues
    (fun b hb => ⟨fun a ha hHigh => hWrites.2.2 a (by
      have := (List.pairwise_cons.mp hApart).1 b hb
      simp only [regionsDisjoint, block] at this
      omega), fieldValues_regions hValues b hb⟩)
  have hReads := recordWriteValues_read ptr 0 words store (by omega)
  have hSlots1 := slotsOwned_of_values ptr 0 words slots hValues1 hReads
  have hSlotBlocks := slotsBlocks_of_values ptr 0 words slots hValues1 hReads
  have hCount1 : st.mem.read64 (ptr - 40).toUInt32 = 1 :=
    (h.writeValues_header 0 words (by omega) 40 (by decide) (by decide)).trans hCount
  have hApart1 : (block st ptr :: slotsBlocks st ptr 0 slots).Pairwise regionsDisjoint := by
    rw [block_eq hCap1, hSlotBlocks, hBlocks1]
    exact hApart
  obtain ⟨hAt2, hNode2, hBlocks2, hStep2⟩ := hRaw1.seal hAt1
    (by rw [← hLength]; exact hValues.length_eq.symm) hShort hCount1 hSlots1 hApart1
  refine ⟨hAt2, hNode2, ?_, ?_⟩
  · change Node.blocks (recordSeal width (recordWriteValues ptr 0 words store) ptr (maskOf slots))
      ptr (.record slots) = _
    rw [hBlocks2]
    change block st ptr :: slotsBlocks st ptr 0 slots = _
    rw [block_eq hCap1, hSlotBlocks, hBlocks1]
  · have hStep2' : Step heap st (fun r => regionsDisjoint r (block store ptr)) heap
        (recordSeal width st ptr (maskOf slots)) [] := by
      simpa only [block_eq hCap1] using hStep2
    simpa only [recordAssemble, st, List.nil_append] using
      hStep1.trans hStep2' (fun _ hr => ⟨hr, fun _ => hr⟩)

end Verified
