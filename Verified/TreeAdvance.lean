import Verified.TreeCopyStep

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def advanceRecordStore (store : Store Unit) (p : UInt64) (i : Nat) (word : UInt64) : Store Unit :=
  recordHeaderWrite { store with mem := store.mem.write64 (slotAddress p i) word }
    p 8 (UInt64.ofNat (i + 1))

theorem CopyRecord.Holds.advance {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {parent word : UInt64} {record : CopyRecord} (h : record.Holds shape heap store parent)
    (hAt : heap.At store) (hBound : record.next < record.slots.length)
    (hValue : (record.slots[record.next]).ValueOwned heap store word)
    (hSourceApart : ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      regionsDisjoint r (block store record.pointer))
    (hPrefixApart : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next),
      regionsDisjoint b (block store record.pointer))
    (hValueApart : ∀ b ∈ (record.slots[record.next]).valueBlocks store word,
      regionsDisjoint b (block store record.pointer)) :
    let store' := advanceRecordStore store record.pointer record.next word
    CopyRecord.Holds shape heap store' parent { record with next := record.next + 1 } ∧
      Step heap store (fun r => regionsDisjoint r (block store record.pointer)) heap store' [] ∧
      ({ record with next := record.next + 1 } : CopyRecord).blocks store' =
        record.blocks store ++ (record.slots[record.next]).valueBlocks store word := by
  let p := record.pointer
  let i := record.next
  let dataStore := { store with mem := store.mem.write64 (slotAddress p i) word }
  let store' := advanceRecordStore store p i word
  have hBase := h.storage.base
  have hAddress := h.storage.address
  have hCapacity := h.storage.capacity
  have hTaken : (record.slots.take i).length = i := List.length_take_of_le h.bound
  have hSlotAddress : (slotAddress p i).toNat = p.toNat + 8 * i :=
    slotAddress_toNat (by dsimp [p, i]; omega)
  have hHeaderAddress : (p - 8).toUInt32.toNat = p.toNat - 8 :=
    headerAddress_toNat (by change 8 ≤ p.toNat; dsimp [p]; omega)
      (by dsimp [p]; omega)
  have hData : Memory.WritesRange store dataStore (p.toNat + 8 * i)
      (p.toNat + 8 * i + 8) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hSlotAddress]) (by rw [hSlotAddress])
  have hHeader : Memory.WritesRange dataStore store' (p.toNat - 8) p.toNat :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hHeaderAddress])
      (by rw [hHeaderAddress]; dsimp [p]; omega)
  have hAll : Memory.WritesRange store store' (p.toNat - 8) (p.toNat + 8 * i + 8) :=
    (hData.mono (by omega) (by omega)).trans (hHeader.mono (by omega) (by omega))
  obtain ⟨hAt', hRaw', hCap⟩ := h.storage.write hAt hAll (by omega)
    (by dsimp [p]; omega) (by dsimp [p, i]; omega) (.inr (by dsimp [p]; omega))
  have hBytes (r : Nat × Nat) (hApart : regionsDisjoint r (block store p)) :
      ∀ a, r.1 ≤ a → a < r.1 + r.2 → store'.mem.bytes a = store.mem.bytes a := by
    intro a hLow hHigh
    apply hAll.2.2
    simp only [regionsDisjoint, block] at hApart
    dsimp [p, i] at *
    omega
  obtain ⟨hSource', _⟩ :=
    NodeBorrowed.frame hAt' record.source (.record record.slots) h.borrowed
      (fun r hr => ⟨hBytes r (hSourceApart r hr), NodeBorrowed.regions _ _ h.borrowed r hr⟩)
  obtain ⟨hPrefix', hPrefixBlocks⟩ := SlotsOwned.frame hAt' p 0 (record.slots.take i) h.filled
    (by dsimp [p, i] at *; omega)
    (fun a hLow hHigh =>
      (hHeader.2.2 a (.inr (by omega))).trans (hData.2.2 a (.inl (by rw [hTaken] at hHigh; omega))))
    (fun b hb => ⟨hBytes b (hPrefixApart b hb), SlotsOwned.regions p 0 _ h.filled b hb⟩)
  obtain ⟨hValue', hValueBlocks⟩ := hValue.frame hAt'
    (fun b hb => ⟨hBytes b (hValueApart b hb), hValue.regions b hb⟩)
  have hRead : store'.mem.read64 (slotAddress p i) = word := by
    rw [hHeader.read64 _ (.inr (by rw [hSlotAddress]; omega))]
    exact Memory.read64_write64 ..
  obtain ⟨hSingleton, hSingletonBlocks⟩ := hValue'.singleton hRead
  have hNextSlots : SlotsOwned heap store' p 0 (record.slots.take (i + 1)) := by
    rw [List.take_succ_eq_append_getElem hBound, SlotsOwned.append_iff]
    refine ⟨hPrefix', ?_⟩
    simpa only [List.length_take_of_le h.bound, Nat.zero_add] using hSingleton
  have hReadHeader (back : UInt64) (h16 : 16 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      store'.mem.read64 (p - back).toUInt32 = store.mem.read64 (p - back).toUInt32 := by
    apply hAll.read64
    left
    rw [headerAddress_toNat (by dsimp [p]; omega) (by dsimp [p]; omega)]
    dsimp [p, i] at *
    omega
  refine ⟨⟨h.layout, by dsimp [i] at *; omega, hRaw', hSource',
    (hReadHeader 40 (by decide) (by decide)).trans h.parent,
    (hReadHeader 24 (by decide) (by decide)).trans h.source,
    fun ht => (hReadHeader 16 (by decide) (by decide)).trans (h.width ht),
    Memory.read64_write64 .., hNextSlots⟩,
    Step.ofWritesRange hAt' hAll (by simp only [block]; dsimp [p]; omega)
      (by simp only [block]; dsimp [p, i]; omega), ?_⟩
  change block store' p :: slotsBlocks store' p 0 (record.slots.take (i + 1)) = _
  rw [List.take_succ_eq_append_getElem hBound, slotsBlocks_append,
    List.length_take_of_le h.bound, Nat.zero_add,
    hSingletonBlocks, hValueBlocks, hPrefixBlocks, block_eq hCap]
  rfl

#print axioms CopyRecord.Holds.advance

end Verified
