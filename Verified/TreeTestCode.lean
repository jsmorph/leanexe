import Verified.TreeCopyState
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def treeCopyCondition (mask : UInt64) (i : Nat) (word : UInt64) : UInt32 :=
  (if ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 then 0 else 1) &&&
    (if word = 0 then 0 else 1)

def copyBranch : LeanExe.Pipeline.Slot → UInt32
  | .child (.record _) => 1
  | _ => 0

theorem treeCopyCondition_spec {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {parent : UInt64} {record : CopyRecord} (h : record.Holds shape heap store parent)
    (hBound : record.next < record.slots.length) :
    treeCopyCondition (maskOf record.slots) record.next
      (store.mem.read64 (slotAddress record.source record.next)) =
      copyBranch record.slots[record.next] := by
  obtain ⟨r, hLength, -, -, -⟩ := id h.layout
  have hBit : ((maskOf record.slots >>> (UInt64.ofNat record.next % 64)) &&& 1) =
      record.slots[record.next].bit :=
    maskOf_test _ (by rw [hLength]; exact shape.width_le r) _ hBound
  have hBorrow := SlotsBorrowed.get record.slots 0 h.borrowed.2 record.next hBound
  simp only [Nat.zero_add] at hBorrow
  cases hSlot : record.slots[record.next] with
  | word value => simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch]
  | child value =>
    rw [hSlot] at hBorrow
    cases value with
    | null =>
      have hZero : store.mem.read64 (slotAddress record.source record.next) = 0 := hBorrow.1
      simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch, hZero]
    | record children =>
      have hNonzero := hBorrow.1.1.nonzero
      simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch, hNonzero]

/-- The mask code of the slot test pushes the mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.maskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.mask) store s
      (maskOf record.slots) := by
  obtain ⟨r, -, hMask, hPrefix, -⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hMask]
  exact PushesWord.selectCode r shape.mask (PushesWord.tag hSrc hRoom)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

theorem wp_treeCopyTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {word mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.mask) store s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hWord : s.get (base + 4) = some (.i64 word))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyCondition mask i word) :: s.values } host) :
    wp m (treeCopyTest shape base ++ rest) Q store s host := by
  rw [treeCopyTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex hWord
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    by_cases hZero : word = 0 <;>
    simpa [wp_simp, hIndex, hWord, treeCopyCondition, hBit, hZero] using hNext

#print axioms treeCopyCondition_spec
#print axioms CopyRecord.Holds.maskPushes
#print axioms wp_treeCopyTest

end Verified
