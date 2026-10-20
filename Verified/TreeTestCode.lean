import Verified.TreeCopyState

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
    treeCopyCondition shape.mask record.next
      (store.mem.read64 (slotAddress record.source record.next)) =
      copyBranch record.slots[record.next] := by
  have hBit : ((shape.mask >>> (UInt64.ofNat record.next % 64)) &&& 1) =
      record.slots[record.next].bit := by
    rw [← h.layout.2.1]
    exact maskOf_test _ (by rw [h.layout.1]; exact shape.short) _ hBound
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

theorem wp_treeCopyTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {word : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hWord : s.get (base + 4) = some (.i64 word))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyCondition shape.mask i word) :: s.values } host) :
    wp m (treeCopyTest shape base ++ rest) Q store s host := by
  simp only [Locals.get] at hIndex hWord
  by_cases hBit : ((shape.mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    by_cases hZero : word = 0 <;>
    simpa [treeCopyTest, wp_simp, hIndex, hWord, treeCopyCondition, hBit, hZero] using hNext

#print axioms treeCopyCondition_spec
#print axioms wp_treeCopyTest

end Verified
