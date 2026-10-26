import Verified.TreeRestoreCode
import Verified.TreeCopyCompleteInv
import Verified.TreeCopyLocals

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyComplete {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s', CopyCompleted shape heap0 initial root result limit heap store' current parents →
      CopyLocals base s0 result current.pointer s' →
      s'.get (base + 5) = some (.i64 ((parents.head?.map CopyRecord.pointer).getD 0)) →
      wp m rest Q store' s' host) :
    wp m (headerLoad (base + 1) 40 ++ [.localSet (base + 5)] ++
      restoreRecordCode shape (base + 1) ++ rest) Q store s host := by
  have hCurrent := h.frames.current
  have hBase := hCurrent.storage.base
  have hAddress := hCurrent.storage.address
  have hBelow := hCurrent.storage.below
  have hTop := h.step.at_.top
  have hLow5 : s.params.length ≤ base + 5 := by omega
  have hHigh5 : base + 5 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hSlots : SlotsOwned heap store current.pointer 0 current.slots := by
    simpa only [hDone, List.take_length] using hCurrent.filled
  have hNodeApart : (Node.blocks store current.pointer (.record current.slots)).Pairwise
      regionsDisjoint := by
    rw [← current.blocks_done store hDone]
    exact (List.pairwise_append.mp h.apart).1
  simp only [List.append_assoc]
  refine wp_headerLoad hLocals.current ?_ ?_
  · rw [headerAddress_toNat (by change 40 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 40 + 8 ≤ store.mem.pages * 65536
    omega
  rw [hCurrent.parent]
  refine wp_localSet_local hLow5 hHigh5 ?_
  let sFresh := setLocal s (base + 5) (.i64 ((parents.head?.map CopyRecord.pointer).getD 0))
  have hFreshLocals : CopyLocals base s0 result current.pointer sFresh :=
    hLocals.scratch hLow5 (by omega) (by omega)
  have hFresh : sFresh.get (base + 5) = some (.i64 ((parents.head?.map CopyRecord.pointer).getD 0)) :=
    Locals.get_setLocal_same hLow5 hHigh5
  refine wp_restoreOwnedRecord hCurrent.storage h.step.at_ hFreshLocals.current hCurrent.layout
    hSlots hNodeApart ?_
  intro store' hWrites hAt hOwned hBlocks
  exact hNext store' sFresh (h.complete hDone hWrites hAt hOwned hBlocks) hFreshLocals hFresh

#print axioms wp_treeCopyComplete

end Verified
