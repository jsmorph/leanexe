import Verified.TreeAdvanceCode
import Verified.TreeCopyAscendInv
import Verified.TreeCopyLocals

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyAscendInv {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current parent : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyCompleted shape heap0 initial root result limit heap store current (parent :: parents))
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hFresh : s.get (base + 5) = some (.i64 parent.pointer))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s', CopyInv shape heap0 initial root result limit heap store'
      { parent with next := parent.next + 1 } parents →
      CopyLocals base s0 result parent.pointer s' → wp m rest Q store' s' host) :
    wp m (headerLoad (base + 5) 8 ++ [.localSet (base + 2)] ++
      treeSlotAddress (base + 5) (base + 2) ++ [.localGet (base + 1), .store64 0] ++
      treeCopyAdvance (base + 5) (base + 2) ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host := by
  have hParents : CopyFrames shape heap store parent parents := h.parents
  have hParent := hParents.current
  have hBase := hParent.storage.base
  have hAddress := hParent.storage.address
  have hBelow := hParent.storage.below
  have hTop := h.step.at_.top
  have hApartTail : (copyBlocks store parent parents).Pairwise regionsDisjoint :=
    (List.pairwise_append.mp h.apart).2.1
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  cases h.path with
  | child hBound hSlot hPath =>
    have hValue : (parent.slots[parent.next]).ValueOwned heap store current.pointer := by
      rw [hSlot]
      exact h.owned
    have hSourceApart : ∀ r ∈ (Node.record parent.slots).slotRegions store parent.source,
        regionsDisjoint r (block store parent.pointer) := by
      intro r hr
      exact h.sources.apart h.step (by simp) r hr _ (by simp [copyBlocks, CopyRecord.blocks])
    have hPrefixApart : ∀ b ∈ slotsBlocks store parent.pointer 0 (parent.slots.take parent.next),
        regionsDisjoint b (block store parent.pointer) := by
      intro b hb
      exact regionsDisjoint_symm ((List.pairwise_cons.mp hApartTail).1 b (List.mem_append_left _ hb))
    have hValueApart : ∀ b ∈ (parent.slots[parent.next]).valueBlocks store current.pointer,
        regionsDisjoint b (block store parent.pointer) := by
      intro b hb
      rw [hSlot] at hb
      change b ∈ Node.blocks store current.pointer (.record current.slots) at hb
      rw [← current.blocks_done store h.done] at hb
      exact (List.pairwise_append.mp h.apart).2.2 b hb _ (by simp [copyBlocks, CopyRecord.blocks])
    simp only [List.append_assoc]
    refine wp_headerLoad hFresh ?_ ?_
    · rw [headerAddress_toNat (by change 8 ≤ parent.pointer.toNat; omega) (by omega)]
      change parent.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
      omega
    rw [hParent.index]
    refine wp_localSet_local hLow2 hHigh2 ?_
    let sIndex := setLocal s (base + 2) (.i64 (UInt64.ofNat parent.next))
    have hIndexLocals : CopyLocals base s0 result current.pointer sIndex :=
      hLocals.scratch hLow2 (by omega) (by omega)
    have hParentLocal : sIndex.get (base + 5) = some (.i64 parent.pointer) := by
      rw [Locals.get_setLocal_ne hLow2 (by omega)]
      exact hFresh
    have hIndex : sIndex.get (base + 2) = some (.i64 (UInt64.ofNat parent.next)) :=
      Locals.get_setLocal_same hLow2 hHigh2
    refine wp_copyRecordAdvance (rest := [.localGet (base + 5), .localSet (base + 1)] ++ rest)
      hParent h.step.at_ hBound hValue hSourceApart hPrefixApart hValueApart
      hParentLocal hIndex hIndexLocals.current ?_
    intro store' hParent' hWrite hBlocks
    simp only [hSlot, LeanExe.Pipeline.Slot.valueBlocks] at hBlocks
    have hInv := h.ascend hParent' hWrite hBlocks
    have hLow1 : sIndex.params.length ≤ base + 1 := by change s.params.length ≤ base + 1; omega
    have hHigh1 : base + 1 < sIndex.params.length + sIndex.locals.length := by
      simp only [sIndex, setLocal, List.length_set]
      exact Locals.lt_total (by omega)
    have hNextLocals := hIndexLocals.setCurrent (next := parent.pointer) hLow1
      (by rw [hIndexLocals.frame.positions, ← hLocals.frame.positions]; omega)
    change wp m ([.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store' sIndex host
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, hParentLocal]
    exact wp_localSet_local hLow1 hHigh1 (hNext store' _ hInv hNextLocals)

#print axioms wp_treeCopyAscendInv

end Verified
