import Verified.TreeSlotCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyRead {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {record : CopyRecord} {parent : UInt64} {base : Nat}
    {rest : Program} {Q : Assertion Unit} (h : record.Holds shape heap store parent)
    (hAt : heap.At store) (hBound : record.next < record.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hPtr : s.get (base + 1) = some (.i64 record.pointer))
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat record.next)))
    (hNext : ∀ s', Frame base s s' → s'.get base = s.get base →
      s'.get (base + 1) = some (.i64 record.pointer) →
      s'.get (base + 2) = some (.i64 (UInt64.ofNat record.next)) →
      s'.get (base + 4) = some (.i64 (store.mem.read64 (slotAddress record.source record.next))) →
      s'.values = s.values → wp m rest Q store s' host) :
    wp m (treeCopyRead base ++ rest) Q store s host := by
  have hBase := h.storage.base
  have hAddress := h.storage.address
  have hBelow := h.storage.below
  have hTop := hAt.top
  have hSrcAddress := h.borrowed.1.address
  have hSrcBelow := h.borrowed.1.below
  have hLow3 : s.params.length ≤ base + 3 := by omega
  have hLow4 : s.params.length ≤ base + 4 := by omega
  have hHigh3 : base + 3 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hHigh4 : base + 4 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  let word := store.mem.read64 (slotAddress record.source record.next)
  let sSource := setLocal s (base + 3) (.i64 record.source)
  let sValue := setLocal sSource (base + 4) (.i64 word)
  have hLow4Source : sSource.params.length ≤ base + 4 := hLow4
  have hHigh4Source : base + 4 < sSource.params.length + sSource.locals.length := by
    simpa only [sSource, setLocal, List.length_set] using hHigh4
  have hSourceLocal : sSource.get (base + 3) = some (.i64 record.source) :=
    Locals.get_setLocal_same hLow3 hHigh3
  have hIndexLocal : sSource.get (base + 2) = some (.i64 (UInt64.ofNat record.next)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega)]
    exact hIndex
  have hFrameSource : Frame base s sSource := Frame.set hLow3 (by omega) (by omega)
  have hFrameValue : Frame base sSource sValue := Frame.set hLow4Source (by omega)
    (by rw [hFrameSource.positions]; omega)
  simp only [treeCopyRead, List.append_assoc]
  refine wp_headerLoad hPtr ?_ ?_
  · rw [headerAddress_toNat (by change 24 ≤ record.pointer.toNat; omega) (by omega)]
    change record.pointer.toNat - 24 + 8 ≤ store.mem.pages * 65536
    omega
  rw [h.source]
  refine wp_localSet_local hLow3 hHigh3 ?_
  refine wp_treeSlotLoad hSourceLocal hIndexLocal ?_ ?_
  · rw [slotAddress_toNat (by omega)]
    omega
  refine wp_localSet_local hLow4Source hHigh4Source ?_
  apply hNext sValue (hFrameSource.trans hFrameValue)
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega), Locals.get_setLocal_ne hLow3 (by omega)]
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega), Locals.get_setLocal_ne hLow3 (by omega)]
    exact hPtr
  · dsimp only [sValue]
    rw [Locals.get_setLocal_ne hLow4Source (by omega)]
    exact hIndexLocal
  · exact Locals.get_setLocal_same hLow4Source hHigh4Source
  · rfl

#print axioms wp_treeCopyRead

end Verified
