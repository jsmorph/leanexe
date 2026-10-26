import Verified.TreeNewCode
import Verified.TreeCopyDescendInv
import Verified.TreeCopyStartInv
import Verified.TreeCopyLocals

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyDescendInv {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root children : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record children))
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' ptr s',
      CopyInv shape heap0 initial root result limit heap' store'
        ⟨store.mem.read64 (slotAddress current.source current.next), ptr, children, 0⟩
        (current :: parents) →
      CopyLocals base s0 result ptr s' → wp m rest Q store' s' host) :
    wp m (treeCopyAllocate shape (base + 4) (base + 5) ++
      treeCopyBegin shape (base + 4) (base + 5) [.localGet (base + 4)] [.localGet (base + 1)] ++
      [.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store s host := by
  have hCurrent := h.frames.current
  have hLayout : NodeLayout shape (.record children) := by
    obtain ⟨-, -, -, -, hSlots⟩ := id hCurrent.layout
    exact SlotsLayout.child (slots := current.slots) hSlots current.next hBound
      (.record children) hSlot
  have hBorrow := SlotsBorrowed.get current.slots 0 hCurrent.borrowed.2 current.next hBound
  rw [hSlot] at hBorrow
  simp only [Nat.zero_add] at hBorrow
  have hInitialChild := h.step.childSource (h.sources current List.mem_cons_self).2 hBound hSlot
  have hCharge : allocCost (8 * children.length) ≤ (current.work parents).cost := by
    unfold CopyRecord.work CopyWork.cost
    rw [List.drop_eq_getElem_cons hBound, hSlot]
    simp only [slotsCopyCost, nodeCopyCost]
    omega
  have hLow5 : s.params.length ≤ base + 5 := by omega
  have hHigh5 : base + 5 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  have hLow1 : s.params.length ≤ base + 1 := by omega
  have hHigh1 : base + 1 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  rw [List.append_assoc]
  refine wp_treeCopyNew hm (shape := shape) (dst := base + 5) (input := base + 4)
    (parent := some (base + 1)) (slots := children)
    (rest := [.localGet (base + 5), .localSet (base + 1)] ++ rest) h.step.at_ ?_
    (h.toCopyProgress.trap hCharge hTrap) hLayout hBorrow.1 hWord hLocals.current
    (by omega) ?_ hLow5 hHigh5 ?_
  · rw [h.step.cap m]
    exact hCap
  · intro pos hp
    simp only [Option.some.injEq] at hp
    omega
  intro heap' store' ptr hNew hChild hTop
  have hInv := h.descend
    (child := ⟨store.mem.read64 (slotAddress current.source current.next), ptr, children, 0⟩)
    hBound hSlot rfl hInitialChild hNew hChild hTop
  let sFresh := setLocal s (base + 5) (.i64 ptr)
  have hFreshLocals : CopyLocals base s0 result current.pointer sFresh :=
    hLocals.scratch hLow5 (by omega) (by omega)
  have hFresh : sFresh.get (base + 5) = some (.i64 ptr) :=
    Locals.get_setLocal_same hLow5 hHigh5
  have hLow1Fresh : sFresh.params.length ≤ base + 1 := hLow1
  have hHigh1Fresh : base + 1 < sFresh.params.length + sFresh.locals.length := by
    simpa only [sFresh, setLocal, List.length_set] using hHigh1
  have hNextLocals := hFreshLocals.setCurrent (next := ptr) hLow1Fresh
    (by rw [hFreshLocals.frame.positions]; rw [← hLocals.frame.positions]; omega)
  change wp m ([.localGet (base + 5), .localSet (base + 1)] ++ rest) Q store' sFresh host
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, hFresh]
  exact wp_localSet_local hLow1Fresh hHigh1Fresh (hNext heap' store' ptr _ hInv hNextLocals)

#print axioms wp_treeCopyDescendInv

end Verified
