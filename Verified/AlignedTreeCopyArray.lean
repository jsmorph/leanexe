import Verified.AlignedTreeCopySteps
import Verified.TreeSlotCode
import Verified.TreeCopyInvariant
import Verified.TreeAdvance
import Verified.TreeCopyLocals
import Verified.TreeCopyStartInv
import Verified.ArrayCopy

/-!
The copy of an array slot under the flag: the ports of `CopyInv.arrayStep` and
`wp_treeCopyArrayInv`.  The source's array, whose region in the initial store is a region of the
source record, has an aligned address, so its copy by `wpX_copyArray` reads aligned words, and the
new block's address and capacity are multiples of 8.  The address goes into the slot of the record
being copied as a word does.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The region of an array in slot `j` is a region of the record. -/
theorem slotRegions_array {store : Store Unit} {p : UInt64} {slots : List LeanExe.Pipeline.Slot}
    {j : Nat} (hj : j < slots.length) {xs : Array UInt64} (hSlot : slots[j] = .array xs) :
    ((store.mem.read64 (slotAddress p j)).toNat, 8 * (xs.size + 1)) ∈
      (Node.record slots).slotRegions store p := by
  refine List.mem_cons_of_mem _ (slotsRegions_get 0 slots j hj _ ?_)
  rw [hSlot, Nat.zero_add]
  simp [slotsRegions]

/-- The address of an array in the slot of the record being copied. -/
theorem CopyInvX.arrayAl {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord} {xs : Array UInt64}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .array xs) :
    strict = true →
      (store.mem.read64 (slotAddress current.source current.next)).toNat % 8 = 0 := fun hs => by
  rw [h.1.step.recordRead (h.1.sources current List.mem_cons_self).2 hBound]
  exact (h.2 hs).sources current List.mem_cons_self _ (slotRegions_array hBound hSlot)

/-- `CopyInv.arrayStep` with the alignment: the new block of the array and the heap after it are
aligned. -/
theorem CopyInv.arrayStepX {strict : Bool} {shape : TreeShape} {heap0 heap heap' : Heap}
    {initial store store1 store' : Store Unit} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {xs : Array UInt64} {ptr : UInt64}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .array xs)
    (hNew : Step heap store (fun _ => True) heap' store1 [block store1 ptr])
    (hTop : heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * (xs.size + 1)))
    (hCurrent : CopyRecord.Holds shape heap' store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { current with next := current.next + 1 })
    (hWrite : Step heap' store1 (fun r => regionsDisjoint r (block store1 current.pointer))
      heap' store' [])
    (hBlocks : ({ current with next := current.next + 1 } : CopyRecord).blocks store' =
      current.blocks store1 ++ [block store1 ptr])
    (hAl : strict = true → (block store1 ptr).1 % 8 = 0 ∧ (block store1 ptr).2 % 8 = 0 ∧
      heap'.Aligned) :
    CopyInvX strict shape heap0 initial root result limit heap' store'
      { current with next := current.next + 1 } parents := by
  obtain ⟨h, hA⟩ := hX
  obtain ⟨hFrames1, hSame1, hFresh1⟩ := h.frames.step hNew
  have hStep1 : Step heap0 initial (fun _ => True) heap' store1
      (copyBlocks store1 current parents ++ [block store1 ptr]) := by
    rw [hSame1]
    exact h.step.transBoth hNew (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  have hApart1 : (copyBlocks store1 current parents).Pairwise regionsDisjoint := by
    rw [hSame1]
    exact h.apart
  have hKeep := h.sources.parentsKept
    (hStep1.mono (fun _ h => h) (fun b hb => List.mem_append_left _ hb)) hApart1
  have hFrames := hFrames1.replaceCurrent hWrite hKeep hCurrent
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store1) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (hFrames1.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCopyBlocks : copyBlocks store' { current with next := current.next + 1 } parents =
      current.blocks store1 ++
        block store1 ptr :: parents.flatMap (fun record => record.blocks store1) := by
    simp only [copyBlocks, hBlocks, hParentBlocks, List.append_assoc, List.singleton_append]
  have hAll := hStep1.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine ⟨?_, fun hs => ⟨(hAl hs).2.2, ?_, ?_⟩⟩
  · refine {
      frames := hFrames
      path := h.path.advance _
      sources := h.sources.advance _
      step := hAll.mono (fun _ _ => trivial) (fun b hb => ?_)
      apart := ?_
      budget := ?_
    }
    · rw [hCopyBlocks] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append_left _ (List.mem_append_left _ hb)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_left _ (List.mem_append_right _ hb)
    · rw [hCopyBlocks]
      apply (List.pairwise_middle (fun h => regionsDisjoint_symm h)).mpr
      refine List.pairwise_cons.mpr ⟨fun b hb => ?_, hApart1⟩
      have hb' : b ∈ copyBlocks store current parents := by
        rw [← hSame1]
        exact hb
      exact regionsDisjoint_symm (hFresh1 b hb' _ (List.mem_singleton_self _))
    · have hWork := CopyRecord.work_array (parents := parents) hBound hSlot
      have hCharge : (current.work parents).charge = allocCost (8 * (xs.size + 1)) := by
        unfold CopyRecord.work
        rw [List.drop_eq_getElem_cons hBound, hSlot]
        exact congrArg allocCost (Nat.mul_comm _ _)
      exact hWork.cost_bound (by rw [hCharge]; exact hTop) h.budget
  · rw [hCopyBlocks]
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (hA hs).blocks b (by rw [← hSame1]; exact List.mem_append_left _ hb)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨(hAl hs).1, (hAl hs).2.1⟩
      · exact (hA hs).blocks b (by rw [← hSame1]; exact List.mem_append_right _ hb)
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hA hs).sources current List.mem_cons_self
    · exact (hA hs).sources record (List.mem_cons_of_mem current hr)

/-- The invariant after the copy of an array slot: the allocation of the array's new block, and
the write of its address into the slot and of the next index into the header. -/
theorem CopyInv.arrayStep {shape : TreeShape} {heap0 heap heap' : Heap}
    {initial store store1 store' : Store Unit} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {xs : Array UInt64} {ptr : UInt64}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .array xs)
    (hNew : Step heap store (fun _ => True) heap' store1 [block store1 ptr])
    (hTop : heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * (xs.size + 1)))
    (hCurrent : CopyRecord.Holds shape heap' store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { current with next := current.next + 1 })
    (hWrite : Step heap' store1 (fun r => regionsDisjoint r (block store1 current.pointer))
      heap' store' [])
    (hBlocks : ({ current with next := current.next + 1 } : CopyRecord).blocks store' =
      current.blocks store1 ++ [block store1 ptr]) :
    CopyInv shape heap0 initial root result limit heap' store'
      { current with next := current.next + 1 } parents :=
  (CopyInv.arrayStepX (strict := false) ⟨h, nofun⟩ hBound hSlot hNew hTop hCurrent hWrite hBlocks
    nofun).1
#print axioms CopyInv.arrayStep

theorem wpX_treeCopyArrayInv {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {xs : Array UInt64}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .array xs)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s',
      CopyInvX strict shape heap0 initial root result limit heap' store'
        { current with next := current.next + 1 } parents →
      CopyLocals base s0 result current.pointer s' → wpX strict m rest Q store' s' host) :
    wpX strict m (treeCopyArray base ++ rest) Q store s host := by
  have hCurrent := h.1.frames.current
  have hBorrow := SlotsBorrowed.get current.slots 0 hCurrent.borrowed.2 current.next hBound
  rw [hSlot] at hBorrow
  simp only [Nat.zero_add] at hBorrow
  have hCharge : allocCost (8 * (xs.size + 1)) ≤ (current.work parents).cost := by
    unfold CopyRecord.work CopyWork.cost
    rw [List.drop_eq_getElem_cons hBound, hSlot]
    simp only [slotsCopyCost]
    rw [Nat.mul_comm (xs.size + 1) 8]
    omega
  have hLow2 : s.params.length ≤ base + 2 := by omega
  have hHigh2 : base + 2 < s.params.length + s.locals.length := Locals.lt_total (by omega)
  simp only [treeCopyArray, List.append_assoc, List.cons_append, List.nil_append,
    wpX_localGet_cons, hWord]
  refine wpX_localSet_local hLow2 hHigh2 ?_
  let word := store.mem.read64 (slotAddress current.source current.next)
  let s2 := setLocal s (base + 2) (.i64 word)
  change wpX strict m _ Q store s2 host
  have hSrc2 : s2.get (base + 2) = some (.i64 word) := Locals.get_setLocal_same hLow2 hHigh2
  have hLocals2 : CopyLocals base s0 result current.pointer s2 :=
    hLocals.scratch hLow2 (by omega) (by omega)
  have hPositions2 : s2.positions = s.positions := by
    simp only [s2, Locals.positions_setLocal]
  refine wpX_copyArray (c := allocCost (8 * (xs.size + 1))) hm hRt h.1.step.at_
    (fun hs => (h.2 hs).heap) (h.arrayAl hBound hSlot)
    (by rw [h.1.step.cap m]; exact hCap) le_rfl (h.1.toCopyProgress.trap hCharge hTrap) hBorrow.1
    hSrc2 (by omega) (by show s.params.length ≤ base + 3; omega) (by omega) ?_
  intro heap1 store1 s3 ptr hNew hOwned hFrame3 hTop hAlloc
  obtain ⟨hFrames1, hSame1, hFresh1⟩ := h.1.frames.step hNew
  have hCurrent1 := hFrames1.current
  have hLow4 : s3.params.length ≤ base + 4 := by
    rw [hFrame3.params]
    show s.params.length ≤ _
    omega
  have hHigh4 : base + 4 < s3.params.length + s3.locals.length :=
    Locals.lt_total (by rw [hFrame3.positions, hPositions2]; omega)
  refine wpX_localSet_local hLow4 hHigh4 ?_
  let s4 := setLocal { s3 with values := s2.values } (base + 4) (.i64 ptr)
  change wpX strict m _ Q store1 s4 host
  have hPositions4 : s4.positions = s.positions := by
    simp only [s4, Locals.positions_setLocal]
    rw [← hPositions2, ← hFrame3.positions]
    rfl
  have hBelow3 (j : Nat) (hj : j < base + 3) : s4.get j = s2.get j := by
    rw [Locals.get_setLocal_ne (s := { s3 with values := s2.values }) hLow4 (by omega)]
    exact (hFrame3.below j hj).1
  have hLocals4 : CopyLocals base s0 result current.pointer s4 :=
    ⟨hLocals2.frame.trans ((hFrame3.mono (by omega)).trans
      (Frame.setValues hLow4 (by omega) (by rw [hFrame3.positions, hPositions2]; omega))),
      (hBelow3 base (by omega)).trans hLocals2.result,
      (hBelow3 (base + 1) (by omega)).trans hLocals2.current, hLocals2.values⟩
  have hPtr4 : s4.get (base + 4) = some (.i64 ptr) :=
    Locals.get_setLocal_same (s := { s3 with values := s2.values }) hLow4 hHigh4
  have hBase := hCurrent1.storage.base
  have hAddress := hCurrent1.storage.address
  have hBelow := hCurrent1.storage.below
  have hTop1 := hNew.at_.top
  refine wpX_headerLoad hLocals4.current ?_ (fun hs => ⟨h.pointerAl hs, rfl⟩) ?_
  · rw [headerAddress_toNat (by change 8 ≤ current.pointer.toNat; omega) (by omega)]
    change current.pointer.toNat - 8 + 8 ≤ store1.mem.pages * 65536
    omega
  rw [hCurrent1.index]
  have hLow2' : s4.params.length ≤ base + 2 := by
    rw [hLocals4.frame.params, ← hLocals.frame.params]
    omega
  have hHigh2' : base + 2 < s4.params.length + s4.locals.length :=
    Locals.lt_total (by rw [hPositions4]; omega)
  refine wpX_localSet_local hLow2' hHigh2' ?_
  let s5 := setLocal s4 (base + 2) (.i64 (UInt64.ofNat current.next))
  change wpX strict m _ Q store1 s5 host
  have hLocals5 : CopyLocals base s0 result current.pointer s5 :=
    hLocals4.scratch hLow2' (by omega) (by rw [hPositions4]; omega)
  have hIndex5 : s5.get (base + 2) = some (.i64 (UInt64.ofNat current.next)) :=
    Locals.get_setLocal_same hLow2' hHigh2'
  have hPtr5 : s5.get (base + 4) = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow2' (by omega)]
    exact hPtr4
  have hStep1 : Step heap0 initial (fun _ => True) heap1 store1
      (copyBlocks store current parents ++ [block store1 ptr]) :=
    h.1.step.transBoth hNew (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  have hMem : block store1 current.pointer ∈ copyBlocks store current parents := by
    rw [← hSame1]
    simp [copyBlocks, CopyRecord.blocks]
  have hApart1 : (copyBlocks store1 current parents).Pairwise regionsDisjoint := by
    rw [hSame1]
    exact h.1.apart
  simp only [copyBlocks, CopyRecord.blocks, List.cons_append] at hApart1
  have hHead := (List.pairwise_cons.mp hApart1).1
  have hValue : (current.slots[current.next]).ValueOwned heap1 store1 ptr := by
    rw [hSlot]
    exact hOwned
  have hRun := wpX_copyRecordAdvance (rest := rest) (Q := Q) (s := s5) hCurrent1 hNew.at_ hBound
    hValue
    (fun r hr => h.1.sources.apart hStep1 List.mem_cons_self r hr _
      (List.mem_append_left _ hMem))
    (fun b hb => regionsDisjoint_symm (hHead b (List.mem_append_left _ hb)))
    (fun b hb => by
      rw [hSlot] at hb
      rw [List.mem_singleton.mp hb]
      exact regionsDisjoint_symm (hFresh1 _ hMem _ (List.mem_singleton_self _)))
    hLocals5.current hIndex5 hPtr5 h.pointerAl
    (fun store' hHolds hWrite hBlocks => by
      rw [hSlot] at hBlocks
      exact hNext heap1 store' s5
        (CopyInv.arrayStepX h hBound hSlot hNew hTop hHolds hWrite hBlocks fun hs => by
          have := hOwned.base
          obtain ⟨hp, hc, ha⟩ := hAlloc hs
          simp only [block]
          exact ⟨by omega, by omega, ha⟩) hLocals5)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hRun

/-- The copy of an array slot: the array goes to a new block, and its address goes into the slot
of the record being copied, whose index advances. -/
theorem wp_treeCopyArrayInv {m : Module} (hm : Runtime m) {host : HostEnv Unit}
    {heap0 heap : Heap} {initial store : Store Unit} {shape : TreeShape}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit base : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {s0 s : Locals} {xs : Array UInt64}
    {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hWord : s.get (base + 4) =
      some (.i64 (store.mem.read64 (slotAddress current.source current.next))))
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .array xs)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q)
    (hNext : ∀ heap' store' s',
      CopyInv shape heap0 initial root result limit heap' store'
        { current with next := current.next + 1 } parents →
      CopyLocals base s0 result current.pointer s' → wp m rest Q store' s' host) :
    wp m (treeCopyArray base ++ rest) Q store s host :=
  wpX_treeCopyArrayInv (strict := false) hm nofun ⟨h, nofun⟩ hLocals hWord hBound hSlot hLow hHigh
    hCap hTrap (fun heap' store' s' a1 a2 => hNext heap' store' s' a1.1 a2)
#print axioms wp_treeCopyArrayInv

end Verified
