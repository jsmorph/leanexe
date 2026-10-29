import Verified.TreeCopyStartInv
import Verified.TreeCopyAdvanceInv
import Verified.TreeCopyDescendInv
import Verified.TreeCopyAscendInv
import Verified.AlignedTreeMemory

/-!
The alignment of a tree copy in progress, and the copy's invariants under the flag.  `CopyAligned`
states that the heap is aligned, that every block of the records being copied and of the values
already copied into them starts and ends at a multiple of 8, and that every region of their
sources, in the initial store, starts at one.  The first gives each new block an aligned root and
capacity, the second gives the copy's blocks and pointers, and the third gives the sources'
pointers, which the copy reads.  `CopyInvX strict` and `CopyCompletedX strict` are `CopyInv` and
`CopyCompleted` with `CopyAligned` under `strict = true`, and each step lemma is its original with
the alignment of the state after it, from the same equalities of the copy's blocks that the
original proves.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The regions of slot `j` are regions of the slots. -/
theorem slotsRegions_get {store : Store Unit} {p : UInt64} :
    ∀ (i : Nat) (slots : List LeanExe.Pipeline.Slot) (j : Nat) (hj : j < slots.length),
      ∀ r ∈ slotsRegions store p (i + j) [slots[j]], r ∈ slotsRegions store p i slots
  | _, [], _, hj, _, _ => absurd hj (by simp)
  | i, s :: rest, 0, _, r, hr => by
    simp only [List.getElem_cons_zero, Nat.add_zero] at hr
    cases s <;> simp_all [slotsRegions]
  | i, s :: rest, j + 1, hj, r, hr => by
    simp only [List.getElem_cons_succ] at hr
    have hIn := slotsRegions_get (i + 1) rest j (by simp at hj; omega) r
      (by rw [show i + 1 + j = i + (j + 1) by omega]; exact hr)
    cases s <;> simp_all [slotsRegions]

/-- The regions of a child record in slot `j` are regions of its parent. -/
theorem slotRegions_child {store : Store Unit} {p : UInt64} {slots : List LeanExe.Pipeline.Slot}
    {j : Nat} (hj : j < slots.length) {cs : List LeanExe.Pipeline.Slot}
    (hSlot : slots[j] = .child (.record cs)) :
    ∀ r ∈ (Node.record cs).slotRegions store (store.mem.read64 (slotAddress p j)),
      r ∈ (Node.record slots).slotRegions store p := by
  intro r hr
  refine List.mem_cons_of_mem _ (slotsRegions_get 0 slots j hj r ?_)
  rw [hSlot, Nat.zero_add]
  simpa [slotsRegions] using hr

/-- The alignment of a copy in progress. -/
structure CopyAligned (heap : Heap) (initial store : Store Unit) (current : CopyRecord)
    (parents : List CopyRecord) : Prop where
  heap : heap.Aligned
  blocks : ∀ b ∈ copyBlocks store current parents, b.1 % 8 = 0 ∧ b.2 % 8 = 0
  sources : ∀ record ∈ current :: parents,
    ∀ r ∈ (Node.record record.slots).slotRegions initial record.source, r.1 % 8 = 0

/-- `CopyInv` with the alignment under `strict = true`. -/
def CopyInvX (strict : Bool) (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat) (heap : Heap)
    (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop :=
  CopyInv shape heap0 initial root result limit heap store current parents ∧
    (strict = true → CopyAligned heap initial store current parents)

/-- `CopyCompleted` with the alignment under `strict = true`. -/
def CopyCompletedX (strict : Bool) (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat) (heap : Heap)
    (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop :=
  CopyCompleted shape heap0 initial root result limit heap store current parents ∧
    (strict = true → CopyAligned heap initial store current parents)

/-- The pointer of a record whose block is aligned. -/
theorem pointer_mod8_of_block {store : Store Unit} {p : UInt64} (hBase : 48 ≤ p.toNat)
    (h : (block store p).1 % 8 = 0) : p.toNat % 8 = 0 := by
  simp only [block] at h
  omega

/-- The current record's pointer and capacity. -/
theorem CopyAligned.current {heap : Heap} {initial store : Store Unit} {current : CopyRecord}
    {parents : List CopyRecord} (h : CopyAligned heap initial store current parents)
    (hBase : 48 ≤ current.pointer.toNat) :
    current.pointer.toNat % 8 = 0 ∧ capacityAt store current.pointer % 8 = 0 := by
  have hb := h.blocks (block store current.pointer) (by simp [copyBlocks, CopyRecord.blocks])
  simp only [block] at hb
  omega

/-- The pointer of a record whose source is aligned. -/
theorem CopyAligned.source {heap : Heap} {initial store : Store Unit} {current : CopyRecord}
    {parents : List CopyRecord} (h : CopyAligned heap initial store current parents) :
    ∀ record ∈ current :: parents, record.source.toNat % 8 = 0 := fun record hr =>
  h.sources record hr (record.source.toNat, 8 * record.slots.length) (by simp [Node.slotRegions])

/-- `CopyInv.start` with the alignment: the root's new block and the heap after its allocation
are aligned, and so are the source's regions. -/
theorem CopyInv.startX {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {source result : UInt64}
    {limit : Nat}
    (hSource : NodeBorrowed heap0 initial source (.record root))
    (hStep : Step heap0 initial (fun _ => True) heap store [block store result])
    (hRecord : CopyRecord.Holds shape heap store 0 ⟨source, result, root, 0⟩)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + allocCost (8 * root.length))
    (hLimit : heap0.top.toNat + nodeCopyCost (.record root) ≤ limit)
    (hAl : strict = true → heap.Aligned ∧ result.toNat % 8 = 0 ∧
      capacityAt store result % 8 = 0 ∧
      ∀ r ∈ (Node.record root).slotRegions initial source, r.1 % 8 = 0) :
    CopyInvX strict shape heap0 initial root result limit heap store ⟨source, result, root, 0⟩
      [] := by
  have hBlocks : copyBlocks store ⟨source, result, root, 0⟩ [] = [block store result] := by
    simp only [copyBlocks, CopyRecord.blocks, List.take_zero, slotsBlocks,
      List.flatMap_nil, List.append_nil]
  refine ⟨?_, fun hs => ⟨(hAl hs).1, ?_, ?_⟩⟩
  · refine {
      frames := hRecord
      path := .root rfl rfl
      sources := ?_
      step := ?_
      apart := ?_
      budget := ?_
    }
    · intro record hr
      simp only [List.mem_singleton] at hr
      subst record
      exact ⟨hRecord.layout, hSource⟩
    · simpa only [hBlocks] using hStep
    · rw [hBlocks]
      exact List.pairwise_singleton ..
    · simp only [CopyRecord.work, List.drop_zero, CopyWork.cost,
        List.map_nil, List.sum_nil, Nat.add_zero]
      simp only [nodeCopyCost] at hLimit
      omega
  · have hBase := hRecord.storage.base
    obtain ⟨-, hr, hc, -⟩ := hAl hs
    rw [hBlocks]
    intro b hb
    rw [List.mem_singleton.mp hb]
    simp only [block]
    change result.toNat % 8 = 0 at hr
    omega
  · intro record hr
    rw [List.mem_singleton.mp hr]
    exact (hAl hs).2.2.2

/-- `CopyInv.advanceStep` with the alignment: the copy's blocks are those before the step. -/
theorem CopyInv.advanceStepX {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hCurrent : CopyRecord.Holds shape heap store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { current with next := current.next + 1 })
    (hWrite : Step heap store (fun r => regionsDisjoint r (block store current.pointer))
      heap store' [])
    (hBlocks : ({ current with next := current.next + 1 } : CopyRecord).blocks store' =
      current.blocks store)
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hCharge : (current.work parents).charge = 0) :
    CopyInvX strict shape heap0 initial root result limit heap store'
      { current with next := current.next + 1 } parents := by
  obtain ⟨h, hA⟩ := hX
  have hKeep := h.sources.parentsKept h.step h.apart
  have hFrames := h.frames.replaceCurrent hWrite hKeep hCurrent
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (h.frames.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCopyBlocks : copyBlocks store' { current with next := current.next + 1 } parents =
      copyBlocks store current parents := by
    simp only [copyBlocks, hBlocks, hParentBlocks]
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine ⟨?_, fun hs => ⟨(hA hs).heap, by rw [hCopyBlocks]; exact (hA hs).blocks, ?_⟩⟩
  · refine {
      frames := hFrames
      path := h.path.advance _
      sources := h.sources.advance _
      step := ?_
      apart := ?_
      budget := ?_
    }
    · simpa only [hCopyBlocks] using hAll
    · rw [hCopyBlocks]
      exact h.apart
    · exact hWork.cost_bound (by rw [hCharge]; simp) h.budget
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hA hs).sources current List.mem_cons_self
    · exact (hA hs).sources record (List.mem_cons_of_mem current hr)

/-- `CopyInv.descend` with the alignment: the child's new block, the heap after its allocation,
and the child's source regions, which are regions of its parent's source, are aligned. -/
theorem CopyInv.descendX {strict : Bool} {shape : TreeShape} {heap0 heap heap' : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current child : CopyRecord} {parents : List CopyRecord}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record child.slots)) (hNext : child.next = 0)
    (hChildSource : NodeBorrowed heap0 initial child.source (.record child.slots))
    (hChildRead : strict = true →
      child.source = initial.mem.read64 (slotAddress current.source current.next))
    (hNew : Step heap store (fun _ => True) heap' store' [block store' child.pointer])
    (hChild : child.Holds shape heap' store' current.pointer)
    (hTop : heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * child.slots.length))
    (hAl : strict = true → heap'.Aligned ∧ child.pointer.toNat % 8 = 0 ∧
      capacityAt store' child.pointer % 8 = 0) :
    CopyInvX strict shape heap0 initial root result limit heap' store' child
      (current :: parents) := by
  obtain ⟨h, hA⟩ := hX
  obtain ⟨hFrames, hBlocks, hApart⟩ := h.frames.step hNew
  have hCopyBlocks : copyBlocks store' child (current :: parents) =
      block store' child.pointer :: copyBlocks store current parents := by
    simp only [copyBlocks, CopyRecord.blocks, hNext, List.take_zero, slotsBlocks,
      List.cons_append, List.nil_append, List.flatMap_cons] at hBlocks ⊢
    exact congrArg (List.cons (block store' child.pointer)) hBlocks
  have hAll := h.step.transBoth hNew (keep := fun _ => True)
    (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  refine ⟨?_, fun hs => ⟨(hAl hs).1, ?_, ?_⟩⟩
  · refine {
      frames := ⟨hChild, hFrames⟩
      path := .child hBound hSlot h.path
      sources := ?_
      step := ?_
      apart := ?_
      budget := ?_
    }
    · intro record hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨hChild.layout, hChildSource⟩
      · exact h.sources record hr
    · apply hAll.mono (fun _ _ => trivial)
      intro b hb
      rw [hCopyBlocks] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ hb
    · rw [hCopyBlocks]
      exact List.pairwise_cons.mpr
        ⟨fun b hb => regionsDisjoint_symm (hApart b hb _ (by simp)), h.apart⟩
    · have hWork := CopyRecord.work_descend (parents := parents) hBound hSlot hNext
      have hCharge : (current.work parents).charge = allocCost (8 * child.slots.length) := by
        unfold CopyRecord.work
        rw [List.drop_eq_getElem_cons hBound, hSlot]
        rfl
      exact hWork.cost_bound (by rw [hCharge]; exact hTop) h.budget
  · rw [hCopyBlocks]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have hBase := hChild.storage.base
      obtain ⟨-, hp, hc⟩ := hAl hs
      simp only [block]
      omega
    · exact (hA hs).blocks b hb
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · intro r hr'
      rw [hChildRead hs] at hr'
      exact (hA hs).sources current List.mem_cons_self r (slotRegions_child hBound hSlot r hr')
    · exact (hA hs).sources record hr

/-- `CopyInv.complete` with the alignment: the copy's blocks are those before the step. -/
theorem CopyInv.completeX {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (hX : CopyInvX strict shape heap0 initial root result limit heap store current parents)
    (hDone : current.next = current.slots.length)
    (hWrites : Memory.WritesRange store store' (current.pointer.toNat - 40) current.pointer.toNat)
    (hAt : heap.At store') (hOwned : NodeOwned heap store' current.pointer (.record current.slots))
    (hNodeBlocks : Node.blocks store' current.pointer (.record current.slots) =
      Node.blocks store current.pointer (.record current.slots)) :
    CopyCompletedX strict shape heap0 initial root result limit heap store' current parents := by
  obtain ⟨h, hA⟩ := hX
  have hCurrent := h.frames.current
  have hBase := hCurrent.storage.base
  have hWrite : Step heap store (fun r => regionsDisjoint r (block store current.pointer))
      heap store' [] :=
    Step.ofWritesRange hAt hWrites (by simp only [block]; omega) (by simp only [block]; omega)
  have hKeep := h.sources.parentsKept h.step h.apart
  have hParentFrames : CopyParentFrames shape heap store' parents := by
    cases parents with
    | nil => trivial
    | cons parent parents => exact (h.frames.2.stepKeeping hWrite hKeep).1
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (h.frames.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCurrentBlocks : current.blocks store' = current.blocks store := by
    rw [current.blocks_done store' hDone, current.blocks_done store hDone]
    exact hNodeBlocks
  have hCopyBlocks : copyBlocks store' current parents = copyBlocks store current parents := by
    simp only [copyBlocks, hCurrentBlocks, hParentBlocks]
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine ⟨?_, fun hs => ⟨(hA hs).heap, by rw [hCopyBlocks]; exact (hA hs).blocks,
    (hA hs).sources⟩⟩
  refine {
    done := hDone
    owned := hOwned
    parents := hParentFrames
    path := h.path
    sources := h.sources
    step := ?_
    apart := ?_
    budget := h.budget
  }
  · simpa only [hCopyBlocks] using hAll
  · rw [hCopyBlocks]
    exact h.apart

/-- `CopyCompleted.ascend` with the alignment: the copy's blocks are those before the step, in
another order. -/
theorem CopyCompleted.ascendX {strict : Bool} {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current parent : CopyRecord} {parents : List CopyRecord}
    (hX : CopyCompletedX strict shape heap0 initial root result limit heap store current
      (parent :: parents))
    (hParent : CopyRecord.Holds shape heap store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { parent with next := parent.next + 1 })
    (hWrite : Step heap store (fun r => regionsDisjoint r (block store parent.pointer)) heap store' [])
    (hParentBlocks : ({ parent with next := parent.next + 1 } : CopyRecord).blocks store' =
      parent.blocks store ++ Node.blocks store current.pointer (.record current.slots)) :
    CopyInvX strict shape heap0 initial root result limit heap store'
      { parent with next := parent.next + 1 } parents := by
  obtain ⟨h, hA⟩ := hX
  have hSources : CopySources shape heap0 initial parent parents :=
    fun record hr => h.sources record (List.mem_cons_of_mem current hr)
  have hStepTail : Step heap0 initial (fun _ => True) heap store (copyBlocks store parent parents) :=
    h.step.mono (fun _ _ => trivial) (fun _ hb => List.mem_append_right _ hb)
  have hApartTail : (copyBlocks store parent parents).Pairwise regionsDisjoint :=
    (List.pairwise_append.mp h.apart).2.1
  have hKeep := hSources.parentsKept hStepTail hApartTail
  have hFrames := h.parents.replaceCurrent hWrite hKeep hParent
  have hAncestors : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons ancestor parents =>
      have hTail := (h.parents.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hNewBlocks : copyBlocks store' { parent with next := parent.next + 1 } parents =
      (parent.blocks store ++ current.blocks store) ++
        parents.flatMap (fun record => record.blocks store) := by
    simp only [copyBlocks, hParentBlocks, hAncestors, current.blocks_done store h.done]
  have hOldBlocks : copyBlocks store current (parent :: parents) =
      (current.blocks store ++ parent.blocks store) ++
        parents.flatMap (fun record => record.blocks store) := by
    simp only [copyBlocks, List.flatMap_cons, List.append_assoc]
  have hPerm : (copyBlocks store current (parent :: parents)).Perm
      (copyBlocks store' { parent with next := parent.next + 1 } parents) := by
    rw [hOldBlocks, hNewBlocks]
    exact List.perm_append_comm.append_right _
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine ⟨?_, fun hs => ⟨(hA hs).heap,
    fun b hb => (hA hs).blocks b (hPerm.mem_iff.mpr hb), ?_⟩⟩
  · refine {
      frames := hFrames
      path := ?_
      sources := hSources.advance _
      step := hAll.mono (fun _ _ => trivial) (fun _ hb => hPerm.mem_iff.mpr hb)
      apart := h.apart.perm hPerm (fun h => regionsDisjoint_symm h)
      budget := ?_
    }
    · cases h.path with
      | child _ _ rest => exact rest.advance _
    · have hWork := CopyRecord.work_ascend (parent := parent) (parents := parents) h.done
      have hCharge : (current.work (parent :: parents)).charge = 0 := by
        simp only [CopyRecord.work, h.done, List.drop_length, CopyWork.charge]
      exact hWork.cost_bound (by rw [hCharge]; simp) h.budget
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hA hs).sources parent (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact (hA hs).sources record (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

end Verified
