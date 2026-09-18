import Project.ProofKit.PackedAppendCopy
import Project.ProofKit.PackedAllocationState
import Project.ProofKit.PackedCapacity
import Project.ProofKit.OwnedPacked

namespace Project.ProofKit.PackedAppend
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedMemory FixedArrayCapacity FixedArrayCopy

def need (left right : ByteArray) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (left.size + right.size))

def program (scratch : Nat) : Wasm.Program :=
  [.localGet (scratch + 1), .localGet (scratch + 3), .addI64, .localSet (scratch + 5)] ++
    PackedCapacity.program (scratch + 5) (scratch + 7) ++ PackedAllocation.program (scratch + 7) ++
    [.localGet (scratch + 12), .localSet (scratch + 4)] ++
    PackedCopy.program scratch (scratch + 4) (scratch + 1) (scratch + 6) none ++
    PackedCopy.program (scratch + 2) (scratch + 4) (scratch + 3) (scratch + 6) (some (scratch + 1)) ++
    [.localGet (scratch + 4)]

def Preserved (before after : Locals) (scratch : Nat) : Prop :=
  after.params = before.params ∧ after.locals.length = before.locals.length ∧
  I64Values after.locals ∧ ∀ index, index < scratch → after.get index = before.get index

theorem program_spec (scratch : Nat) (module_ : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (leftPtr rightPtr : UInt64) (left right : ByteArray)
    (hHeap : heap.At initial) (hLeft : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hLeftProtected : heap.Protects leftPtr.toNat (leftPtr.toNat + left.size))
    (hRightProtected : heap.Protects rightPtr.toNat (rightPtr.toNat + right.size))
    (hSize : left.size + right.size ≤ 4294967296)
    (hBump : takeFirstFitFrom 0 (need left right) heap.nodes = none →
      heap.top.toNat + 48 + (need left right).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need left right) ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hLower : frame.params.length ≤ scratch) (hBound : scratch + 13 ≤ frame.params.length + frame.locals.length)
    (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hLeftPtr : frame.get scratch = some (.i64 leftPtr))
    (hLeftLength : frame.get (scratch + 1) = some (.i64 (UInt64.ofNat left.size)))
    (hRightPtr : frame.get (scratch + 2) = some (.i64 rightPtr))
    (hRightLength : frame.get (scratch + 3) = some (.i64 (UInt64.ofNat right.size)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      result.values = [.i64 (allocatedRoot heap.top (need left right) heap.nodes)] →
      Preserved frame result scratch → heap.PackedOutput initial final (need left right) (left ++ right) →
      wp module_ rest Q final result env) :
    wp module_ (program scratch ++ rest) Q initial frame env := by
  have hFit := fun h => (hBump h).1.le
  have hNeed : left.size + right.size ≤ (need left right).toNat := by
    rw [need, PackedCapacity.capacity_toNat _ hSize]
    exact PackedCapacity.capacityNat_ge _
  have hAllocFrame := heap.frame_allocatePacked initial (need left right) hHeap hFit
  have hLeftAllocated := hAllocFrame.packed hLeftProtected hLeft
  have hRightAllocated := hAllocFrame.packed hRightProtected hRight
  have hLeftSep := hLeftProtected.allocated_disjoint (need left right) hFit
  have hRightSep := hRightProtected.allocated_disjoint (need left right) hFit
  have hSpace := allocated_capacity (need left right) heap.nodes
  have hRootBounds := PackedAllocation.root_bounds initial heap.top (need left right) heap.nodes hHeap.freeList hFit
  have hAddressBound : (allocatedRoot heap.top (need left right) heap.nodes).toNat + (need left right).toNat ≤ 4294967296 :=
    hRootBounds.1
  have hMemoryBound : (allocatedRoot heap.top (need left right) heap.nodes).toNat + (need left right).toNat ≤
      (heap.allocatePackedStore initial (need left right)).mem.pages * 65536 := hRootBounds.2
  let sized := capacityFrame frame (scratch + 5) (UInt64.ofNat (left.size + right.size))
  let prepared := capacityFrame sized (scratch + 7) (need left right)
  have hSizedLength : sized.locals.length = frame.locals.length := capacityFrame_locals_length ..
  have hPreparedLength : prepared.locals.length = frame.locals.length :=
    (capacityFrame_locals_length ..).trans hSizedLength
  have hPreparedParams : prepared.params = frame.params := rfl
  have hPreparedTyped : I64Values prepared.locals :=
    capacityFrame_typed _ _ _ (capacityFrame_typed _ _ _ hTyped)
  simp only [program, List.append_assoc, List.cons_append, List.nil_append,
    wp_localGet_cons, Frame.withValues_get, hLeftLength, hRightLength, hValues,
    wp_addI64_cons, ← UInt64.ofNat_add]
  apply storeWord_spec module_ env initial _ (scratch + 5) (UInt64.ofNat (left.size + right.size))
    (by dsimp; omega) (by change scratch + 5 < frame.params.length + frame.locals.length; omega) rfl
  change wp module_ (PackedCapacity.program (scratch + 5) (scratch + 7) ++ _) Q initial sized env
  apply PackedCapacity.program_spec (scratch + 5) (scratch + 7) (UInt64.ofNat (left.size + right.size))
    module_ env initial sized (capacityFrame_get_capacity _ _ _ (by omega) (by
      change scratch + 5 < frame.params.length + frame.locals.length; omega)) rfl
    (by change frame.params.length ≤ scratch + 7; omega)
    (by change scratch + 7 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 7 < frame.params.length + frame.locals.length; omega)
  apply PackedAllocation.program_spec_frame module_ env initial prepared (scratch + 7) heap.top
    (need left right) heap.allocations heap.nodes rfl hPreparedTyped
    (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega)
    (capacityFrame_get_capacity sized (scratch + 7) _ (by change frame.params.length ≤ scratch + 7; omega)
      (by change scratch + 7 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 7 < frame.params.length + frame.locals.length; omega))
    (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    hHeap.freeList (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages hMemory32
  intro previous current capacity next
  let allocated := PackedAllocation.allocatedFrame prepared (scratch + 7)
    (need left right) previous current capacity next (allocatedRoot heap.top (need left right) heap.nodes)
  have hAllocatedLength : allocated.locals.length = frame.locals.length :=
    (PackedAllocation.allocatedFrame_length prepared (scratch + 7) _ _ _ _ _ _
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega)).trans hPreparedLength
  have hAllocatedParams : allocated.params = frame.params := rfl
  have hAllocatedTyped : I64Values allocated.locals := PackedAllocation.allocatedFrame_typed _ _ _ _ _ _ _ _ hPreparedTyped
  have hAllocatedRead (index : Nat) (hi : index < scratch + 4) : allocated.get index = frame.get index := by
    have ha := PackedAllocation.allocatedFrame_get_before prepared (scratch + 7) (need left right) previous current capacity next
      (allocatedRoot heap.top (need left right) heap.nodes)
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega) index (by omega)
    have hp := capacityFrame_get_before sized (scratch + 7) (need left right)
      (by change frame.params.length ≤ scratch + 7; omega)
      (by change scratch + 7 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 7 < frame.params.length + frame.locals.length; omega) index (by omega)
    have hs := capacityFrame_get_before frame (scratch + 5) (UInt64.ofNat (left.size + right.size))
      (by omega) (by change scratch + 5 < frame.params.length + frame.locals.length; omega) index (by omega)
    exact ha.trans (hp.trans hs)
  have hResultRead : allocated.get (scratch + 12) = some (.i64 (allocatedRoot heap.top (need left right) heap.nodes)) := by
    exact PackedAllocation.allocatedFrame_get_field prepared (scratch + 7) _ _ _ _ _ _
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega) 5 (by decide)
  change wp module_ (.localGet (scratch + 12) :: .localSet (scratch + 4) :: _) Q
    (heap.allocatePackedStore initial (need left right)) allocated env
  simp only [wp_localGet_cons, hResultRead, show allocated.values = [] from rfl]
  apply storeWord_spec module_ env _ _ (scratch + 4) _
    (by change frame.params.length ≤ scratch + 4; omega)
    (by change scratch + 4 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega) rfl
  let copying := capacityFrame allocated (scratch + 4) (allocatedRoot heap.top (need left right) heap.nodes)
  have hCopyingLength : copying.locals.length = frame.locals.length :=
    (capacityFrame_locals_length ..).trans hAllocatedLength
  have hCopyingParams : copying.params = frame.params := rfl
  have hCopyingTyped := capacityFrame_typed allocated (scratch + 4) (allocatedRoot heap.top (need left right) heap.nodes) hAllocatedTyped
  have hCopyingRead (index : Nat) (hi : index < scratch + 4) : copying.get index = frame.get index :=
    (capacityFrame_get_before allocated (scratch + 4) _ (by rw [hAllocatedParams]; omega)
      (by change scratch + 4 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega)
      index hi).trans (hAllocatedRead index hi)
  have hCopyingRoot : copying.get (scratch + 4) = some (.i64 (allocatedRoot heap.top (need left right) heap.nodes)) :=
    capacityFrame_get_capacity allocated (scratch + 4) _ (by rw [hAllocatedParams]; omega)
      (by change scratch + 4 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega)
  have hCounter : copying.validIndex (scratch + 6) := by
    change scratch + 6 < copying.params.length + copying.locals.length
    rw [hCopyingParams, hCopyingLength]
    omega
  apply PackedCopy.append_spec scratch (scratch + 2) (scratch + 4) (scratch + 1) (scratch + 3) (scratch + 6)
    module_ env (heap.allocatePackedStore initial (need left right)) copying leftPtr rightPtr
    (allocatedRoot heap.top (need left right) heap.nodes) left right hCounter rfl
    (by omega) (by omega) (by omega) (by omega) (by omega)
    ((hCopyingRead scratch (by omega)).trans hLeftPtr) ((hCopyingRead (scratch + 2) (by omega)).trans hRightPtr)
    hCopyingRoot ((hCopyingRead (scratch + 1) (by omega)).trans hLeftLength)
    ((hCopyingRead (scratch + 3) (by omega)).trans hRightLength) hLeftAllocated hRightAllocated
    (by omega) (by omega) (by omega) (by omega)
  intro final hWrites hBytes
  let done := counterFrame copying (scratch + 6) right.size hCounter
  have hDoneRoot := (counterFrame_get_ne copying (scratch + 6) right.size (scratch + 4) hCounter (by omega)).trans hCopyingRoot
  have hDoneCapacity : done = capacityFrame copying (scratch + 6) (UInt64.ofNat right.size) := by
    simp only [done, counterFrame, Locals.set,
      show ¬scratch + 6 < copying.params.length by rw [hCopyingParams]; omega, ite_false, capacityFrame]
  simp only [wp_localGet_cons, hDoneRoot, counterFrame_values]
  apply hNext _ _ rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change done.params = frame.params
      rw [hDoneCapacity]
      exact hCopyingParams
    · change done.locals.length = frame.locals.length
      exact (counterFrame_locals_length ..).trans hCopyingLength
    · change I64Values done.locals
      rw [hDoneCapacity]
      exact capacityFrame_typed _ _ _ hCopyingTyped
    · intro index hi
      exact (counterFrame_get_ne copying (scratch + 6) right.size index hCounter (by omega)).trans
        (hCopyingRead index (by omega))
  · exact heap.packedOutput initial final (need left right) (left ++ right) hHeap
      (by rw [ByteArray.size_append]; exact hNeed) (fun h => (hBump h).1) hPages
      (by rw [ByteArray.size_append]; exact hWrites) hBytes

#print axioms program_spec

end Project.ProofKit.PackedAppend
