import Project.ProofKit.PackedPushCopy
import Project.ProofKit.PackedAllocationState
import Project.ProofKit.PackedCapacity
import Project.ProofKit.OwnedPacked

namespace Project.ProofKit.PackedPush
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedMemory FixedArrayCapacity FixedArrayCopy

def need (bytes : ByteArray) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (bytes.size + 1))

def program (scratch : Nat) : Wasm.Program :=
  [.localGet (scratch + 1), .constI64 1, .addI64, .localSet (scratch + 4)] ++
    PackedCapacity.program (scratch + 4) (scratch + 6) ++ PackedAllocation.program (scratch + 6) ++
    [.localGet (scratch + 11), .localSet (scratch + 3)] ++
    PackedCopy.pushProgram scratch (scratch + 3) (scratch + 1) (scratch + 2) (scratch + 5) ++
    [.localGet (scratch + 3)]

def Preserved (before after : Locals) (scratch : Nat) : Prop :=
  after.params = before.params ∧ after.locals.length = before.locals.length ∧
  I64Values after.locals ∧ ∀ index, index < scratch ∨ scratch + 12 ≤ index → after.get index = before.get index

theorem program_spec (scratch : Nat) (module_ : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (source value : UInt64) (bytes : ByteArray)
    (hHeap : heap.At initial) (hBytes : ByteArrayAt initial.mem source.toNat bytes)
    (hProtected : heap.Protects source.toNat (source.toNat + bytes.size))
    (hSize : bytes.size + 1 ≤ 4294967296)
    (hBump : takeFirstFitFrom 0 (need bytes) heap.nodes = none →
      heap.top.toNat + 48 + (need bytes).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need bytes) ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hLower : frame.params.length ≤ scratch) (hBound : scratch + 12 ≤ frame.params.length + frame.locals.length)
    (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hSource : frame.get scratch = some (.i64 source))
    (hLength : frame.get (scratch + 1) = some (.i64 (UInt64.ofNat bytes.size)))
    (hValue : frame.get (scratch + 2) = some (.i64 value))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      result.values = [.i64 (allocatedRoot heap.top (need bytes) heap.nodes)] →
      Preserved frame result scratch → heap.PackedOutput initial final (need bytes) (bytes.push value.toUInt8) →
      final.mem.pages = (heap.allocatePackedStore initial (need bytes)).mem.pages →
      wp module_ rest Q final result env) :
    wp module_ (program scratch ++ rest) Q initial frame env := by
  have hFit := fun h => (hBump h).1.le
  have hNeed : bytes.size + 1 ≤ (need bytes).toNat := by
    rw [need, PackedCapacity.capacity_toNat _ hSize]
    exact PackedCapacity.capacityNat_ge _
  have hAllocFrame := heap.frame_allocatePacked initial (need bytes) hHeap hFit
  have hAllocatedBytes := hAllocFrame.packed hProtected hBytes
  have hSeparate := hProtected.allocated_disjoint (need bytes) hFit
  have hSpace := allocated_capacity (need bytes) heap.nodes
  have hRootBounds := PackedAllocation.root_bounds initial heap.top (need bytes) heap.nodes hHeap.freeList hFit
  have hAddressBound : (allocatedRoot heap.top (need bytes) heap.nodes).toNat + (need bytes).toNat ≤ 4294967296 :=
    hRootBounds.1
  have hMemoryBound : (allocatedRoot heap.top (need bytes) heap.nodes).toNat + (need bytes).toNat ≤
      (heap.allocatePackedStore initial (need bytes)).mem.pages * 65536 := hRootBounds.2
  let sized := capacityFrame frame (scratch + 4) (UInt64.ofNat (bytes.size + 1))
  let prepared := capacityFrame sized (scratch + 6) (need bytes)
  have hSizedLength : sized.locals.length = frame.locals.length := capacityFrame_locals_length ..
  have hPreparedLength : prepared.locals.length = frame.locals.length :=
    (capacityFrame_locals_length ..).trans hSizedLength
  have hPreparedParams : prepared.params = frame.params := rfl
  have hPreparedTyped : I64Values prepared.locals :=
    capacityFrame_typed _ _ _ (capacityFrame_typed _ _ _ hTyped)
  have hSum : UInt64.ofNat bytes.size + 1 = UInt64.ofNat (bytes.size + 1) :=
    (UInt64.ofNat_add bytes.size 1).symm
  simp only [program, List.append_assoc, List.cons_append, List.nil_append,
    wp_localGet_cons, Frame.withValues_get, hLength, wp_constI64_cons, hValues,
    wp_addI64_cons, hSum]
  apply storeWord_spec module_ env initial _ (scratch + 4) (UInt64.ofNat (bytes.size + 1))
    (by dsimp; omega) (by change scratch + 4 < frame.params.length + frame.locals.length; omega) rfl
  change wp module_ (PackedCapacity.program (scratch + 4) (scratch + 6) ++ _) Q initial sized env
  apply PackedCapacity.program_spec (scratch + 4) (scratch + 6) (UInt64.ofNat (bytes.size + 1))
    module_ env initial sized (capacityFrame_get_capacity _ _ _ (by omega) (by
      change scratch + 4 < frame.params.length + frame.locals.length; omega)) rfl
    (by change frame.params.length ≤ scratch + 6; omega)
    (by change scratch + 6 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 6 < frame.params.length + frame.locals.length; omega)
  apply PackedAllocation.program_spec_frame module_ env initial prepared (scratch + 6) heap.top
    (need bytes) heap.allocations heap.nodes rfl hPreparedTyped
    (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega)
    (capacityFrame_get_capacity sized (scratch + 6) _ (by change frame.params.length ≤ scratch + 6; omega)
      (by change scratch + 6 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 6 < frame.params.length + frame.locals.length; omega))
    (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    hHeap.freeList (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages hMemory32
  intro previous current capacity next
  let allocated := PackedAllocation.allocatedFrame prepared (scratch + 6)
    (need bytes) previous current capacity next (allocatedRoot heap.top (need bytes) heap.nodes)
  have hAllocatedLength : allocated.locals.length = frame.locals.length :=
    (PackedAllocation.allocatedFrame_length prepared (scratch + 6) _ _ _ _ _ _
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega)).trans hPreparedLength
  have hAllocatedParams : allocated.params = frame.params := rfl
  have hAllocatedTyped : I64Values allocated.locals := PackedAllocation.allocatedFrame_typed _ _ _ _ _ _ _ _ hPreparedTyped
  have hAllocatedRead (index : Nat) (hi : index < scratch + 3) : allocated.get index = frame.get index := by
    have ha := PackedAllocation.allocatedFrame_get_before prepared (scratch + 6) (need bytes) previous current capacity next
      (allocatedRoot heap.top (need bytes) heap.nodes)
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega) index (by omega)
    have hp := capacityFrame_get_before sized (scratch + 6) (need bytes)
      (by change frame.params.length ≤ scratch + 6; omega)
      (by change scratch + 6 < sized.params.length + sized.locals.length; rw [hSizedLength]; change scratch + 6 < frame.params.length + frame.locals.length; omega) index (by omega)
    have hs := capacityFrame_get_before frame (scratch + 4) (UInt64.ofNat (bytes.size + 1))
      (by omega) (by change scratch + 4 < frame.params.length + frame.locals.length; omega) index (by omega)
    exact ha.trans (hp.trans hs)
  have hResultRead : allocated.get (scratch + 11) = some (.i64 (allocatedRoot heap.top (need bytes) heap.nodes)) := by
    exact PackedAllocation.allocatedFrame_get_field prepared (scratch + 6) _ _ _ _ _ _
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega) 5 (by decide)
  have hAllocatedAfter (index : Nat) (hi : scratch + 12 ≤ index) : allocated.get index = frame.get index := by
    exact (PackedAllocation.allocatedFrame_get_after prepared (scratch + 6) (need bytes) previous current capacity next
      (allocatedRoot heap.top (need bytes) heap.nodes)
      (by rw [hPreparedParams]; omega) (by rw [hPreparedParams, hPreparedLength]; omega) index (by omega)).trans
      ((capacityFrame_get_ne sized (scratch + 6) (need bytes)
        (by change frame.params.length ≤ scratch + 6; omega) index (by omega)).trans
      (capacityFrame_get_ne frame (scratch + 4) (UInt64.ofNat (bytes.size + 1)) (by omega) index (by omega)))
  change wp module_ (.localGet (scratch + 11) :: .localSet (scratch + 3) :: _) Q
    (heap.allocatePackedStore initial (need bytes)) allocated env
  simp only [wp_localGet_cons, hResultRead, show allocated.values = [] from rfl]
  apply storeWord_spec module_ env _ _ (scratch + 3) _
    (by change frame.params.length ≤ scratch + 3; omega)
    (by change scratch + 3 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega) rfl
  let copying := capacityFrame allocated (scratch + 3) (allocatedRoot heap.top (need bytes) heap.nodes)
  have hCopyingLength : copying.locals.length = frame.locals.length :=
    (capacityFrame_locals_length ..).trans hAllocatedLength
  have hCopyingParams : copying.params = frame.params := rfl
  have hCopyingTyped := capacityFrame_typed allocated (scratch + 3) (allocatedRoot heap.top (need bytes) heap.nodes) hAllocatedTyped
  have hCopyingRead (index : Nat) (hi : index < scratch + 3) : copying.get index = frame.get index :=
    (capacityFrame_get_before allocated (scratch + 3) _ (by rw [hAllocatedParams]; omega)
      (by change scratch + 3 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega)
      index hi).trans (hAllocatedRead index hi)
  have hCopyingRoot : copying.get (scratch + 3) = some (.i64 (allocatedRoot heap.top (need bytes) heap.nodes)) :=
    capacityFrame_get_capacity allocated (scratch + 3) _ (by rw [hAllocatedParams]; omega)
      (by change scratch + 3 < allocated.params.length + allocated.locals.length; rw [hAllocatedParams, hAllocatedLength]; omega)
  have hCounter : copying.validIndex (scratch + 5) := by
    change scratch + 5 < copying.params.length + copying.locals.length
    rw [hCopyingParams, hCopyingLength]
    omega
  apply PackedCopy.push_spec scratch (scratch + 3) (scratch + 1) (scratch + 2) (scratch + 5)
    module_ env (heap.allocatePackedStore initial (need bytes)) copying source
    (allocatedRoot heap.top (need bytes) heap.nodes) value bytes hCounter rfl
    (by omega) (by omega) (by omega) (by omega)
    ((hCopyingRead scratch (by omega)).trans hSource) hCopyingRoot
    ((hCopyingRead (scratch + 1) (by omega)).trans hLength)
    ((hCopyingRead (scratch + 2) (by omega)).trans hValue) hAllocatedBytes
    (by omega) (by omega) (by omega)
  intro final hWrites hBytes
  let done := counterFrame copying (scratch + 5) bytes.size hCounter
  have hDoneRoot := (counterFrame_get_ne copying (scratch + 5) bytes.size (scratch + 3) hCounter (by omega)).trans hCopyingRoot
  have hDoneCapacity : done = capacityFrame copying (scratch + 5) (UInt64.ofNat bytes.size) := by
    simp only [done, counterFrame, Locals.set,
      show ¬scratch + 5 < copying.params.length by rw [hCopyingParams]; omega, ite_false, capacityFrame]
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
      apply (counterFrame_get_ne copying (scratch + 5) bytes.size index hCounter (by omega)).trans
      rcases hi with hi | hi
      · exact hCopyingRead index (by omega)
      · exact (capacityFrame_get_ne allocated (scratch + 3) _
          (by rw [hAllocatedParams]; omega) index (by omega)).trans (hAllocatedAfter index hi)
  · exact heap.packedOutput initial final (need bytes) (bytes.push value.toUInt8) hHeap
      (by rw [ByteArray.size_push]; exact hNeed) (fun h => (hBump h).1) hPages
      (by simpa only [ByteArray.size_push, Nat.add_assoc] using hWrites) hBytes
  · exact hWrites.2.1

#print axioms program_spec
end Project.ProofKit.PackedPush
