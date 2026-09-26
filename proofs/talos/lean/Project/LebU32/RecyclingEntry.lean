import Project.LebU32.RecyclingLoop

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Spec PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 800000

def entryFrame (n : UInt64) : Locals :=
  { params := [.i64 10, .i64 n, .i64 0, .i64 0, .i64 0]
    locals := List.replicate 36 (.i64 0)
    values := [] }

theorem initial_arena (initial : Store Unit) (heap : Heap)
    (hHeap : heap.At initial) (hEmpty : heap.nodes = []) :
    Arena initial heap.top 0 heap initial := by
  refine ⟨hHeap, by simp, rfl, ⟨Nat.le_refl _, ?_⟩, fun _ _ => rfl, rfl⟩
  simp [hEmpty]

theorem initial_buffer (initial : Store Unit) (heap : Heap) (hEmpty : heap.nodes = []) :
    Buffer heap.top heap initial ⟨0, 0⟩ ByteArray.empty := by
  refine ⟨?_, ⟨by simp, ?_⟩, fun _ => rfl, ?_, ?_⟩
  · simp [PackedMemory.ByteArrayAt]
  · simp [hEmpty]
  · simp
  · simp

theorem initial_running (n : UInt64) : Running (entryFrame n) 10 n 0 0 := by
  refine ⟨⟨rfl, rfl, rfl, I64Values.replicate 36 0⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem func0_heap (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (n : UInt64)
    (hHeap : heap.At initial) (hEmpty : heap.nodes = []) (hn : n.toNat < 4294967296)
    (hFit32 : heap.top.toNat + 560 < 4294967296)
    (hFit : heap.top.toNat + 560 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 0 initial [.i64 0, .i64 0, .i64 0, .i64 n, .i64 10]
      (fun final values => ∃ root : UInt64,
        values = [.i64 (UInt64.ofNat (lebList 10 n).length), .i64 root, .i64 root] ∧
        (∀ i : Nat, i < (lebList 10 n).length → final.mem.bytes (root.toNat + i) = (lebList 10 n)[i]!) ∧
        final.mem.pages = initial.mem.pages ∧
        (∀ address, address < heap.top.toNat → final.mem.bytes address = initial.mem.bytes address)) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp «module» func0 _ initial (entryFrame n) env
  rw [function_shape]
  change wp «module» ([.constI64 0, .localSet 5, .constI64 0, .localSet 9] ++
    [.block 0 0 [.loop 0 0 loopBody]] ++ func0.drop 5) _ initial (entryFrame n) env
  wp_packed_frame [entryFrame, List.replicate]
  change wp «module» ([.block 0 0 [.loop 0 0 loopBody]] ++ func0.drop 5) _ initial (entryFrame n) env
  have hStart : loopInvariant initial heap.top (lebList 10 n) initial (entryFrame n) :=
    ⟨heap, ⟨0, 0⟩, ByteArray.empty, initial_arena initial heap hHeap hEmpty,
      initial_buffer initial heap hEmpty, Or.inl ⟨10, n, by decide, rfl, rfl, initial_running n⟩⟩
  apply loop_spec env initial initial heap.top (lebList 10 n) (entryFrame n) (encode_length n hn)
    hStart hFit32 hFit hPages
  intro final result finalHeap node bytes fuel hArena hBuffer hSplit hFinished
  have hLength : (lebList 10 n).length = bytes.size := by
    rw [hSplit]
    rfl
  have hValues := hFinished.values
  have hDone := hFinished.done
  have hOwner := hFinished.owner
  have hPointer := hFinished.pointer
  have hSize := hFinished.size
  simp only [Locals.get] at hDone hOwner hPointer hSize
  change wp «module» [.localGet 9, .constI64 0, .eqI64,
    .iff 0 0 [.localGet 2, .localSet 6, .localGet 3, .localSet 7, .localGet 4, .localSet 8] [],
    .localGet 6, .localGet 7, .localGet 8] _ final result env
  wp_packed_frame [hValues, hDone]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hValues, hOwner, hPointer, hSize]
  refine ⟨node.root, ?_, ?_, hArena.pages, hArena.prefixBytes⟩
  · simp [hLength, func0Def]
  · intro i hi
    have hByte := hBuffer.values.2.2 i (by omega)
    have hBound : i < bytes.size := by omega
    simpa [hSplit, getElem!_pos, hBound, ByteArray.getElem_eq_getElem_data] using hByte

#print axioms initial_arena
#print axioms initial_buffer
#print axioms initial_running
#print axioms func0_heap
end Project.LebU32.Recycling
