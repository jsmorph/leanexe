import Project.LebU32.RecyclingNegativePush

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem negative_spec (env : HostEnv Unit) (initial store : Store Unit) (base : UInt64)
    (heap : Heap) (node : FreeNode) (bytes : ByteArray) (frame : Locals) (fuel v : UInt64)
    (hArena : Arena initial base bytes.size heap store) (hBuffer : Buffer base heap store node bytes)
    (hRunning : Running frame fuel v node.root bytes.size)
    (hLow : frame.get 10 = some (.i64 (v % 128)))
    (hRest : frame.get 11 = some (.i64 (v / 128)))
    (hSize : bytes.size < 5) (hFit32 : base.toNat + 560 < 4294967296)
    (hFit : base.toNat + 560 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result nextHeap,
      Running result (fuel - 1) (v / 128) (allocatedNode heap.top 8 heap.nodes).root (bytes.size + 1) →
      Arena initial base (bytes.size + 1) nextHeap final →
      Buffer base nextHeap final (allocatedNode heap.top 8 heap.nodes) (bytes.push (v % 128 + 128).toUInt8) →
      wp «module» rest Q final result env) :
    wp «module» (negative ++ rest) Q store frame env := by
  rw [negative_prefix_shape]
  simp only [List.append_assoc]
  apply negative_push_spec env initial store base heap node bytes frame fuel v
    hArena hBuffer hRunning hLow hRest hSize hFit32 hFit hPages hCap
  intro pushed ready hReady hArena' hBuffer' hOutput
  by_cases hEmpty : bytes.size = 0
  · have hZero : ready.get 5 = some (.i64 0) := by
      simpa only [hBuffer.empty hEmpty] using hReady.tracked
    have hValues := hReady.values
    simp only [Locals.get] at hZero
    simp only [PackedReleaseGuard.program, List.cons_append, List.nil_append]
    wp_packed_frame [hZero, hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hValues]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    have hFrame : ({ ready with values := [] } : Locals) = ready :=
      Frame.ext _ _ rfl rfl hValues.symm
    simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append, hFrame]
    apply negative_tail_spec env pushed ready fuel (v / 128) node.root
      (allocatedNode heap.top 8 heap.nodes).root (bytes.size + 1) hReady
    intro result hResult
    exact hNext pushed result (heap.allocate 8) hResult hArena' hBuffer'
  · have hOld := hBuffer.owned hEmpty
    have hKept := hOutput.frame.ownsPacked hOutput.heapAt hOld
    have hBump := (hArena.bump hSize hFit32 hFit hCap).1.le
    have hSep := hOld.allocation_disjoint 8 (fun _ => hBump)
    apply PackedReleaseGuard.program_spec env «module» 5 pushed (heap.allocate 8) ready node bytes
      (allocatedNode heap.top 8 heap.nodes).root 5 21 release_function rfl hOutput.heapAt hKept
      hReady.values hReady.tracked hReady.owner (hOld.root_ne hSep)
    intro hHeap
    have hArena'' := hArena'.released hHeap hKept (hBuffer.above hEmpty)
    have hOwned := hOutput.owned.released node hOld.buffer.rootBound
      (by have := hOld.buffer.addressBound; omega) (regionsDisjoint_symm hSep)
    have hBuffer'' : Buffer base ((heap.allocate 8).release node)
        ((heap.allocate 8).releaseStore pushed node) (allocatedNode heap.top 8 heap.nodes)
        (bytes.push (v % 128 + 128).toUInt8) :=
      ⟨hOwned.buffer.values, hOwned.payload_protects, hBuffer'.empty,
        fun _ => hOwned, hBuffer'.above⟩
    apply negative_tail_spec env _ ready fuel (v / 128) node.root
      (allocatedNode heap.top 8 heap.nodes).root (bytes.size + 1) hReady
    intro result hResult
    exact hNext _ result _ hResult hArena'' hBuffer''

#print axioms negative_spec
end Project.LebU32.Recycling
