import Project.LebU32.RecyclingFrame

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem positive_spec (env : HostEnv Unit) (initial store : Store Unit) (base : UInt64)
    (heap : Heap) (node : FreeNode) (bytes : ByteArray) (frame : Locals) (fuel v : UInt64)
    (hArena : Arena initial base bytes.size heap store) (hBuffer : Buffer base heap store node bytes)
    (hRunning : Running frame fuel v node.root bytes.size)
    (hLow : frame.get 10 = some (.i64 (v % 128)))
    (hSize : bytes.size < 5) (hFit32 : base.toNat + 560 < 4294967296)
    (hFit : base.toNat + 560 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      Finished result fuel (allocatedNode heap.top 8 heap.nodes).root (bytes.size + 1) →
      Arena initial base (bytes.size + 1) (heap.allocate 8) final →
      Buffer base (heap.allocate 8) final (allocatedNode heap.top 8 heap.nodes) (bytes.push (v % 128).toUInt8) →
      wp «module» rest Q final result env) :
    wp «module» (positive ++ rest) Q store frame env := by
  have hParams := hRunning.params
  have hLocals := hRunning.locals
  have hValues := hRunning.values
  have hPointer := hRunning.pointer
  have hLength := hRunning.size
  have hFuel := hRunning.fuel
  have hNeed := need_small bytes hSize
  have hBump := hArena.bump hSize hFit32 hFit hCap
  simp only [Locals.get, hParams, hLocals, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] at hLow hPointer hLength hFuel
  rw [positive_shape]
  simp only [List.append_assoc]
  simp only [positiveHead, positiveTail, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hLow, hPointer, hLength, byte_mask]
  apply PackedPush.program_spec 29 «module» env store heap _ node.root bytes (v % 128).toUInt8
    hArena.heapAt hBuffer.values hBuffer.protection (by omega)
    (by simpa only [hNeed] using fun _ => hBump) (hArena.pages.le.trans hPages) rfl
    (by simpa [List.length_set, hParams]) (by simp [List.length_set, hParams, hLocals]) rfl
    (by
      dsimp only
      repeat apply I64Values.set
      exact hRunning.typed)
    (by simp [Locals.get, hParams, hLocals, List.getElem?_set])
    (by simp [Locals.get, hParams, hLocals, List.getElem?_set])
    (by simp [Locals.get, hParams, hLocals, List.getElem?_set])
  intro final result hResult hPreserved hOutput hPageEq
  rw [hNeed] at hResult hOutput hPageEq
  obtain ⟨hFinalArena, hFinalBuffer⟩ := hArena.pushed hSize hFit32 hFit hOutput hPageEq
  have hResultParams : result.params.length = 5 := by rw [hPreserved.1]; exact hParams
  have hResultLocals : result.locals.length = 36 := by simpa [List.length_set, hLocals] using hPreserved.2.1
  have hResultFuel := hPreserved.2.2.2 0 (Or.inl (by decide))
  have hResultLength := hPreserved.2.2.2 14 (Or.inl (by decide))
  simp only [Locals.get] at hResultFuel hResultLength
  simp only [hParams, hLocals, hResultParams, hResultLocals, List.getElem?_set,
    List.length_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte, hFuel] at hResultFuel hResultLength
  wp_packed_frame [hResult, hResultParams, hResultLocals, hResultLength]
  apply hNext _ _ ?_ hFinalArena hFinalBuffer
  refine ⟨⟨?_, ?_, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hResultParams
  · simpa only [List.length_set] using hResultLocals
  · repeat apply I64Values.set
    exact hPreserved.2.2.1
  all_goals simp only [Locals.get, hResultParams, hResultLocals, List.getElem?_set,
    List.length_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    hResultFuel, ← UInt64.ofNat_add, allocatedNode]

  all_goals exact congrArg (fun word => some (Value.i64 word)) (UInt64.ofNat_add bytes.size 1).symm

#print axioms positive_spec
end Project.LebU32.Recycling
