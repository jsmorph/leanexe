import Project.ClobDepth.AllocationEntry
import Project.ClobDepth.AllocationInit
import Project.ClobDepth.MissingStore

namespace Project.ClobDepth.MissingHeap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The missing-price branch handles both a reused free chunk and a new bump
allocation, then delegates its data movement to the checked copy/store rules. -/
theorem missingProg_spec (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (owner price qty : UInt64) (source : FreeNode) (levels : List LevelL) (f4 f5 : UInt64)
    (hLength : levels.length < 4294967296) (hHeap : heap.At st)
    (hOwner : OwnsLevels heap st source levels)
    (hFit32 : heap.top.toNat + 48 + (fixedArrayBytesU (levels.length + 1) 2).toNat < 4294967296)
    (hFit : heap.top.toNat + 48 + (fixedArrayBytesU (levels.length + 1) 2).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ st1,
      AllocatedResult st heap (fixedArrayBytesU (levels.length + 1) 2) st1
        (levels ++ [{ lprice := price, lqty := qty }]) →
      ∀ final, MissingStore.ResultLocalsAt final
        (allocatedRoot heap.top (fixedArrayBytesU (levels.length + 1) 2) heap.nodes) →
      wp «module» rest Q st1 final env) :
    wp «module» (Entry.missingProg ++ rest) Q st
      (MissingFields.branchFrame owner source.root price qty levels f4 f5) env := by
  let need := fixedArrayBytesU (levels.length + 1) 2
  let target := allocatedRoot heap.top need heap.nodes
  let capacity := allocatedCapacity need heap.nodes
  let prepared := MissingPrepare.prepareFrame owner source.root price qty levels f4 f5
  have hNeed : need.toNat = fixedArrayBytes (levels.length + 1) 2 := by
    apply fixedArrayBytesU_toNat
    · rw [size_eq]; omega
    · decide
    · unfold fixedArrayBytes; rw [size_eq]; omega
  have hReady := initialize_copy st heap need (levels.length + 1) source levels
    hHeap hOwner hNeed.ge (fun _ => hFit32) (fun _ => hFit)
  have hTotalU : (UInt64.ofNat levels.length * 2).toNat = levels.length * 2 := by
    rw [UInt64.toNat_mul, toNat_ofNat_lt (by rw [size_eq]; omega)]
    change (levels.length * 2) % 18446744073709551616 = _
    omega
  have hTotal64 : levels.length * 2 < UInt64.size := by rw [size_eq]; omega
  rw [AllocationEntry.missing_decomposition]
  simp only [List.append_assoc]
  apply MissingFields.missingFieldsProg_spec env st owner source.root price qty levels
    f4 f5 hLength hOwner.buffer.contents.2
  apply AllocationEntry.missingCapacity_spec env st owner source.root price qty levels f4 f5 hLength
  change wp «module» (FixedArrayAllocate.program 24 2 ++ _) Q st
    (FixedArraySearch.frame prepared.params (prepared.locals.take 20) [] need 0 0 0 0 0) env
  apply allocation_program env st heap prepared.params (prepared.locals.take 20) [] 24 rfl
    need 2 0 0 0 0 0 hHeap (fun _ => ⟨hFit32.le, hFit⟩) hPages
  intro previous current oldCapacity next
  let allocatedFrame := FixedArraySearch.frame prepared.params (prepared.locals.take 20) []
    need previous current oldCapacity next target
  let copyBase := MissingFinish.finishFrame allocatedFrame target
  have hLocals : copyBase.locals.length = 26 := rfl
  have hValues : copyBase.values = [] := rfl
  have hCounter : copyBase.locals[15]? = some (.i64 0) := rfl
  have hInit := MissingCopyInvariant.initial (initialized st heap need (levels.length + 1))
    copyBase target source.root capacity levels hLocals hValues hCounter
    hReady.fresh hReady.length hReady.sourceRead
  apply AllocationEntry.finish_spec env (heap.allocateArrayStore st need 2) allocatedFrame
    target (UInt64.ofNat (levels.length + 1)) 13 rfl rfl rfl rfl (by decide) rfl
    (by
      have hBound := hReady.memoryBound
      change target.toNat % 4294967296 + 8 ≤ _
      change target.toNat + ((levels.length + 1) * 2 + 1) * 8 ≤
        (heap.allocateArrayStore st need 2).mem.pages * 65536 at hBound
      omega)
  apply MissingCopy.missingCopyProg_spec env (initialized st heap need (levels.length + 1))
    copyBase target source.root capacity levels rfl hLocals hValues rfl rfl rfl hTotalU hTotal64
    hReady.rootBound hReady.sourceBound hReady.addressBound hReady.memoryBound hReady.separated
  · exact hInit
  · intro st1 hInvariant
    apply MissingStore.missingStoreProg_spec env (initialized st heap need (levels.length + 1))
      st1 copyBase target source.root capacity price qty levels rfl hLocals hValues rfl rfl rfl rfl
      hInvariant hTotalU hTotal64 hReady.rootBound hReady.sourceBound hReady.addressBound
      hReady.memoryBound hReady.separated
    intro st2 hFinish final hResult
    refine hNext st2 ?_ final hResult
    refine allocated_result st st2 heap need (levels ++ [{ lprice := price, lqty := qty }])
      hHeap (by simpa only [List.length_append, List.length_cons, List.length_nil] using hNeed.ge)
      (fun _ => hFit32) (fun _ => hFit) hFinish.pages hFinish.globals hFinish.levelsOwned ?_
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      (show MemEqOutsideFlatWords (heap.allocateArrayStore st need 2) st2 target
        ((levels.length + 1) * 2) from
        fun address hOutside => (hFinish.outside address hOutside).trans (hReady.outside address hOutside))

#print axioms missingProg_spec
end Project.ClobDepth.MissingHeap
