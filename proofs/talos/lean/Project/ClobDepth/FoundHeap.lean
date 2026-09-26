import Project.ClobDepth.MissingHeap
import Project.ClobDepth.FoundBranch

namespace Project.ClobDepth.FoundHeap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Properties Project.ClobDepth.Representation
  Project.ClobDepth.HeapProof Project.EulerRiemann.Execution

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem foundProg_spec (env : HostEnv Unit) (st : Store Unit) (heap : Heap)
    (owner price qty : UInt64) (source : FreeNode) (levels : List LevelL) (i : Nat)
    (hLength : levels.length < 4294967296) (hIndex : priceIdx levels price = some i)
    (hHeap : heap.At st) (hOwner : OwnsLevels heap st source levels)
    (hFit32 : heap.top.toNat + 48 + (fixedArrayBytesU levels.length 2).toNat < 4294967296)
    (hFit : heap.top.toNat + 48 + (fixedArrayBytesU levels.length 2).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ st1,
      AllocatedResult st heap (fixedArrayBytesU levels.length 2) st1
        (levels.set i { lprice := price, lqty := levels[i]!.lqty + qty }) →
      ∀ final, FoundBranch.ResultLocalsAt final
        (allocatedRoot heap.top (fixedArrayBytesU levels.length 2) heap.nodes) →
      wp «module» rest Q st1 final env) :
    wp «module» (Entry.foundProg ++ rest) Q st
      (FoundPrepare.branchFrame owner source.root price qty levels i) env := by
  let need := fixedArrayBytesU levels.length 2
  let target := allocatedRoot heap.top need heap.nodes
  let capacity := allocatedCapacity need heap.nodes
  let prepared := AllocationEntry.foundCapacityFrame owner source.root price qty levels i
  have hi := priceIdx_some_lt hIndex
  have hNeed : need.toNat = fixedArrayBytes levels.length 2 := by
    apply fixedArrayBytesU_toNat
    · rw [size_eq]; omega
    · decide
    · unfold fixedArrayBytes; rw [size_eq]; omega
  have hReady := initialize_copy st heap need levels.length source levels
    hHeap hOwner hNeed.ge (fun _ => hFit32) (fun _ => hFit)
  have hTotalU : (UInt64.ofNat levels.length * 2).toNat = levels.length * 2 := by
    rw [UInt64.toNat_mul, toNat_ofNat_lt (by rw [size_eq]; omega)]
    change (levels.length * 2) % 18446744073709551616 = _
    omega
  have hTotal64 : levels.length * 2 < UInt64.size := by rw [size_eq]; omega
  rw [Entry.foundProg_decomposition]
  simp only [List.append_assoc]
  apply FoundPrepare.foundPrepareProg_spec env st owner source.root price qty levels
    i hLength hIndex hOwner.buffer.contents.2
  simp only [FoundPrepare.prepareFrame, List.cons_append, List.nil_append]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  rw [AllocationEntry.found_decomposition]
  simp only [List.append_assoc]
  apply AllocationEntry.foundCapacity_spec env st owner source.root price qty levels i hLength
  change wp «module» (FixedArrayAllocate.program 24 2 ++ _) _ st
    (FixedArraySearch.frame prepared.params (prepared.locals.take 20) [] need
      (UInt64.ofNat i) (UInt64.ofNat i + 1) 1 0 0) env
  apply allocation_program env st heap prepared.params (prepared.locals.take 20) [] 24 rfl
    need 2 (UInt64.ofNat i) (UInt64.ofNat i + 1) 1 0 0 hHeap
    (fun _ => ⟨hFit32.le, hFit⟩) hPages
  intro previous current oldCapacity next
  let allocatedFrame := FixedArraySearch.frame prepared.params (prepared.locals.take 20) []
    need previous current oldCapacity next target
  let copyBase := MissingFinish.finishFrame allocatedFrame target
  have hLocals : copyBase.locals.length = 26 := rfl
  have hValues : copyBase.values = [] := rfl
  have hCounter : copyBase.locals[15]? = some (.i64 0) := rfl
  have hInit := FoundCopyInvariant.initial (initialized st heap need levels.length)
    copyBase target source.root capacity levels hLocals hValues hCounter
    hReady.fresh hReady.length hReady.sourceRead
  apply AllocationEntry.finish_spec env (heap.allocateArrayStore st need 2) allocatedFrame
    target (UInt64.ofNat levels.length) 12 rfl rfl rfl rfl (by decide) rfl
    (by
      have hBound := hReady.memoryBound
      change target.toNat % 4294967296 + 8 ≤ _
      change target.toNat + (levels.length * 2 + 1) * 8 ≤
        (heap.allocateArrayStore st need 2).mem.pages * 65536 at hBound
      omega)
  apply FoundCopy.foundCopyProg_spec env (initialized st heap need levels.length)
    copyBase target source.root capacity levels rfl hLocals hValues rfl rfl rfl hTotalU hTotal64
    hReady.rootBound hReady.sourceBound hReady.addressBound hReady.memoryBound hReady.separated
  · exact hInit
  · intro st1 hInvariant
    apply FoundStore.foundStoreProg_spec env (initialized st heap need levels.length)
      st1 copyBase target source.root capacity price (levels[i]!.lqty + qty) levels i
      rfl hLocals hValues rfl rfl rfl rfl hInvariant hi hTotalU hTotal64
      hReady.rootBound hReady.sourceBound hReady.addressBound hReady.memoryBound hReady.separated
    intro st2 hFinish
    have hResult : AllocatedResult st heap need st2
        (levels.set i { lprice := price, lqty := levels[i]!.lqty + qty }) := by
      refine allocated_result st st2 heap need _ hHeap (by simpa only [List.length_set] using hNeed.ge)
        (fun _ => hFit32) (fun _ => hFit) hFinish.pages hFinish.globals hFinish.levelsOwned ?_
      simpa only [List.length_set] using
        (show MemEqOutsideFlatWords (heap.allocateArrayStore st need 2) st2 target
          (levels.length * 2) from
          fun address hOutside => (hFinish.outside address hOutside).trans (hReady.outside address hOutside))
    simp (config := { maxSteps := 1000000 }) [wp_simp,
      Entry.foundResultProg, List.cons_append, List.nil_append,
      FoundStore.storeResultFrame, MissingCopyInvariant.copyLoopFrame,
      copyBase, MissingFinish.finishFrame, allocatedFrame, FixedArraySearch.frame,
      prepared, AllocationEntry.foundCapacityFrame, FoundAllocPrepare.allocFrame,
      Locals.get, Locals.set?, List.take, List.drop, List.length,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine hNext st2 hResult _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [target, need]

#print axioms foundProg_spec
end Project.ClobDepth.FoundHeap
