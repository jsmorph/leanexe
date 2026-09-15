import Project.EulerReconstructed.RetryShape
import Project.EulerReconstructed.HeapAllocate
import Project.EulerRiemann.HeapEmpty
import Project.ProofKit.FixedArraySearchPrepare

namespace Project.EulerReconstructed.Execution
open Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayResult

def retryFailureSaved (saved : List Wasm.Value) (status dt : UInt64) : List Wasm.Value :=
  (saved.set 1 (.i64 status)).set 2 (.i64 dt)

def retryFailureFrame (params saved : List Wasm.Value)
    (status dt previous current capacity next root : UInt64) : Locals :=
  finishFrame (resultFrame (FixedArraySearch.frame params (retryFailureSaved saved status dt) []
    8 previous current capacity next root) 69 root) 11 12 root

theorem retry_failure_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 8) (hSaved : saved.length = 71)
    (status dt need previous current capacity next result : UInt64)
    (hDt : params[4]? = some (.i64 dt)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.«module» rest Q store
      (FixedArraySearch.frame params (retryFailureSaved saved status dt) []
        8 previous current capacity next result) env) :
    wp Project.EulerReconstructed.«module» ([.constI64 status, .localSet 9, .localGet 4, .localSet 10] ++
      FixedArrayCapacity.constantProgram 0 7 79 ++ rest) Q store
      (FixedArraySearch.frame params saved [] need previous current capacity next result) env := by
  obtain ⟨hDtBound, hDtRead⟩ := List.getElem_of_getElem? hDt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp [wp_simp, FixedArraySearch.frame, hParams, hSaved, hDtRead]
  change wp Project.EulerReconstructed.«module» (FixedArrayCapacity.constantProgram 0 7 79 ++ rest) Q store
    (FixedArraySearch.frame params (retryFailureSaved saved status dt) []
      need previous current capacity next result) env
  apply FixedArrayCapacity.constantProgram_spec 0 7 79 Project.EulerReconstructed.«module» env store _ rfl
    (by simp [FixedArraySearch.frame, hParams])
    (by simp [Locals.validIndex, FixedArraySearch.frame, retryFailureSaved, hParams, hSaved])
  have hStart : params.length + (retryFailureSaved saved status dt).length = 79 := by
    simp [retryFailureSaved, hParams, hSaved]
  rw [← hStart, FixedArraySearch.capacityFrame_need]
  exact hNext

theorem retry_failure_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved : List Wasm.Value) (hParams : params.length = 8) (hSaved : saved.length = 71)
    (status dt need previous current capacity next result : UInt64)
    (hDt : params[4]? = some (.i64 dt)) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + 8 ≤ 4294967296 ∧ bumpPages heap.top 8 ≤ store.memoryCap Project.EulerReconstructed.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next,
      wp Project.EulerReconstructed.«module» rest Q (heap.emptyStore store)
        (retryFailureFrame params saved status dt previous current capacity next
          (allocatedRoot heap.top 8 heap.nodes)) env) :
    wp Project.EulerReconstructed.«module» (retryFailureProgram status ++ rest) Q store
      (FixedArraySearch.frame params saved [] need previous current capacity next result) env := by
  have hStart : params.length + (retryFailureSaved saved status dt).length = 79 := by
    simp [retryFailureSaved, hParams, hSaved]
  have hBounds := heap.allocate_grid_bounds store 8 0 hHeap (by decide) (fun h => (hBump h).1)
  have hAddress : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat + 8 ≤
      (heap.allocateStore store 8).mem.pages * 65536 := by
    rw [Project.ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
    exact hBounds.2
  unfold retryFailureProgram
  simp only [List.append_assoc]
  apply retry_failure_prepare_spec env store params saved hParams hSaved status dt need
    previous current capacity next result hDt
  apply heap_allocation_program_spec env store heap params (retryFailureSaved saved status dt) []
    79 hStart 8 previous current capacity next result hHeap hBump hPages
  intro previous current capacity next
  let root := allocatedRoot heap.top 8 heap.nodes
  let base := FixedArraySearch.frame params (retryFailureSaved saved status dt) []
    8 previous current capacity next root
  have hBaseParams : base.params.length = 8 := hParams
  have hBaseLocals : base.locals.length = 77 := by
    simp [base, FixedArraySearch.frame, retryFailureSaved, hSaved]
  have hRoot : base.get 84 = some (.i64 root) := by
    simp [base, FixedArraySearch.frame, Locals.get, hParams, retryFailureSaved, hSaved]
  have hValid69 : base.validIndex 69 := by
    simp [Locals.validIndex, hBaseParams, hBaseLocals]
  change wp Project.EulerReconstructed.«module» (resultProgram 84 69 ++ lengthStoreProgram 69 0 ++
    finishProgram 69 11 12 ++ rest) Q (heap.allocateStore store 8) base env
  simp only [List.append_assoc]
  apply resultProgram_spec 84 69 Project.EulerReconstructed.«module» env _ base root rfl hRoot (by omega) hValid69
  have hInstalledRoot := resultFrame_get_result base 69 root (by omega) hValid69
  apply lengthStore_spec Project.EulerReconstructed.«module» env _ _ root 0 69 rfl hInstalledRoot hAddress
  apply finishProgram_spec Project.EulerReconstructed.«module» env _ _ root 69 11 12 rfl hInstalledRoot
    (by simp [resultFrame_params, hBaseParams])
    (by simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hBaseParams, hBaseLocals])
    (by simp [resultFrame_params, hBaseParams])
    (by simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hBaseParams, hBaseLocals])
  exact hNext previous current capacity next

#print axioms retry_failure_prepare_spec
#print axioms retry_failure_program_spec

end Project.EulerReconstructed.Execution
