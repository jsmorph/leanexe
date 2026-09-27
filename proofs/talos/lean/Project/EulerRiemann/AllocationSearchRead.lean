import Project.EulerRiemann.AllocationReuse

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.Memory

def searchRead : Wasm.Program :=
  [.localGet 49, .constI64 32, .subI64, .wrapI64, .load64 0, .localSet 50,
    .localGet 49, .constI64 8, .subI64, .wrapI64, .load64 0, .localSet 51]

theorem sweep_search_read_shape : (sweepSearch.drop 8).take 12 = searchRead := rfl

theorem searchRead_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need previous root capacity next result oldCapacity oldNext : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296)
    (hFit : root.toNat ≤ store.mem.pages * 65536)
    (hCapacityRead : store.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : store.mem.read64 (root - 8).toUInt32 = next)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame params saved need previous root capacity next result) env) :
    wp Project.EulerRiemann.«module» (searchRead ++ rest) Q store
      (allocationFrame params saved need previous root oldCapacity oldNext result) env := by
  have hBound (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [toUInt32_toNat, toNat_sub_of_le root offset (by omega)]
    omega
  have hCapacityBound : (root.toUInt32 - 32).toNat + 8 ≤ store.mem.pages * 65536 := by
    simpa using hBound 32 (by decide) (by decide)
  have hNextBound : (root.toUInt32 - 8).toNat + 8 ≤ store.mem.pages * 65536 := by
    simpa using hBound 8 (by decide) (by decide)
  have hCapacityRead' : store.mem.read64 (root.toUInt32 - 32) = capacity := by
    simpa using hCapacityRead
  have hNextRead' : store.mem.read64 (root.toUInt32 - 8) = next := by
    simpa using hNextRead
  unfold searchRead
  simpa [wp_simp, allocationFrame, hParams, hPrefix, Nat.reducePow, ← toUInt32_eq_ofNat,
    hCapacityRead', hNextRead', Nat.not_lt.mpr hCapacityBound, Nat.not_lt.mpr hNextBound]
    using hNext

def searchAdvance : Wasm.Program := [.localGet 49, .localSet 48, .localGet 51, .localSet 49]

theorem sweep_search_advance_shape :
    sweepSearch[23]? = some (.iff 0 0 sweepFit searchAdvance) := rfl

theorem searchAdvance_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need previous root capacity next result : UInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame params saved need root next capacity next result) env) :
    wp Project.EulerRiemann.«module» (searchAdvance ++ rest) Q store
      (allocationFrame params saved need previous root capacity next result) env := by
  unfold searchAdvance
  simpa [wp_simp, allocationFrame, hParams, hPrefix] using hNext

#print axioms sweep_search_read_shape
#print axioms searchRead_spec
#print axioms sweep_search_advance_shape
#print axioms searchAdvance_spec

end Project.EulerRiemann.Execution
