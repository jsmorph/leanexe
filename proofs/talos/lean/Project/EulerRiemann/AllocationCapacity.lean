import Project.EulerRiemann.AllocationExecute
import Project.ProofKit.FixedArrayCapacity

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.FixedArrayCapacity

theorem sweep_capacity_shape : (func70.drop 6).take 18 = localProgram 42 7 47 := rfl

theorem sweep_capacity_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (length need previous current capacity next result : UInt64)
    (hLength : saved[37]? = some (.i64 length)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame params saved (normalizedCapacity length 7) previous current capacity
        next result) env) :
    wp Project.EulerRiemann.«module» ((func70.drop 6).take 18 ++ rest) Q store
      (allocationFrame params saved need previous current capacity next result) env := by
  rw [sweep_capacity_shape]
  refine localProgram_spec 42 length 7 47 _ env store _ ?_ rfl ?_ ?_ Q rest ?_
  · obtain ⟨hLengthBound, hLengthRead⟩ := List.getElem_of_getElem? hLength
    simp [allocationFrame, Locals.get, hParams, hPrefix, hLengthRead]
  · simp [allocationFrame, hParams]
  · simp [allocationFrame, Locals.validIndex, hParams, hPrefix]
  · simpa [capacityFrame, allocationFrame, hParams, hPrefix] using hNext

theorem sweep_capacity_toNat (length : UInt64) (hLength : length.toNat ≤ 640000) :
    (normalizedCapacity length 7).toNat = 8 + length.toNat * 56 := by
  have hRaw : (unnormalizedCapacity length 7).toNat = 8 + length.toNat * 56 := by
    have h8 : (8 : UInt64).toNat = 8 := rfl
    have h7 : (7 : UInt64).toNat = 7 := rfl
    unfold unnormalizedCapacity
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, h8, h7]
    norm_num
    omega
  have hNotSmall : ¬unnormalizedCapacity length 7 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hRaw]
    change ¬8 + length.toNat * 56 < 8
    omega
  simp only [normalizedCapacity, ite_eq_right hNotSmall, hRaw]

#print axioms sweep_capacity_shape
#print axioms sweep_capacity_spec
#print axioms sweep_capacity_toNat

end Project.EulerRiemann.Execution
