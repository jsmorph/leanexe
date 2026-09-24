import Project.EulerReconstructed.FrozenSweepLoopShape
import Project.EulerRiemann.FrozenAllocationPreserve
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.FixedArrayResult

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit
open Project.ProofKit.FixedArrayCapacity Project.ProofKit.FixedArrayResult
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution (boolWord allocatedStore allocatedRoot countedStore)

def sweepParameters (n : Nat) (fuel : UInt64) (axis : Bool) (ratio owner source : UInt64) : List Value :=
  [.i64 (UInt64.ofNat n), .i64 fuel, .i64 (boolWord axis), .i64 ratio, .i64 owner, .i64 source]

def sweepSaved (source : UInt64) (count : Nat) : List Value :=
  List.replicate 37 (.i64 0) ++
    [.i64 source, .i64 (UInt64.ofNat count), .i64 0, .i64 0, .i64 0, .i64 0]

def sweepAllocationFrame (params saved : List Value)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame params saved [] need previous current capacity next result

theorem sweep_entry_shape : func121.take 6 =
    [.localGet 5, .localSet 43, .localGet 43, .wrapI64, .load64 0, .localSet 44] := rfl

theorem sweep_capacity_shape :
    (func121.drop 6).take 18 = FixedArrayCapacity.localProgram 44 7 49 := rfl

theorem sweep_allocation_shape :
    (func121.drop 24).take 15 = FixedArrayAllocate.program 49 7 := rfl

theorem sweep_install_shape : (func121.drop 39).take 8 =
    [.localGet 54, .localSet 45] ++ lengthStoreLocalProgram 45 44 ++
      [.constI64 0, .localSet 46] := rfl

theorem sweep_entry_spec (env : HostEnv Unit) (store : Store Unit) (n : Nat)
    (fuel : UInt64) (axis : Bool) (ratio owner source : UInt64)
    (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (hGrid : Memory.GridAt store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store
      (sweepAllocationFrame (sweepParameters n fuel axis ratio owner source)
        (sweepSaved source grid.size) 0 0 0 0 0 0) env) :
    wp Project.EulerReconstructed.Frozen.«module» (func121.take 6 ++ rest) Q store
      (func121Def.toLocals (sweepParameters n fuel axis ratio owner source)) env := by
  rw [sweep_entry_shape]
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  simp only [UInt64.toNat_toUInt32] at hBound
  simpa [wp_simp, func121Def, Function.toLocals, Function.numParams, Function.numLocals,
    ValueType.zero, sweepParameters, sweepSaved, sweepAllocationFrame, FixedArraySearch.frame,
    List.replicate, ← Project.ProofKit.Memory.toUInt32_eq_ofNat, hLength, hBound] using hNext

theorem sweep_capacity_spec (env : HostEnv Unit) (store : Store Unit) (n : Nat)
    (fuel : UInt64) (axis : Bool) (ratio owner source : UInt64) (count : Nat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store
      (sweepAllocationFrame (sweepParameters n fuel axis ratio owner source)
        (sweepSaved source count) (normalizedCapacity (UInt64.ofNat count) 7) 0 0 0 0 0) env) :
    wp Project.EulerReconstructed.Frozen.«module» ((func121.drop 6).take 18 ++ rest) Q store
      (sweepAllocationFrame (sweepParameters n fuel axis ratio owner source)
        (sweepSaved source count) 0 0 0 0 0 0) env := by
  rw [sweep_capacity_shape]
  apply FixedArrayCapacity.localProgram_spec 44 (UInt64.ofNat count) 7 49
  · simp [sweepAllocationFrame, FixedArraySearch.frame, sweepParameters, sweepSaved, Locals.get]
  · rfl
  · change 6 ≤ 49
    decide
  · change 49 < 55
    decide
  · simpa [capacityFrame, sweepAllocationFrame, FixedArraySearch.frame,
      sweepParameters, sweepSaved] using hNext

theorem sweep_install_spec (env : HostEnv Unit) (store : Store Unit) (n : Nat)
    (fuel : UInt64) (axis : Bool)
    (ratio owner source target need previous current capacity next : UInt64) (count : Nat)
    (hBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q (writeLength store target (UInt64.ofNat count))
      (sweepFrame n fuel axis ratio owner source target count 0 {}
        [.i64 0, .i64 0, .i64 need, .i64 previous, .i64 current, .i64 capacity,
          .i64 next, .i64 target]) env) :
    wp Project.EulerReconstructed.Frozen.«module» ((func121.drop 39).take 8 ++ rest) Q store
      (sweepAllocationFrame (sweepParameters n fuel axis ratio owner source) (sweepSaved source count)
        need previous current capacity next target) env := by
  rw [sweep_install_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp [wp_simp, sweepAllocationFrame, FixedArraySearch.frame, sweepParameters, sweepSaved]
  refine lengthStoreLocal_spec _ env store _ target (UInt64.ofNat count) 45 44 ?_ ?_
    hBound Q _ ?_
  · simp [Locals.get]
  · simp [Locals.get]
  · simpa [wp_simp, sweepFrame, writeLength] using hNext

#print axioms sweep_entry_shape
#print axioms sweep_capacity_shape
#print axioms sweep_allocation_shape
#print axioms sweep_install_shape
#print axioms sweep_entry_spec
#print axioms sweep_capacity_spec
#print axioms sweep_install_spec
end Project.EulerReconstructed.Frozen.Execution
