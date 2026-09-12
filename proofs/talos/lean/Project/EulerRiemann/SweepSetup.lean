import Project.EulerRiemann.AllocationPreserve
import Project.EulerRiemann.SweepLoopShape
import Project.ProofKit.FixedArrayResult

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.FixedArrayResult

def sweepParameters (n : Nat) (axis : Bool) (ratio owner source : UInt64) : List Wasm.Value :=
  [.i64 (UInt64.ofNat n), .i64 (boolWord axis), .i64 ratio, .i64 owner, .i64 source]

def sweepSaved (source : UInt64) (count : Nat) : List Wasm.Value :=
  List.replicate 36 (.i64 0) ++
    [.i64 source, .i64 (UInt64.ofNat count), .i64 0, .i64 0, .i64 0, .i64 0]

theorem sweep_entry_shape : func70.take 6 =
    [.localGet 4, .localSet 41, .localGet 41, .wrapI64, .load64 0, .localSet 42] := rfl

theorem sweep_install_shape : (func70.drop 39).take 8 =
    [.localGet 52, .localSet 43] ++ lengthStoreLocalProgram 43 42 ++
      [.constI64 0, .localSet 44] := rfl

theorem sweep_saved_length (source : UInt64) (count : Nat) :
    (sweepSaved source count).length = 42 := by simp [sweepSaved]

theorem sweep_saved_count (source : UInt64) (count : Nat) :
    (sweepSaved source count)[37]? = some (.i64 (UInt64.ofNat count)) := by simp [sweepSaved]

theorem sweep_entry_spec (env : HostEnv Unit) (store : Store Unit) (n : Nat) (axis : Bool)
    (ratio owner source : UInt64) (grid : Array Traversal.Cell) (hGrid : Memory.GridAt store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame (sweepParameters n axis ratio owner source) (sweepSaved source grid.size)
        0 0 0 0 0 0) env) :
    wp Project.EulerRiemann.«module» (func70.take 6 ++ rest) Q store
      (func70Def.toLocals (sweepParameters n axis ratio owner source)) env := by
  rw [sweep_entry_shape]
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  simp only [UInt64.toNat_toUInt32] at hBound
  simpa [wp_simp, func70Def, Function.toLocals, Function.numParams, Function.numLocals,
    ValueType.zero, sweepParameters, sweepSaved, allocationFrame, List.replicate,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, hLength, hBound] using hNext

theorem sweep_install_spec (env : HostEnv Unit) (store : Store Unit) (n : Nat) (axis : Bool)
    (ratio owner source target need previous current capacity next : UInt64) (count : Nat)
    (hBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (writeLength store target (UInt64.ofNat count))
      (sweepFrame n axis ratio owner source target count 0 {}
        [.i64 0, .i64 0, .i64 need, .i64 previous, .i64 current, .i64 capacity,
          .i64 next, .i64 target]) env) :
    wp Project.EulerRiemann.«module» ((func70.drop 39).take 8 ++ rest) Q store
      (allocationFrame (sweepParameters n axis ratio owner source) (sweepSaved source count)
        need previous current capacity next target) env := by
  rw [sweep_install_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp [wp_simp, allocationFrame, sweepParameters, sweepSaved]
  refine lengthStoreLocal_spec _ env store _ target (UInt64.ofNat count) 43 42 ?_ ?_
    hBound Q _ ?_
  · simp [Locals.get]
  · simp [Locals.get]
  · simpa [wp_simp, sweepFrame, writeLength] using hNext

#print axioms sweep_entry_shape
#print axioms sweep_install_shape
#print axioms sweep_saved_length
#print axioms sweep_saved_count
#print axioms sweep_entry_spec
#print axioms sweep_install_spec

end Project.EulerRiemann.Execution
