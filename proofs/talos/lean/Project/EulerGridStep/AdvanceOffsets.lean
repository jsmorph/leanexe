import Project.EulerGridStep.NeighborIndexing
import Project.EulerGridStep.Helpers

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def advanceEntryFrame (ratio inputUnused pointer unused output : UInt64) (index : Nat) : Locals :=
  { params := [.i64 ratio, .i64 inputUnused, .i64 pointer, .i64 unused, .i64 output, .i64 (UInt64.ofNat index)],
    locals := List.replicate 62 (.i64 0), values := [] }

def advanceOffsets : Wasm.Program := func35.take 47

def advanceOffsetsFrame (ratio inputUnused pointer unused output : UInt64) (size index : Nat) : Locals :=
  { advanceEntryFrame ratio inputUnused pointer unused output index with
    locals := ((((((advanceEntryFrame ratio inputUnused pointer unused output index).locals.set
      0 (.i64 (UInt64.ofNat (3 * index)))).set
      1 (.i64 (UInt64.ofNat (previousOffset index)))).set
      2 (.i64 (UInt64.ofNat (nextOffset size index)))).set
      59 (.i64 (if index + 1 < size / 3 then UInt64.ofNat (3 * index) else UInt64.ofNat size))).set
      60 (.i64 3)).set
      61 (.i64 (if index + 1 < size / 3 then UInt64.ofNat (3 * index + 3) else pointer)) }

macro "advance_offsets_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceOffsets, func35, advanceEntryFrame, List.set,
        List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine ⟨by omega, ?_⟩
    | (try rw [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add])

/-- Exact first47 instructions compute safe transmissive neighbor offsets. -/
theorem advance_offsets_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      (advanceOffsetsFrame ratio inputUnused pointer unused output input.size index) env) :
    wp m (advanceOffsets ++ rest) Q initial
      (advanceEntryFrame ratio inputUnused pointer unused output index) env := by
  have hSize32 := input_size_lt_32 initial pointer input hArray
  have hSize64 := hArray.size_lt
  have hi32 : index < 4294967296 := by omega
  have hi64 : index < UInt64.size := by omega
  have hIndexNat := UInt64.toNat_ofNat_of_lt' hi64
  have hOffsetNat := UInt64.toNat_ofNat_of_lt' (show 3 * index < UInt64.size by omega)
  have hMul := triple_mul_word index
  have hAdd1 : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := (UInt64.ofNat_add index 1).symm
  have hAdd3 : UInt64.ofNat (3 * index) + 3 = UInt64.ofNat (3 * index + 3) := (UInt64.ofNat_add (3 * index) 3).symm
  have hGuard1 := neighbor_add_guard index 1 hi32 (by decide)
  have hGuard3 := neighbor_add_guard (3 * index) 3 (by omega) (by decide)
  change ¬ (UInt64.ofNat index + 1 < UInt64.ofNat index) at hGuard1
  change ¬ (UInt64.ofNat (3 * index) + 3 < UInt64.ofNat (3 * index)) at hGuard3
  rw [hAdd1] at hGuard1
  rw [hAdd3] at hGuard3
  have hNextTest := next_cell_word_test input.size index hSize32 hi
  rw [hAdd1] at hNextTest
  have hLengthBound := hArray.generatedLengthBound
  have hLengthSafe := Nat.not_lt.mpr hLengthBound
  have hLengthRead := hArray.lengthRead
  have hPointerAddress := hArray.pointerAddress_eq
  by_cases hz : index = 0
  · subst index
    change ((1 : UInt64) < UInt64.ofNat input.size / 3) ↔ 1 < input.size / 3 at hNextTest
    by_cases hn : 1 < input.size / 3
    all_goals
      advance_offsets_peel
      simpa [advanceOffsetsFrame, advanceEntryFrame, previousOffset, nextOffset, hn] using hNext
  · have hWordZero : UInt64.ofNat index ≠ 0 := by
      intro hw
      have := congrArg UInt64.toNat hw
      rw [hIndexNat] at this
      exact hz this
    have hMulGuard := triple_mul_guard index hi32 (by omega)
    have hSub : UInt64.ofNat (3 * index) - 3 = UInt64.ofNat (3 * index - 3) :=
      (UInt64.ofNat_sub (by omega : 3 ≤ 3 * index)).symm
    have hSubGuard : ¬ (UInt64.ofNat (3 * index) < 3) := by
      rw [UInt64.lt_iff_toNat_lt, hOffsetNat]
      change ¬ 3 * index < 3
      omega
    by_cases hn : index + 1 < input.size / 3
    all_goals
      advance_offsets_peel
      simpa [advanceOffsetsFrame, advanceEntryFrame, previousOffset, nextOffset, hz, hn] using hNext

#print axioms advance_offsets_spec
end Project.EulerGridStep.Execution
