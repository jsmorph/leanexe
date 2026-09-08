import Project.EulerGridStep.AdvanceReadLeft
import Project.EulerGridStep.AdvanceReadCentre
import Project.EulerGridStep.AdvanceReadRight

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.EulerGridScan.Execution
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def advanceCellArguments (ratio : UInt64) (input : Array UInt64) (index : Nat) : List Value :=
  [.i64 (input.getD (nextOffset input.size index + 2) 0),
    .i64 (input.getD (nextOffset input.size index + 1) 0),
    .i64 (input.getD (nextOffset input.size index) 0),
    .i64 (input.getD (3 * index + 2) 0),
    .i64 (input.getD (3 * index + 1) 0),
    .i64 (input.getD (3 * index) 0),
    .i64 (input.getD (previousOffset index + 2) 0),
    .i64 (input.getD (previousOffset index + 1) 0),
    .i64 (input.getD (previousOffset index) 0),
    .i64 (ratio)]

def advanceReadFrame (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64)
    (index : Nat) : Locals :=
  { advanceEntryFrame ratio inputUnused pointer unused output index with
    locals := [.i64 (UInt64.ofNat (3 * index)),
      .i64 (UInt64.ofNat (previousOffset index)),
      .i64 (UInt64.ofNat (nextOffset input.size index)),
      .i64 (ratio),
      .i64 (pointer),
      .i64 (UInt64.ofNat (previousOffset index)),
      .i64 (input.getD (previousOffset index) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (previousOffset index + 1)),
      .i64 (input.getD (previousOffset index + 1) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (previousOffset index + 2)),
      .i64 (input.getD (previousOffset index + 2) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (3 * index)),
      .i64 (input.getD (3 * index) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (3 * index + 1)),
      .i64 (input.getD (3 * index + 1) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (3 * index + 2)),
      .i64 (input.getD (3 * index + 2) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (nextOffset input.size index)),
      .i64 (input.getD (nextOffset input.size index) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (nextOffset input.size index + 1)),
      .i64 (input.getD (nextOffset input.size index + 1) 0),
      .i64 (pointer),
      .i64 (UInt64.ofNat (nextOffset input.size index + 2)),
      .i64 (input.getD (nextOffset input.size index + 2) 0)] ++ List.replicate 28 (.i64 0) ++
      [.i64 pointer, .i64 (UInt64.ofNat (nextOffset input.size index + 2)),
        .i64 (UInt64.ofNat (nextOffset input.size index + 2))],
    values := advanceCellArguments ratio input index }

def advanceReads : Wasm.Program := (func35.drop 47).take 189

theorem advance_reads_shape : advanceReads =
    (func35.drop 47).take 15 ++
    (func35.drop 62).take 23 ++
    (func35.drop 85).take 23 ++
    (func35.drop 108).take 13 ++
    (func35.drop 121).take 23 ++
    (func35.drop 144).take 23 ++
    (func35.drop 167).take 13 ++
    (func35.drop 180).take 23 ++
    (func35.drop 203).take 23 ++ (func35.drop 226).take 10 := rfl

/-- Nine independently checked loads stage the exact cell arguments without changing memory. -/
theorem advance_reads_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (advanceReadFrame ratio inputUnused pointer unused output input index) env) :
    wp m (advanceReads ++ rest) Q initial
      (advanceOffsetsFrame ratio inputUnused pointer unused output input.size index) env := by
  rw [advance_reads_shape]
  simp only [List.append_assoc]
  apply advance_read_0_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_1_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_2_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_3_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_4_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_5_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_6_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_7_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_read_8_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  wp_run [func35, advanceReadStageFrame, advanceReadIndex, advanceReadOffset, advanceOffsetsFrame,
    advanceEntryFrame, List.set, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.add_zero]
  simpa [advanceReadFrame, advanceCellArguments, advanceEntryFrame,
    -UInt64.ofNat_mul, -UInt64.ofNat_add] using hNext

#print axioms advance_reads_shape
#print axioms advance_reads_spec
end Project.EulerGridStep.Execution
