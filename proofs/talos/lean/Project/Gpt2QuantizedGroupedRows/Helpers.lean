import Project.Gpt2QuantizedGroupedRows.ProjectionRegion
import Project.Gpt2QuantizedLinearRows.Dot
import Project.Gpt2QuantizedLinearRows.Rows

namespace Project.Gpt2QuantizedGroupedRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized Project.Gpt2QuantizedLinearRows.QuantizeRows

theorem dot_exact (env : HostEnv Unit) (initial : Store Unit)
    (weightOwner weightPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset inputOffset width : Nat)
    (hweights : ByteArrayAt initial.mem weightPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hweightSize : weightOffset + width ≤ weights.size)
    (hinputSize : inputOffset + width ≤ input.size) :
    TerminatesWith env «module» 4 initial
      [.i64 (UInt64.ofNat width), .i64 (UInt64.ofNat inputOffset),
        .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat input.size),
        .i64 inputPtr, .i64 inputOwner, .i64 (UInt64.ofNat weights.size),
        .i64 weightPtr, .i64 weightOwner]
      (fun final values => final = initial ∧
        values = [.i64 (dot weights input weightOffset inputOffset width).toUInt64]) := by
  exact Project.FunctionRegion.terminatesWith ProjectionRegion.shift 4
    (by simp [ProjectionRegion.domain]) (Project.Gpt2QuantizedLinearRows.dot_exact
      env initial weightOwner weightPtr inputOwner inputPtr weights input weightOffset inputOffset width hweights hinput hweightSize hinputSize)

#print axioms dot_exact

theorem rescale_exact (env : HostEnv Unit) (initial : Store Unit)
    (accumulator inputScale weightScale : UInt32) :
    TerminatesWith env «module» 6 initial
      [.i64 weightScale.toUInt64, .i64 inputScale.toUInt64, .i64 accumulator.toUInt64]
      (fun final values => final = initial ∧
        values = [.i64 (rescale accumulator inputScale weightScale).toUInt64]) := by
  exact Project.FunctionRegion.terminatesWith ProjectionRegion.shift 6
    (by simp [ProjectionRegion.domain]) (Project.Gpt2QuantizedLinearRows.rescale_exact
      env initial accumulator inputScale weightScale)

#print axioms rescale_exact

theorem quantizeRows_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr : UInt64) (input : ByteArray) (width rows : Nat)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hInputProtected : heap.Protects ptr.toNat (ptr.toNat + input.size))
    (hCount : 4 * rows ≤ 2^32)
    (hScaleBump : takeFirstFitFrom 0 (scaleNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (scaleNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scaleNeed rows) ≤ initial.memoryCap «module» 0)
    (hByteBump : let next := heap.allocate (scaleNeed rows)
      takeFirstFitFrom 0 (byteNeed width rows) next.nodes = none →
        next.top.toNat + 48 + (byteNeed width rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (byteNeed width rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env «module» 3 initial
      [.i64 (UInt64.ofNat rows), .i64 (UInt64.ofNat width),
        .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * rows)), .i64 (scaleNode heap rows).root,
          .i64 (scaleNode heap rows).root, .i64 (UInt64.ofNat (rows * width)),
          .i64 (valueNode heap width rows).root, .i64 (valueNode heap width rows).root] ∧
        Project.Gpt2QuantizedLinearRows.QuantizeRows.Output heap initial final input width rows) := by
  exact Project.FunctionRegion.terminatesWith ProjectionRegion.shift 3
    (by simp [ProjectionRegion.domain]) (Project.Gpt2QuantizedLinearRows.quantizeRows_exact
      env initial heap owner ptr input width rows hHeap hInput hInputSize hInputProtected hCount hScaleBump hByteBump hPages)

#print axioms quantizeRows_exact

end Project.Gpt2QuantizedGroupedRows
