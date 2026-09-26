import Project.Gpt2QuantizedGroupedRows.Linear

open Project.Gpt2QuantizedLinearRows

namespace Project.Gpt2QuantizedGroupedRows.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution Projection

def ExactSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool),
    heap.At initial →
    ByteArrayAt initial.mem weightsPtr.toNat weights →
    ByteArrayAt initial.mem inputPtr.toNat input →
    weightOffset + width * outputWidth ≤ weights.size →
    scaleOffset + outputWidth * 4 ≤ weights.size →
    (withBias = true → biasOffset + outputWidth * 4 ≤ weights.size) →
    rows * width * 4 ≤ input.size → 0 < width →
    64 ∣ width → width < UInt64.size →
    heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size) →
    heap.Protects inputPtr.toNat (inputPtr.toNat + input.size) →
    4 * (rows * (width / 64)) ≤ 2^32 → 4 * (rows * outputWidth) ≤ 2^32 →
    (takeFirstFitFrom 0 (QuantizeRows.scaleNeed (rows * (width / 64))) heap.nodes = none →
      heap.top.toNat + 48 + (QuantizeRows.scaleNeed (rows * (width / 64))).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (QuantizeRows.scaleNeed (rows * (width / 64))) ≤ initial.memoryCap module_ 0) →
    (let next := heap.allocate (QuantizeRows.scaleNeed (rows * (width / 64)));
      takeFirstFitFrom 0 (QuantizeRows.byteNeed 64 (rows * (width / 64))) next.nodes = none →
        next.top.toNat + 48 + (QuantizeRows.byteNeed 64 (rows * (width / 64))).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (QuantizeRows.byteNeed 64 (rows * (width / 64))) ≤ initial.memoryCap module_ 0) →
    (let next := QuantizeRows.outputHeap heap 64 (rows * (width / 64));
      takeFirstFitFrom 0 (need outputWidth rows) next.nodes = none →
        next.top.toNat + 48 + (need outputWidth rows).toNat < 4294967296 ∧
        FixedArrayBump.requiredPages next.top (need outputWidth rows) ≤ initial.memoryCap module_ 0) →
    initial.mem.pages ≤ 65536 →
    TerminatesWith env module_ 8 initial
      (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias).reverse
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * (rows * outputWidth))), .i64 (outputNode heap width outputWidth rows).root] ∧
        Output heap initial final weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias)

theorem linearGroupedRows_exact_for : ExactSpecFor «module» := linearGroupedRows_exact

#print axioms linearGroupedRows_exact_for

end Project.Gpt2QuantizedGroupedRows.Spec
