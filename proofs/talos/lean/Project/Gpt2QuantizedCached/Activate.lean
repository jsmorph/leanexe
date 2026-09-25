import Project.Gpt2QuantizedCached.FP32Region
import Project.Gpt2CachedStep.Activate.Spec

namespace Project.Gpt2QuantizedCached.Activate
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.Activate

theorem activate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (inputOwner inputPtr : UInt64) (input : ByteArray)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : takeFirstFitFrom 0 (need input) heap.nodes = none →
      heap.top.toNat + 48 + (need input).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need input) ≤ initial.memoryCap Project.Gpt2CachedStep.«module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.activate input
    let node := allocatedNode heap.top (need input) heap.nodes
    TerminatesWith env Project.Gpt2QuantizedCached.«module» 53 initial
      [.i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate (need input)).At final ∧
        (heap.allocate (need input)).OwnsPacked final node output ∧
        heap.Frame initial (heap.allocate (need input)) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
  exact Project.FunctionRegion.terminatesWith FP32Region.shift 32
    (by simp [FP32Region.domain]) (Project.Gpt2CachedStep.Activate.Spec.activate_exact
      env initial heap inputOwner inputPtr input hHeap hInput hInputProtected hBump hPages)

#print axioms activate_exact
end Project.Gpt2QuantizedCached.Activate
