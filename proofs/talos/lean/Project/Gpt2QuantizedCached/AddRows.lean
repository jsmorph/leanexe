import Project.Gpt2QuantizedCached.FP32Region
import Project.Gpt2CachedStep.AddRows.Spec

namespace Project.Gpt2QuantizedCached.AddRows
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.AddRows

theorem addRows_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (leftOwner rightOwner leftPtr rightPtr : UInt64) (left right : ByteArray)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hRightSize : 4 * (left.size / 4) ≤ right.size)
    (hRightProtected : heap.Protects rightPtr.toNat (rightPtr.toNat + right.size))
    (hInputProtected : heap.Protects leftPtr.toNat (leftPtr.toNat + left.size))
    (hBump : takeFirstFitFrom 0 (need left) heap.nodes = none →
      heap.top.toNat + 48 + (need left).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need left) ≤ initial.memoryCap Project.Gpt2CachedStep.«module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.addRows left right
    let node := allocatedNode heap.top (need left) heap.nodes
    TerminatesWith env Project.Gpt2QuantizedCached.«module» 51 initial
      [.i64 (UInt64.ofNat right.size), .i64 rightPtr, .i64 rightOwner,
       .i64 (UInt64.ofNat left.size), .i64 leftPtr, .i64 leftOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate (need left)).At final ∧
        (heap.allocate (need left)).OwnsPacked final node output ∧
        heap.Frame initial (heap.allocate (need left)) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
  exact Project.FunctionRegion.terminatesWith FP32Region.shift 30
    (by simp [FP32Region.domain]) (Project.Gpt2CachedStep.AddRows.Spec.addRows_exact
      env initial heap leftOwner rightOwner leftPtr rightPtr left right hHeap hInput hRight hRightSize hRightProtected hInputProtected hBump hPages)

#print axioms addRows_exact
end Project.Gpt2QuantizedCached.AddRows
