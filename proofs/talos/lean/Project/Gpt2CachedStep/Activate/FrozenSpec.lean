import Project.Gpt2CachedStep.Activate.FrozenBody

namespace Project.Gpt2CachedStep.Frozen.Activate.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution

theorem activate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (inputOwner inputPtr : UInt64) (input : ByteArray)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : takeFirstFitFrom 0 (need input) heap.nodes = none →
      heap.top.toNat + 48 + (need input).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need input) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.activate input
    let node := allocatedNode heap.top (need input) heap.nodes
    TerminatesWith env «module» 32 initial
      [.i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate (need input)).At final ∧
        (heap.allocate (need input)).OwnsPacked final node output ∧
        heap.Frame initial (heap.allocate (need input)) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func32Def) rfl ?_
  change wp «module» (func32 ++ []) _ initial
    { params := parameters inputOwner inputPtr input, locals := List.replicate 20 (.i64 0) } env
  apply body_spec env initial heap inputOwner inputPtr input _ hHeap hInput hInputProtected
    hBump hPages rfl (by simp) rfl (I64Values.replicate _ _)
  intro final result hValues hOutput
  simp only [wp_nil]
  have hPost := And.intro hOutput.heapAt
    (And.intro hOutput.owned (And.intro hOutput.frame (And.intro hOutput.pages (hOutput.memoryCap «module» 0))))
  have hRoot : allocatedRoot heap.top (need input) heap.nodes =
      (allocatedNode heap.top (need input) heap.nodes).root := rfl
  simpa [func32Def, Function.numParams, hValues, hRoot, -UInt64.ofNat_mul] using hPost

#print axioms activate_exact

end Project.Gpt2CachedStep.Frozen.Activate.Spec
