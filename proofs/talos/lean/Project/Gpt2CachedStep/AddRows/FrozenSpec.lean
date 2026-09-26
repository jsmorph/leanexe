import Project.Gpt2CachedStep.AddRows.FrozenBody

namespace Project.Gpt2CachedStep.Frozen.AddRows.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution

theorem addRows_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (leftOwner rightOwner leftPtr rightPtr : UInt64) (left right : ByteArray)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hRightSize : 4 * (left.size / 4) ≤ right.size)
    (hRightProtected : heap.Protects rightPtr.toNat (rightPtr.toNat + right.size))
    (hInputProtected : heap.Protects leftPtr.toNat (leftPtr.toNat + left.size))
    (hBump : takeFirstFitFrom 0 (need left) heap.nodes = none →
      heap.top.toNat + 48 + (need left).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need left) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.addRows left right
    let node := allocatedNode heap.top (need left) heap.nodes
    TerminatesWith env «module» 30 initial
      [.i64 (UInt64.ofNat right.size), .i64 rightPtr, .i64 rightOwner,
       .i64 (UInt64.ofNat left.size), .i64 leftPtr, .i64 leftOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size), .i64 node.root, .i64 node.root] ∧
        (heap.allocate (need left)).At final ∧
        (heap.allocate (need left)).OwnsPacked final node output ∧
        heap.Frame initial (heap.allocate (need left)) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_
  change wp «module» (func30 ++ []) _ initial
    { params := parameters leftOwner rightOwner leftPtr rightPtr left right, locals := List.replicate 22 (.i64 0) } env
  apply body_spec env initial heap leftOwner rightOwner leftPtr rightPtr left right _ hHeap hInput
    hRight hRightSize hRightProtected hInputProtected
    hBump hPages rfl (by simp) rfl (I64Values.replicate _ _)
  intro final result hValues hOutput
  simp only [wp_nil]
  have hPost := And.intro hOutput.heapAt
    (And.intro hOutput.owned (And.intro hOutput.frame (And.intro hOutput.pages (hOutput.memoryCap «module» 0))))
  have hRoot : allocatedRoot heap.top (need left) heap.nodes =
      (allocatedNode heap.top (need left) heap.nodes).root := rfl
  simpa [func30Def, Function.numParams, hValues, hRoot, -UInt64.ofNat_mul] using hPost

#print axioms addRows_exact

end Project.Gpt2CachedStep.Frozen.AddRows.Spec
