import Project.Gpt2CachedStep.Program
import Project.ProofKit.PackedInput
import Project.ProofKit.PackedAllocExport
import Project.ProofKit.HeapGrowth

namespace Project.Gpt2CachedStep.Initialize
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def freshHeap : Heap := ⟨4096, [], 0, 0, 0, 0⟩
def weightNeed : UInt64 := 497759232
def weightNode : FreeNode := allocatedNode freshHeap.top weightNeed freshHeap.nodes
def heap : Heap := freshHeap.allocate weightNeed
def allocatedStore : Store Unit := freshHeap.allocatePackedStore «module».initialStore weightNeed
def store (weights : ByteArray) : Store Unit := PackedInput.write allocatedStore weightNode.root.toNat weights

theorem freshHeap_at : freshHeap.At («module».initialStore (α := Unit)) := by
  refine ⟨rfl, .nil, ?_⟩
  simp [freshHeap]

theorem reset_initial (env : HostEnv Unit) :
    TerminatesWith env «module» 40 («module».initialStore (α := Unit)) []
      (fun final values => final = «module».initialStore (α := Unit) ∧ values = []) := by
  generalize hInitial : «module».initialStore (α := Unit) = initial
  have hGlobals : initial.globals.globals = [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] := by
    rw [← hInitial]
    rfl
  have hReset : { initial with globals := { globals :=
      [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] } } = initial := by
    rw [← hGlobals]
  refine TerminatesWith.of_wp_entry_for (f := func40Def) rfl ?_
  change wp «module» func40 _ initial (func40Def.toLocals []) env
  wp_run [func40, func40Def, hGlobals, List.set, hReset]
  simp

theorem allocate_exact (env : HostEnv Unit) :
    TerminatesWith env «module» 39 («module».initialStore (α := Unit)) [.i64 weightNeed]
      (fun final values => values = [.i64 weightNode.root] ∧ final = allocatedStore) := by
  exact PackedAllocExport.exact «module» env 39 «module».initialStore 4096 weightNeed 0 []
    (typeIdx := some 39) rfl rfl rfl rfl rfl .nil
    (fun _ => ⟨by decide, by decide⟩) (by decide) rfl

theorem input (weights : ByteArray) (hSize : weights.size = 497759232) :
    heap.At (store weights) ∧ heap.OwnsPacked (store weights) weightNode weights ∧
    (store weights).mem.pages ≤ 65536 ∧
    (store weights).memoryCap «module» 0 = 65536 ∧ heap.top.toNat ≤ 536870912 := by
  have hOutput := PackedInput.allocated freshHeap «module».initialStore weightNeed weights freshHeap_at
    (by change weights.size ≤ 497759232; omega) (fun _ => by decide) (by decide)
  exact ⟨hOutput.heapAt, hOutput.owned, hOutput.pages, hOutput.memoryCap «module» 0, by decide⟩

#print axioms allocate_exact
#print axioms reset_initial
#print axioms input

end Project.Gpt2CachedStep.Initialize
