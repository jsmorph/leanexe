import Project.Gpt2QuantizedCached.Program
import Project.ProofKit.PackedInput
import Project.ProofKit.PackedAllocExport
import Project.ProofKit.HeapGrowth

namespace Project.Gpt2QuantizedCached.Initialize
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def freshHeap : Heap := ⟨4096, [], 0, 0, 0, 0⟩
def weightNeed : UInt64 := 127695976
def weightNode : FreeNode := allocatedNode freshHeap.top weightNeed freshHeap.nodes
def heap : Heap := freshHeap.allocate weightNeed
def allocatedStore : Store Unit := freshHeap.allocatePackedStore «module».initialStore weightNeed
def store (weights : ByteArray) : Store Unit := PackedInput.write allocatedStore weightNode.root.toNat weights

theorem export_indices : «module».findExport "validateModel" = some 60 ∧
    «module».findExport "cachedStep" = some 61 ∧
    «module».findExport "alloc" = some 62 ∧ «module».findExport "reset" = some 63 ∧
    «module».findExport "release" = some 65 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem freshHeap_at : freshHeap.At («module».initialStore (α := Unit)) := by
  refine ⟨rfl, .nil, ?_⟩
  simp [freshHeap]

theorem reset_initial (env : HostEnv Unit) :
    TerminatesWith env «module» 63 («module».initialStore (α := Unit)) []
      (fun final values => final = «module».initialStore (α := Unit) ∧ values = []) := by
  generalize hInitial : «module».initialStore (α := Unit) = initial
  have hGlobals : initial.globals.globals = [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] := by
    rw [← hInitial]
    rfl
  have hReset : { initial with globals := { globals :=
      [.i64 4096, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] } } = initial := by
    rw [← hGlobals]
  refine TerminatesWith.of_wp_entry_for (f := func63Def) rfl ?_
  change wp «module» func63 _ initial (func63Def.toLocals []) env
  wp_run [func63, func63Def, hGlobals, List.set, hReset]
  simp

theorem allocate_exact (env : HostEnv Unit) :
    TerminatesWith env «module» 62 («module».initialStore (α := Unit)) [.i64 weightNeed]
      (fun final values => values = [.i64 weightNode.root] ∧ final = allocatedStore) := by
  exact PackedAllocExport.exact «module» env 62 «module».initialStore 4096 weightNeed 0 []
    (typeIdx := some 62) rfl rfl rfl rfl rfl .nil
    (fun _ => ⟨by decide, by decide⟩) (by decide) rfl

theorem input (weights : ByteArray) (hSize : weights.size = 127695972) :
    heap.At (store weights) ∧ heap.OwnsPacked (store weights) weightNode weights ∧
    (store weights).mem.pages ≤ 65536 ∧
    (store weights).memoryCap «module» 0 = 65536 ∧ heap.top.toNat ≤ 134217728 := by
  have hOutput := PackedInput.allocated freshHeap «module».initialStore weightNeed weights freshHeap_at
    (by change weights.size ≤ 127695976; omega) (fun _ => by decide) (by decide)
  exact ⟨hOutput.heapAt, hOutput.owned, hOutput.pages, hOutput.memoryCap «module» 0, by decide⟩

#print axioms allocate_exact
#print axioms reset_initial
#print axioms input

end Project.Gpt2QuantizedCached.Initialize
