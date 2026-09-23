import Project.Gpt2QuantizedCached.CachedHidden.ActiveStep
import Project.Gpt2QuantizedCached.CachedHidden.Traversal

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure TraversalState (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position index : Nat)
    (current : Store Unit) (frame : Locals) : Prop where
  state : LayerFrame params embeddingNode.root
    (statusRoot (layerPrefix weights cache token position index).2.2
      (traversal heap embeddingNode weights cache token position index).hidden)
    (traversal heap embeddingNode weights cache token position index).updates.root
    (layerPrefix weights cache token position index).1.size
    (layerPrefix weights cache token position index).2.1.size
    (layerPrefix weights cache token position index).2.2 index frame
  heapAt : (traversal heap embeddingNode weights cache token position index).heap.At current
  hidden : (traversal heap embeddingNode weights cache token position index).heap.StatusPacked current
    (layerPrefix weights cache token position index).2.2
    (traversal heap embeddingNode weights cache token position index).hidden
    (layerPrefix weights cache token position index).1
  updates : ByteArrayAt current.mem (traversal heap embeddingNode weights cache token position index).updates.root.toNat
    (layerPrefix weights cache token position index).2.1
  updatesProtected : (traversal heap embeddingNode weights cache token position index).heap.Protects
    (traversal heap embeddingNode weights cache token position index).updates.root.toNat
    ((traversal heap embeddingNode weights cache token position index).updates.root.toNat +
      (layerPrefix weights cache token position index).2.1.size)
  updatesOwned : index ≠ 0 → (traversal heap embeddingNode weights cache token position index).heap.OwnsPacked current
    (traversal heap embeddingNode weights cache token position index).updates
    (layerPrefix weights cache token position index).2.1
  preserved : heap.Frame initial (traversal heap embeddingNode weights cache token position index).heap current
  hiddenFresh : index ≠ 0 → (layerPrefix weights cache token position index).2.2 = 0 →
    heap.FreshNode (traversal heap embeddingNode weights cache token position index).hidden
  updatesFresh : index ≠ 0 → heap.FreshNode (traversal heap embeddingNode weights cache token position index).updates
  separated : index ≠ 0 → (layerPrefix weights cache token position index).2.2 = 0 →
    regionsDisjoint (traversal heap embeddingNode weights cache token position index).hidden.region
      (traversal heap embeddingNode weights cache token position index).updates.region
  pages : current.mem.pages ≤ 65536
  capacity : current.memoryCap «module» 0 = initial.memoryCap «module» 0

theorem LayerFrame.counter_limit {params : List Value} {embedding input updates : UInt64}
    {inputSize updatesSize index : Nat} {status : UInt64} {frame : Locals}
    (h : LayerFrame params embedding input updates inputSize updatesSize status index frame)
    (hParams : params.length = 8) :
    frame.get 127 = some (.i64 (UInt64.ofNat index)) ∧ frame.get 128 = some (.i64 12) := by
  simp only [Locals.get, h.paramsEq, hParams, h.length, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceSub, ite_false, ite_true, h.counter, h.limit, and_self]

theorem traversalState_initial (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hEmbedding : heap.OwnsPacked initial embeddingNode (embedding weights token position))
    (hState : LayerFrame params embeddingNode.root embeddingNode.root 0 3072 0 0 0 frame)
    (hPages : initial.mem.pages ≤ 65536) :
    TraversalState initial heap embeddingNode params weights cache token position 0 initial frame := by
  refine ⟨?_, hHeap, ?_, ?_, ?_, ?_, Heap.Frame.refl .., ?_, ?_, ?_, hPages, rfl⟩
  · simpa only [traversal, layerPrefix_zero, statusRoot, ite_true, embedding_size, ByteArray.size_empty] using hState
  · exact ⟨fun _ => hEmbedding, fun h => False.elim (h rfl)⟩
  · simp [traversal, layerPrefix_zero, ByteArrayAt]
  · exact ⟨Nat.zero_le _, fun _ _ => Or.inl (Nat.zero_le _)⟩
  all_goals intro h; exact False.elim (h rfl)

#print axioms traversalState_initial
end Project.Gpt2QuantizedCached.CachedHidden
