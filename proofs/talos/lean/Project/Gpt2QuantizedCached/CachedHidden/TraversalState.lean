import Project.Gpt2QuantizedCached.CachedHidden.ActiveStep
import Project.Gpt2QuantizedCached.CachedHidden.Traversal

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure TraversalStateAt (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (source : LayerState) (machine : Traversal) (index : Nat)
    (current : Store Unit) (frame : Locals) : Prop where
  state : LayerFrame params embeddingNode.root
    (statusRoot source.2.2
      machine.hidden)
    machine.updates.root
    source.1.size
    source.2.1.size
    source.2.2 index frame
  heapAt : machine.heap.At current
  hidden : machine.heap.StatusPacked current
    source.2.2
    machine.hidden
    source.1
  updates : ByteArrayAt current.mem machine.updates.root.toNat
    source.2.1
  updatesProtected : machine.heap.Protects
    machine.updates.root.toNat
    (machine.updates.root.toNat +
      source.2.1.size)
  updatesOwned : index ≠ 0 → machine.heap.OwnsPacked current
    machine.updates
    source.2.1
  preserved : heap.Frame initial machine.heap current
  hiddenFresh : index ≠ 0 → source.2.2 = 0 →
    heap.FreshNode machine.hidden
  updatesFresh : index ≠ 0 → heap.FreshNode machine.updates
  separated : index ≠ 0 → source.2.2 = 0 →
    regionsDisjoint machine.hidden.region
      machine.updates.region
  pages : current.mem.pages ≤ 65536
  capacity : current.memoryCap «module» 0 = initial.memoryCap «module» 0

abbrev TraversalState (initial : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position index : Nat)
    (current : Store Unit) (frame : Locals) : Prop :=
  TraversalStateAt initial heap embeddingNode params (layerPrefix weights cache token position index)
    (traversal heap embeddingNode weights cache token position index) index current frame

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
