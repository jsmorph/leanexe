import Project.ClobDepth.EmptyHeap
import Project.ClobDepth.FoldHeap

namespace Project.ClobDepth.FoldHeap
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation Project.ClobDepth.HeapProof
  Project.ClobDepth.Func6Fold Project.EulerRiemann.Execution

theorem initial_state (heap : Heap) (st : Store Unit) (os : List OrderL) (side : UInt64)
    (hHeap : heap.At st) (hFit32 : heap.top.toNat + 112 < 4294967296)
    (hFit : heap.top.toNat + 112 ≤ st.mem.pages * 65536) :
    let first := initialized st heap 8 0
    let heap1 := heap.allocate 8
    let second := initialized first heap1 8 0
    let node1 := allocatedNode heap.top 8 heap.nodes
    let node2 := allocatedNode heap1.top 8 heap1.nodes
    State heap st os side node1.root (heap1.allocate 8) second node2 node1.root 0 := by
  dsimp only
  have hFirst := EmptyHeap.empty_result st heap hHeap (by omega) (by omega)
  have hTop1 := allocate_top_le heap 8 (by change _ + 48 + 8 < _; omega)
  have hSecond := EmptyHeap.empty_result (initialized st heap 8 0) (heap.allocate 8)
    hFirst.heapAt (by change _ ≤ _ + 48 + 8 at hTop1; omega)
    (by rw [hFirst.pages]; change _ ≤ _ + 48 + 8 at hTop1; omega)
  have hTop2 := allocate_top_le (heap.allocate 8) 8 (by
    change _ + 48 + 8 < _
    change _ ≤ _ + 48 + 8 at hTop1
    omega)
  refine ⟨hSecond.heapAt, hSecond.pages.trans hFirst.pages, hFirst.frame.trans hSecond.frame,
    hSecond.owned, ?_, Or.inl rfl, ?_, rfl, ?_⟩
  · intro lo hi hProtected
    exact (hFirst.frame.protects lo hi hProtected).allocated_disjoint 8 (fun _ => by
      change _ + 48 + 8 ≤ _
      change _ ≤ _ + 48 + 8 at hTop1
      omega)
  · simp only [Heap.allocate, matchCount, List.take_zero, List.countP_nil, UInt64.add_assoc]
    rfl
  · change _ ≤ _ + 112 + 0 * _
    change _ ≤ _ + 48 + 8 at hTop1 hTop2
    omega

#print axioms initial_state
end Project.ClobDepth.FoldHeap
