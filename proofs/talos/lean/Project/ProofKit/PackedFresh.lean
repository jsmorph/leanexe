import Project.ProofKit.OwnedPacked

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

theorem Heap.Protects.allocated {heap : Heap} {lower upper : Nat}
    (h : heap.Protects lower upper) (need : UInt64)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).Protects lower upper := by
  refine ⟨?_, fun node hNode => h.separated node (allocatedNodes_mem need heap.nodes node hNode)⟩
  have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
  change upper ≤ (allocatedTop heap.top need heap.nodes).toNat
  rw [hTop]
  split <;> have := h.below <;> omega

def Heap.FreshNode (heap : Heap) (node : FreeNode) : Prop :=
  ∀ lower upper, heap.Protects lower upper →
    upper ≤ node.root.toNat - 48 ∨ node.root.toNat + node.capacity.toNat ≤ lower

theorem Heap.freshNode_allocated (heap : Heap) (need : UInt64)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    heap.FreshNode (allocatedNode heap.top need heap.nodes) := by
  intro lower upper h
  exact h.allocated_disjoint need hBump

theorem Heap.FreshNode.owns_disjoint {heap : Heap} {store : Store Unit} {node other : FreeNode}
    {bytes : ByteArray} (h : heap.FreshNode node) (hRoot : 48 ≤ node.root.toNat)
    (hOwner : heap.OwnsPacked store other bytes) :
    regionsDisjoint node.region other.region := by
  have hSep := h _ _ hOwner.protects
  have hOtherRoot := hOwner.buffer.rootBound
  simp only [regionsDisjoint, FreeNode.region]
  omega

theorem Heap.Frame.freshNode {before after : Heap} {initial final : Store Unit}
    (hFrame : before.Frame initial after final) {node : FreeNode} (h : after.FreshNode node) :
    before.FreshNode node := fun lower upper hProtected => h lower upper (hFrame.protects _ _ hProtected)

#print axioms Heap.Protects.allocated
#print axioms Heap.FreshNode.owns_disjoint

end Project.EulerRiemann.Execution
