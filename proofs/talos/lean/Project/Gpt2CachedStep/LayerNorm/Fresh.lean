import Project.Gpt2CachedStep.LayerNorm.Resources
import Project.ProofKit.PackedFresh

namespace Project.Gpt2CachedStep.LayerNorm
open Project.EulerRiemann.Execution

theorem outputNode_fresh {heap : Heap} {rows pageCapacity : Nat}
    (h : Resources heap rows pageCapacity) : heap.FreshNode (outputNode heap rows) := by
  intro lower upper hProtected
  have hMeans := hProtected.allocated (temporaryNeed rows) (fun fit => (h.means fit).1.le)
  have hInverses := hMeans.allocated (temporaryNeed rows) (fun fit => (h.inverses fit).1.le)
  exact hInverses.allocated_disjoint (outputNeed rows) (fun fit => (h.output fit).1.le)

#print axioms outputNode_fresh

end Project.Gpt2CachedStep.LayerNorm
