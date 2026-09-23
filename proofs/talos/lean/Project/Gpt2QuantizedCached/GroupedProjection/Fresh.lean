import Project.Gpt2QuantizedCached.GroupedProjection.Budget
import Project.ProofKit.PackedFresh

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Project.EulerRiemann.Execution Project.Gpt2QuantizedLinearRows

theorem outputNode_fresh {heap : Heap} {width outputWidth rows pageCapacity : Nat}
    (h : Resources heap width outputWidth rows pageCapacity) :
    heap.FreshNode (outputNode heap width outputWidth rows) := by
  intro lower upper hProtected
  have hScales := hProtected.allocated (QuantizeRows.scaleNeed (rows * (width / 64)))
    (fun fit => (h.scales fit).1.le)
  have hValues := hScales.allocated (QuantizeRows.byteNeed 64 (rows * (width / 64)))
    (fun fit => (h.values fit).1.le)
  exact hValues.allocated_disjoint (need outputWidth rows) (fun fit => (h.output fit).1.le)

#print axioms outputNode_fresh
end Project.Gpt2QuantizedCached.GroupedProjection.Projection
