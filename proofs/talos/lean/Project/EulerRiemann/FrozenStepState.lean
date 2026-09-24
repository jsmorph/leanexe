import Project.EulerRiemann.FrozenSweepOwned
import Project.EulerRiemann.FrozenReleaseOwned
import Project.EulerRiemann.FrozenExecutionAccepted

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime

def stepAllocation (heap : Heap) (need : UInt64) (accepted : Bool) : Heap × FreeNode :=
  let first := allocatedNode heap.top need heap.nodes
  let afterFirst := heap.allocate need
  if accepted then
    let second := allocatedNode afterFirst.top need afterFirst.nodes
    ((afterFirst.allocate need).release first, second)
  else (afterFirst, first)

macro "step_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func80Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        boolWord, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

end Project.EulerRiemann.Frozen.Execution
