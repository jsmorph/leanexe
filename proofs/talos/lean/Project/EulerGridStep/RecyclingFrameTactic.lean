import Project.EulerGridStep.GridLoopFrame

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

macro "recycling_loop_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [gridLoopFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, *, -UInt64.ofNat_div, -UInt64.ofNat_mul, -UInt64.ofNat_add, -getElem!_pos]
    | refine ⟨by omega, ?_⟩
    | (try rw [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_div, -UInt64.ofNat_mul, -UInt64.ofNat_add, -getElem!_pos])

end Project.EulerGridStep.Execution
