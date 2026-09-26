import Project.Drone.ExecutionEdgePrefix
import Project.ProofKit.ConstIf

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone


theorem edgeRest_body (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 z0 z1 u v : UInt64) (hRest : u + v = 0) :
    wp «module» (func9.drop 7)
      (fun c => match c with
        | .Fallthrough store frame => store = initial ∧
            frame.values.take 1 = [.i64 (840 * restSeconds (distance z0 z1))]
        | .Return store values => store = initial ∧
            values.take 1 = [.i64 (840 * restSeconds (distance z0 z1))]
        | _ => False)
      initial (edgeStartFrame r0 r1 z0 z1 u v) env := by
  simp only [func9, List.drop, edgeStartFrame]
  wp_fixed_frame [hRest]
  apply wp_constIf rfl
  wp_fixed_frame [hRest]
  apply wp_constIf rfl
  wp_fixed_frame [hRest]
  refine wp_iff_cons rfl ?_
  simp [hRest]
  try wp_fixed_frame [hRest]
  try wp_fixed_frame [hRest]
  refine wp_call_tw ((restSeconds_exact env initial (distance z0 z1)).append_args
    (f := func8Def) rfl rfl rfl [.i64 840]) ?_
  rintro final values ⟨out, rfl, hFinal, rfl⟩
  subst final
  wp_fixed_frame
  trivial

#print axioms edgeRest_body
end Project.Drone.Execution
