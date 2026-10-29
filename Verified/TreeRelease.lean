import Verified.HeapStep
import Verified.TreeHeader
import Verified.RuntimeFacts
import LeanExe.ProofKit.ReleaseTree

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_releaseNode {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {ptr : UInt64} {value : Node} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hOwned : NodeOwned heap store ptr value)
    (hApart : (value.blocks store ptr).Pairwise regionsDisjoint)
    (hNext : ∀ heap' store',
      Step heap store (fun r => ∀ b ∈ value.blocks store ptr, regionsDisjoint r b)
        heap' store' [] → heap'.top = heap.top →
      wp m rest Q store' { s with values := vs } host) :
    wp m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  have hRun := (release_tree_run_top hm.imports hm.release host heap store ptr value hAt
    hOwned hApart).runs (aborts := false)
    |>.append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release) (by rfl) vs
  refine wp_call_runs hRun trivial ?_
  rintro store' _ ⟨_, rfl, rfl, heap', hAt', hTop, hCaps, hKept⟩
  have hStep : Step heap store (fun r => ∀ b ∈ value.blocks store ptr, regionsDisjoint r b)
      heap' store' [] :=
    ⟨hAt', hCaps, fun r hr hPos hKeep => ⟨(hKept r hr hPos hKeep).1,
      (hKept r hr hPos hKeep).2, nofun⟩⟩
  simpa using hNext heap' store' hStep hTop

#print axioms wp_releaseNode
end Verified
