import Verified.HeapStep
import Verified.TreeHeader
import Verified.RuntimeFacts
import LeanExe.Pipeline.ReleaseTree

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

theorem wp_releaseHeader {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals} {ptr : UInt64}
    {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hOwned : TreeHeader.Owned shape r heap store ptr)
    (hNext : ∀ heap' store', Step heap store (fun r => regionsDisjoint r (block store ptr))
      heap' store' [] → heap'.top = heap.top →
      wp m rest Q store' { s with values := vs } host) :
    wp m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  obtain ⟨words, _, hNode⟩ := hOwned
  have hBlocks : Node.blocks store ptr (.record (words.map Slot.word)) = [block store ptr] := by
    simp only [Node.blocks, wordSlots_blocks]
  refine wp_releaseNode hm hAt hNode (by rw [hBlocks]; simp) ?_
  intro heap' store' hStep hTop
  exact hNext heap' store'
    (hStep.mono (fun r hr _ hb => by rw [hBlocks, List.mem_singleton] at hb; subst hb; exact hr)
      (fun _ h => h)) hTop

#print axioms wp_releaseNode
#print axioms wp_releaseHeader

end Verified
