import Project.Drone.ExecutionInitialPush

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
theorem initial_two_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (seed row : UInt64) (state : Nat) (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat) (hAux : aux.length = 19)
    (hValue : aux[4]? = some (.i64 s.value))
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store)
    (hBudget : Budget store heap (pushCost input.size + (pushCost (input.size + 1) + remaining)) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 19 → (∀ i, i ≠ 7 → nextAux[i]? = aux[i]?) →
      nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node ((input.push s.value).push 0) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        { initialFrame seed row state tracked nextAux nextScratch out0 out1 with values := [.i64 node.root] } env) :
    wp Project.Drone.«module» (WordArrayPush.program 28 ++ initialRepushProgram true ++
      WordArrayPush.program 28 ++ rest) Q store (initialFrame seed row state tracked aux s out0 out1) env := by
  apply initial_push_spec env store heap seed row state tracked aux s out0 out1 source input
    (pushCost (input.size + 1) + remaining) pageLimit hAux hSource hInput hHeap hBudget
  intro first p1 c1 cap1 n1 hHeap1 hBudget1 hOutput1 hKeep1 _
  let heap1 := heap.allocate (pushNeed input.size)
  let node1 := allocatedNode heap.top (pushNeed input.size) heap.nodes
  let scratch1 := pushedScratch s input.size node1.root p1 c1 cap1 n1
  apply initial_repush_spec (second := true) (value := s.value) (hAux := hAux) (hValue := hValue)
  apply initial_push_spec env first heap1 seed row state tracked (aux.set 7 (.i64 node1.root))
    { scratch1 with source := node1.root, value := 0 } out0 out1 node1 (input.push s.value)
    remaining pageLimit (by simp [hAux]) rfl (borrow_owned hOutput1) hHeap1
    (by simpa only [Array.size_push] using hBudget1)
  intro final p2 c2 cap2 n2 hHeap2 hBudget2 hOutput2 hKeep2 hFresh2
  refine hNext final _ _ _ _ (by simp [hAux]) ?_ hHeap2 hBudget2 hOutput2 (hKeep1.trans hKeep2) ?_
  · intro i hi
    simp [Ne.symm hi]
  · intro saved words hSaved
    exact hFresh2 saved words (hKeep1.borrowed saved words hSaved)

#print axioms initial_two_push_spec
end Project.Drone.Execution
