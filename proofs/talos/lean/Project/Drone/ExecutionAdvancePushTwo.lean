import Project.Drone.ExecutionAdvancePush

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem advance_two_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer parent : UInt64)
    (aux : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hAux : aux.length = 38)
    (hParent : aux[15]? = some (.i64 parent))
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store)
    (hBudget : Budget store heap (pushCost input.size + (pushCost (input.size + 1) + remaining)) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 38 → (∀ i, i ≠ 24 → nextAux[i]? = aux[i]?) →
      nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node ((input.push s.value).push parent) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        { advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
            resultOwner resultPointer nextAux nextScratch with values := [.i64 node.root] } env) :
    wp Project.Drone.«module» (WordArrayPush.program 52 ++ advanceRepushProgram true ++
      WordArrayPush.program 52 ++ rest) Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer aux s) env := by
  apply advance_push_spec env store heap fuel target r0 r1 last previousOwner previousPointer
    rowOwner rowPointer tracker resultOwner resultPointer aux s source input
    (pushCost (input.size + 1) + remaining) pageLimit hAux hSource hInput hHeap hBudget
  intro first p1 c1 cap1 n1 hHeap1 hBudget1 hOutput1 hKeep1 _
  let heap1 := heap.allocate (pushNeed input.size)
  let node1 := allocatedNode heap.top (pushNeed input.size) heap.nodes
  let scratch1 := pushedScratch s input.size node1.root p1 c1 cap1 n1
  apply advance_repush_spec (second := true) (value := parent) (hAux := hAux) (hValue := hParent)
  apply advance_push_spec env first heap1 fuel target r0 r1 last previousOwner previousPointer
    rowOwner rowPointer tracker resultOwner resultPointer (aux.set 24 (.i64 node1.root))
    { scratch1 with source := node1.root, value := parent } node1 (input.push s.value)
    remaining pageLimit (by simp [hAux]) rfl (borrow_owned hOutput1) hHeap1
    (by simpa only [Array.size_push] using hBudget1)
  intro final p2 c2 cap2 n2 hHeap2 hBudget2 hOutput2 hKeep2 hFresh2
  refine hNext final _ _ _ _ (by simp [hAux]) ?_ hHeap2 hBudget2 hOutput2 (hKeep1.trans hKeep2) ?_
  · intro i hi
    simp [List.getElem?_set, Ne.symm hi]
  · intro saved words hSaved
    exact hFresh2 saved words (hKeep1.borrowed saved words hSaved)

#print axioms advance_two_push_spec
end Project.Drone.Execution
