import Project.Drone.ExecutionAdvancePushTwo

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def rowPushCost (size : Nat) : Nat := pushCost size + pushCost (size + 1) + pushCost (size + 2)

set_option maxRecDepth 32768 in
theorem advance_three_push_shape : (advanceLoopBody.drop 49).take 211 =
    WordArrayPush.program 52 ++ advanceRepushProgram false ++ WordArrayPush.program 52 ++
      advanceRepushProgram true ++ WordArrayPush.program 52 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem advance_three_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer excess parent : UInt64)
    (aux : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hAux : aux.length = 38)
    (hExcess : aux[14]? = some (.i64 excess)) (hParent : aux[15]? = some (.i64 parent))
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store) (hBudget : Budget store heap (rowPushCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 38 → (∀ i, i ≠ 23 → i ≠ 24 → nextAux[i]? = aux[i]?) →
      nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node (((input.push s.value).push excess).push parent) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        { advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
            resultOwner resultPointer nextAux nextScratch with values := [.i64 node.root] } env) :
    wp Project.Drone.«module» ((advanceLoopBody.drop 49).take 211 ++ rest) Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer aux s) env := by
  rw [advance_three_push_shape]
  simp only [List.append_assoc]
  apply advance_push_spec env store heap fuel target r0 r1 last previousOwner previousPointer
    rowOwner rowPointer tracker resultOwner resultPointer aux s source input
    (pushCost (input.size + 1) + (pushCost (input.size + 2) + remaining)) pageLimit
    hAux hSource hInput hHeap (by simpa only [rowPushCost, Nat.add_assoc] using hBudget)
  intro first p1 c1 cap1 n1 hHeap1 hBudget1 hOutput1 hKeep1 _
  let heap1 := heap.allocate (pushNeed input.size)
  let node1 := allocatedNode heap.top (pushNeed input.size) heap.nodes
  let scratch1 := pushedScratch s input.size node1.root p1 c1 cap1 n1
  apply advance_repush_spec (second := false) (value := excess) (hAux := hAux) (hValue := hExcess)
  apply advance_two_push_spec env first heap1 fuel target r0 r1 last previousOwner previousPointer
    rowOwner rowPointer tracker resultOwner resultPointer parent (aux.set 23 (.i64 node1.root))
    { scratch1 with source := node1.root, value := excess } node1 (input.push s.value)
    remaining pageLimit (by simp [hAux]) (by simpa using hParent) rfl
    (borrow_owned hOutput1) hHeap1
    (by simpa only [Array.size_push, Nat.add_assoc] using hBudget1)
  intro final nextHeap node nextAux nextScratch hLength hStable hFinalHeap hFinalBudget hOutput hKeep hFresh
  refine hNext final nextHeap node nextAux nextScratch hLength ?_ hFinalHeap hFinalBudget hOutput
    (hKeep1.trans hKeep) ?_
  · intro i hi23 hi24
    rw [hStable i hi24]
    simp [List.getElem?_set, Ne.symm hi23]
  · intro saved words hSaved
    exact hFresh saved words (hKeep1.borrowed saved words hSaved)

#print axioms advance_three_push_spec
end Project.Drone.Execution
