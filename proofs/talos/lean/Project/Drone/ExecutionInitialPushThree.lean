import Project.Drone.ExecutionInitialPushTwo
import Project.Drone.ExecutionAdvancePushThree

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
theorem initial_three_push_shape : (initialLoopBody.drop 25).take 211 =
    WordArrayPush.program 30 ++ initialRepushProgram false ++ WordArrayPush.program 30 ++
      initialRepushProgram true ++ WordArrayPush.program 30 := rfl

set_option maxRecDepth 32768 in
theorem initial_three_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (seed row : UInt64) (state : Nat) (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat) (hAux : aux.length = 21)
    (hValue : aux[4]? = some (.i64 s.value))
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store) (hBudget : Budget store heap (rowPushCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 21 → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node (((input.push s.value).push s.value).push 0) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        { initialFrame seed row state tracked nextAux nextScratch out0 out1 with values := [.i64 node.root] } env) :
    wp Project.Drone.«module» ((initialLoopBody.drop 25).take 211 ++ rest) Q store
      (initialFrame seed row state tracked aux s out0 out1) env := by
  rw [initial_three_push_shape]
  simp only [List.append_assoc]
  apply initial_push_spec env store heap seed row state tracked aux s out0 out1 source input
    (pushCost (input.size + 1) + (pushCost (input.size + 2) + remaining)) pageLimit
    hAux hSource hInput hHeap (by simpa only [rowPushCost, Nat.add_assoc] using hBudget)
  intro first p1 c1 cap1 n1 hHeap1 hBudget1 hOutput1 hKeep1 _
  let heap1 := heap.allocate (pushNeed input.size)
  let node1 := allocatedNode heap.top (pushNeed input.size) heap.nodes
  let scratch1 := pushedScratch s input.size node1.root p1 c1 cap1 n1
  apply initial_repush_spec (second := false) (value := s.value) (hAux := hAux) (hValue := hValue)
  apply initial_two_push_spec env first heap1 seed row state tracked (aux.set 6 (.i64 node1.root))
    { scratch1 with source := node1.root, value := s.value } out0 out1 node1 (input.push s.value)
    remaining pageLimit (by simp [hAux]) (by simpa using hValue) rfl (borrow_owned hOutput1) hHeap1
    (by simpa only [Array.size_push, Nat.add_assoc] using hBudget1)
  intro final nextHeap node nextAux nextScratch hLength _ hFinalHeap hFinalBudget hOutput hKeep hFresh
  refine hNext final nextHeap node nextAux nextScratch hLength hFinalHeap hFinalBudget hOutput
    (hKeep1.trans hKeep) ?_
  intro saved words hSaved
  exact hFresh saved words (hKeep1.borrowed saved words hSaved)

#print axioms initial_three_push_spec
end Project.Drone.Execution
