import Project.Drone.ExecutionInitialFrame
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

theorem initial_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (seed row : UInt64) (state : Nat) (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat) (hAux : aux.length = 19)
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store) (hBudget : Budget store heap (pushCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      (heap.allocate (pushNeed input.size)).At final →
      Budget final (heap.allocate (pushNeed input.size)) remaining pageLimit →
      (heap.allocate (pushNeed input.size)).OwnsWords final
        (allocatedNode heap.top (pushNeed input.size) heap.nodes) (input.push s.value) →
      PreservesWords heap store (heap.allocate (pushNeed input.size)) final →
      SeparateWords heap store (allocatedNode heap.top (pushNeed input.size) heap.nodes) →
      wp Project.Drone.«module» rest Q final
        { initialFrame seed row state tracked aux
            (pushedScratch s input.size (allocatedRoot heap.top (pushNeed input.size) heap.nodes)
              previous current capacity next) out0 out1 with
          values := [.i64 (allocatedRoot heap.top (pushNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (WordArrayPush.program 28 ++ rest) Q store
      (initialFrame seed row state tracked aux s out0 out1) env := by
  rw [initialFrame_as_push]
  let saved : List Value := [.i64 0, .i64 seed, .i64 seed, .i64 45, .i64 row, .i64 row] ++
    (aux ++ [.i64 (UInt64.ofNat state), .i64 45, .i64 1])
  let tail : List Value := [.i64 0, .i64 out0, .i64 out1, .i64 seed, .i64 0]
  have hStart : ([] : List Value).length + saved.length = 28 := by simp [saved, hAux]
  rw [← hStart]
  apply word_push_budget_spec env store heap [] saved tail s source input remaining pageLimit
    hSource hInput hHeap hBudget Q rest
  intro final previous current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  simpa only [initialFrame_as_push, saved, tail] using
    hNext final previous current capacity next hFinalHeap hFinalBudget hOutput
      ⟨fun saved words h => (hBorrow saved words h).1, hOwned⟩
      (fun saved words h => (hBorrow saved words h).2)

def initialRepushProgram (second : Bool) : Wasm.Program :=
  if second then [.localSet 13, .localGet 13, .localSet 28, .constI64 0, .localSet 34]
  else [.localSet 12, .localGet 12, .localSet 28, .localGet 10, .localSet 34]

theorem initial_repush_spec (env : HostEnv Unit) (store : Store Unit)
    (seed row : UInt64) (state : Nat) (tracked second : Bool) (aux : List Value) (s : Scratch)
    (out0 out1 root value : UInt64) (hAux : aux.length = 19)
    (hValue : aux[4]? = some (.i64 value))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (initialFrame seed row state tracked (aux.set (if second then 7 else 6) (.i64 root))
        { s with source := root, value := if second then 0 else value } out0 out1) env) :
    wp Project.Drone.«module» (initialRepushProgram second ++ rest) Q store
      { initialFrame seed row state tracked aux s out0 out1 with values := [.i64 root] } env := by
  cases second <;>
    simp only [initialRepushProgram, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at * <;>
    wp_initial_frame [hAux, hValue] <;>
    simpa only [initialFrame, Scratch.words, List.cons_append, List.nil_append] using hNext

#print axioms initial_push_spec
#print axioms initial_repush_spec
end Project.Drone.Execution
