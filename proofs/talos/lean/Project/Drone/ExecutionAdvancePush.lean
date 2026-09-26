import Project.Drone.ExecutionAdvanceFrame
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

theorem advance_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer : UInt64)
    (aux : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hAux : aux.length = 38)
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
        { advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
            resultOwner resultPointer aux
            (pushedScratch s input.size (allocatedRoot heap.top (pushNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (pushNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (WordArrayPush.program 52 ++ rest) Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer aux s) env := by
  rw [advanceFrame_as_push]
  let params : List Value := [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat target), .i64 r0, .i64 r1,
    .i64 (if last then 1 else 0), .i64 previousOwner, .i64 previousPointer, .i64 rowOwner, .i64 rowPointer]
  let saved := [.i64 tracker, .i64 0, .i64 resultOwner, .i64 resultPointer, .i64 0] ++ aux
  have hStart : params.length + saved.length = 52 := by simp [params, saved, hAux]
  rw [← hStart]
  apply word_push_budget_spec env store heap params saved [] s source input remaining pageLimit
    hSource hInput hHeap hBudget Q rest
  intro final previous current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  simpa only [advanceFrame_as_push, params, saved] using
    hNext final previous current capacity next hFinalHeap hFinalBudget hOutput
      ⟨fun saved words h => (hBorrow saved words h).1, hOwned⟩
      (fun saved words h => (hBorrow saved words h).2)

def advanceRepushProgram (second : Bool) : Wasm.Program :=
  if second then [.localSet 38, .localGet 38, .localSet 52, .localGet 29, .localSet 58]
  else [.localSet 37, .localGet 37, .localSet 52, .localGet 28, .localSet 58]

theorem advance_repush_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel target : Nat) (r0 r1 : UInt64) (last second : Bool)
    (previousOwner previousPointer rowOwner rowPointer tracker resultOwner resultPointer root value : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 38)
    (hValue : aux[if second then 15 else 14]? = some (.i64 value))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
        resultOwner resultPointer (aux.set (if second then 24 else 23) (.i64 root))
        { s with source := root, value := value }) env) :
    wp Project.Drone.«module» (advanceRepushProgram second ++ rest) Q store
      { advanceFrame fuel target r0 r1 last previousOwner previousPointer rowOwner rowPointer tracker
          resultOwner resultPointer aux s with values := [.i64 root] } env := by
  cases second <;>
    simp only [advanceRepushProgram, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at * <;>
    wp_advance_frame [hAux, hValue] <;>
    simpa only [advanceFrame, Scratch.words, List.cons_append, List.nil_append] using hNext

#print axioms advance_push_spec
#print axioms advance_repush_spec
end Project.Drone.Execution
