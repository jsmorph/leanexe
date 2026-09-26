import Project.Drone.ExecutionUnwindStep
import Project.Drone.ExecutionAppendInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def reverseCost (size : Nat) : Nat := 48 + 8 * (size + 1)

def unwindCost : Nat → Nat → Nat
  | 0, size => reverseCost size
  | count + 1, size => pushCost size + (pushCost (size + 1) + unwindCost count (size + 2))

def unwindInv (initialHeap : Heap) (initial : Store Unit) (terrainNode historyNode : FreeNode)
    (terrain history expected : Array UInt64) (count maxIndex totalSize remaining pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ (heap : Heap) (node : FreeNode) (row : Array UInt64) (fuel index state : Nat)
    (tracked : Bool) (out0 out1 : UInt64) (aux : List Value) (s : Scratch),
    frame = unwindFrame fuel index state terrainNode.root historyNode.root node.root tracked out0 out1 aux s ∧
    aux.length = 36 ∧ aux[33]? = some (.i64 0) ∧ aux[35]? = some (.i64 0) ∧ fuel ≤ count ∧ index ≤ maxIndex ∧ index < terrain.size ∧
    fuel ≤ index + 1 ∧ state < 45 ∧ (tracked = true ↔ fuel < count) ∧ heap.At store ∧
    Budget store heap (unwindCost fuel row.size + remaining) pageLimit ∧
    BorrowedWords heap store terrainNode terrain ∧ BorrowedWords heap store historyNode history ∧
    heap.OwnsWords store node row ∧ regionsDisjoint terrainNode.region node.region ∧
    regionsDisjoint historyNode.region node.region ∧ PreservesWords initialHeap initial heap store ∧
    (tracked = true → SeparateWords initialHeap initial node) ∧ row.size + 2 * fuel = totalSize ∧
    unwind fuel index state terrain history row = expected

set_option maxRecDepth 32768 in
theorem unwind_entry (env : HostEnv Unit) (store : Store Unit)
    (count index state : Nat) (terrain history row : UInt64) (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (func24.drop 8)
      (fun c => match c with
        | .Fallthrough final frame => P final (frame.values.take 2)
        | .Return final values => P final (values.take 2)
        | _ => False)
      store (unwindFrame count index state terrain history row false 0 0
        (List.replicate 36 (.i64 0)) zeroPushScratch) env) :
    TerminatesWith env Project.Drone.«module» 24 store
      [.i64 row, .i64 row, .i64 history, .i64 history, .i64 terrain, .i64 0,
        .i64 (UInt64.ofNat state), .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat count)] P := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_
  change wp Project.Drone.«module» func24 _ store
    { params := unwindParams count index state terrain history row, locals := List.replicate 57 (.i64 0) } env
  simp only [func24]
  wp_fixed_frame [unwindParams]
  simp only [func24, List.drop, unwindFrame, unwindParams, List.replicate, func24Def,
    zeroPushScratch, Scratch.words, Function.numParams, List.length, List.take,
    List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte] at hNext ⊢
  convert hNext using 1
  funext c
  cases c <;> rfl

#print axioms unwind_entry
end Project.Drone.Execution
