import Project.Drone.ExecutionHistoryStep
import Project.Drone.History

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def historyCost : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, size => 56 + (advanceCost 45 0 + (appendCost 45 size + historyCost count (size + 45)))

def historyInv (initialHeap : Heap) (initial : Store Unit) (terrainNode : FreeNode)
    (terrain expected : Array UInt64) (count bound remaining pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ (heap : Heap) (previousNode historyNode : FreeNode) (previous history : Array UInt64)
    (fuel index : Nat) (out0 out1 : UInt64) (aux : List Value) (s : Scratch),
    frame = historyFrame fuel index terrainNode.root previousNode.root historyNode.root out0 out1 aux s ∧
    aux.length = 44 ∧ fuel ≤ count ∧ index + fuel = bound ∧ heap.At store ∧
    Budget store heap (historyCost fuel history.size + remaining) pageLimit ∧
    BorrowedWords heap store terrainNode terrain ∧ BorrowedWords heap store previousNode previous ∧
    135 ≤ previous.size ∧ heap.OwnsWords store historyNode history ∧
    regionsDisjoint terrainNode.region historyNode.region ∧ PreservesWords initialHeap initial heap store ∧
    (fuel < count → SeparateWords initialHeap initial historyNode) ∧
    buildHistory fuel index terrain previous history = expected

set_option maxRecDepth 32768 in
theorem history_entry (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history : UInt64) (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (func22.drop 8)
      (fun c => match c with
        | .Fallthrough final frame => P final (frame.values.take 2)
        | .Return final values => P final (values.take 2)
        | _ => False)
      store (historyFrame fuel index terrain previous history 0 0 (List.replicate 44 (.i64 0)) zeroPushScratch) env) :
    TerminatesWith env Project.Drone.«module» 22 store
      [.i64 history, .i64 history, .i64 previous, .i64 previous, .i64 terrain, .i64 terrain,
        .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat fuel)] P := by
  refine TerminatesWith.of_wp_entry_for (f := func22Def) rfl ?_
  change wp Project.Drone.«module» func22 _ store
    { params := historyParams fuel index terrain previous history, locals := List.replicate 65 (.i64 0) } env
  simp only [func22]
  wp_fixed_frame [historyParams]
  simp only [func22, List.drop, historyFrame, historyParams, List.replicate, func22Def,
    zeroPushScratch, Scratch.words, Function.numParams, List.length, List.take,
    List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd] at hNext ⊢
  convert hNext using 1
  funext c
  cases c <;> rfl

#print axioms history_entry
end Project.Drone.Execution
