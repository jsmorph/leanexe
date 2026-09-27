import Project.Drone.ExecutionAdvanceStep
import Project.Drone.ExecutionAppendInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def advanceCost : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, size => rowPushCost size + advanceCost count (size + 3)

def advanceInv (initialHeap : Heap) (initial : Store Unit) (r0 r1 : UInt64) (last : Bool)
    (previousNode : FreeNode) (previous expected : Array UInt64) (count bound remaining pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ (heap : Heap) (node : FreeNode) (row : Array UInt64) (fuel target : Nat)
    (tracked : Bool) (resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch),
    frame = advanceFrame fuel target r0 r1 last previousNode.root previousNode.root node.root node.root
      (if tracked then node.root else 0) resultOwner resultPointer aux s ∧
    aux.length = 38 ∧ fuel ≤ count ∧ target + fuel = bound ∧
    (tracked = true ↔ fuel < count) ∧ heap.At store ∧
    Budget store heap (advanceCost fuel row.size + remaining) pageLimit ∧
    BorrowedWords heap store previousNode previous ∧ heap.OwnsWords store node row ∧
    regionsDisjoint previousNode.region node.region ∧ PreservesWords initialHeap initial heap store ∧
    (tracked = true → SeparateWords initialHeap initial node) ∧
    advanceLoop fuel target r0 r1 last previous row = expected

def AdvanceResult (initialHeap : Heap) (initial : Store Unit) (previousNode : FreeNode)
    (previous output : Array UInt64) (count remaining pageLimit : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ (heap : Heap) (node : FreeNode), heap.At final ∧ Budget final heap remaining pageLimit ∧
    BorrowedWords heap final previousNode previous ∧ heap.OwnsWords final node output ∧
    regionsDisjoint previousNode.region node.region ∧ PreservesWords initialHeap initial heap final ∧
    (0 < count → SeparateWords initialHeap initial node) ∧ values = [.i64 node.root, .i64 node.root]

set_option maxRecDepth 32768 in
theorem advanceLoop_entry (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 : UInt64) (last : Bool) (previousPointer rowPointer : UInt64) (count target : Nat)
    (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (func18.drop 6)
      (fun c => match c with
        | .Fallthrough store frame => P store (frame.values.take 2)
        | .Return store values => P store (values.take 2)
        | _ => False)
      initial (advanceFrame count target r0 r1 last previousPointer previousPointer rowPointer rowPointer
        0 0 0 (List.replicate 38 (.i64 0)) zeroPushScratch) env) :
    TerminatesWith env Project.Drone.«module» 18 initial
      [.i64 rowPointer, .i64 rowPointer, .i64 previousPointer, .i64 previousPointer,
        .i64 (if last then 1 else 0), .i64 r1, .i64 r0,
        .i64 (UInt64.ofNat target), .i64 (UInt64.ofNat count)] P := by
  refine TerminatesWith.of_wp_entry_for (f := func18Def) rfl ?_
  change wp Project.Drone.«module» func18 _ initial
    { params := [.i64 (UInt64.ofNat count), .i64 (UInt64.ofNat target), .i64 r0, .i64 r1,
        .i64 (if last then 1 else 0), .i64 previousPointer, .i64 previousPointer, .i64 rowPointer, .i64 rowPointer],
      locals := List.replicate 58 (.i64 0) } env
  simp only [func18]
  wp_fixed_frame
  simp only [func18, List.drop, advanceFrame, List.replicate, func18Def, zeroPushScratch, Scratch.words,
    Function.numParams, List.length, List.take, List.cons_append, List.nil_append,
    List.append_nil, Nat.reduceAdd] at hNext ⊢
  convert hNext using 1
  funext c
  cases c <;> rfl

#print axioms advanceLoop_entry
end Project.Drone.Execution
