import Project.Drone.ExecutionAppendStep
import Project.ProofKit.FuelGuard

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def appendCost : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, size => pushCost size + appendCost count (size + 1)

def zeroPushScratch : Scratch := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def appendInv (initialHeap : Heap) (initial : Store Unit) (layerNode : FreeNode)
    (layer expected : Array UInt64) (count bound remaining pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ (heap : Heap) (node : FreeNode) (history : Array UInt64) (fuel state : Nat)
    (tracked : Bool) (resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64),
    frame = appendFrame fuel state layerNode.root layerNode.root node.root node.root
      (if tracked then node.root else 0) resultOwner resultPointer aux s extra ∧
    aux.length = 14 ∧ fuel ≤ count ∧ state + fuel = bound ∧
    (tracked = true ↔ fuel < count) ∧ heap.At store ∧
    Budget store heap (appendCost fuel history.size + remaining) pageLimit ∧
    BorrowedWords heap store layerNode layer ∧ heap.OwnsWords store node history ∧
    regionsDisjoint layerNode.region node.region ∧ PreservesWords initialHeap initial heap store ∧
    (tracked = true → SeparateWords initialHeap initial node) ∧
    appendParents fuel state layer history = expected

def appendMeasure (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.params with
  | .i64 fuel :: _ => fuel.toNat
  | _ => 0

def AppendResult (initialHeap : Heap) (initial : Store Unit) (layerNode : FreeNode)
    (layer output : Array UInt64) (count remaining pageLimit : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ (heap : Heap) (node : FreeNode), heap.At final ∧ Budget final heap remaining pageLimit ∧
    BorrowedWords heap final layerNode layer ∧ heap.OwnsWords final node output ∧
    regionsDisjoint layerNode.region node.region ∧ PreservesWords initialHeap initial heap final ∧
    (0 < count → SeparateWords initialHeap initial node) ∧ values = [.i64 node.root, .i64 node.root]

theorem appendParents_entry (env : HostEnv Unit) (initial : Store Unit)
    (layerPointer historyPointer : UInt64) (count state : Nat)
    (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (func21.drop 6)
      (fun c => match c with
        | .Fallthrough store frame => P store (frame.values.take 2)
        | .Return store values => P store (values.take 2)
        | _ => False)
      initial (appendFrame count state layerPointer layerPointer historyPointer historyPointer
        0 0 0 (List.replicate 14 (.i64 0)) zeroPushScratch 0) env) :
    TerminatesWith env Project.Drone.«module» 21 initial
      [.i64 historyPointer, .i64 historyPointer, .i64 layerPointer, .i64 layerPointer,
        .i64 (UInt64.ofNat state), .i64 (UInt64.ofNat count)] P := by
  refine TerminatesWith.of_wp_entry_for (f := func21Def) rfl ?_
  change wp Project.Drone.«module» func21 _ initial
    { params := [.i64 (UInt64.ofNat count), .i64 (UInt64.ofNat state), .i64 layerPointer,
        .i64 layerPointer, .i64 historyPointer, .i64 historyPointer],
      locals := List.replicate 35 (.i64 0) } env
  simp only [func21]
  wp_fixed_frame
  simp only [func21, List.drop, appendFrame, List.replicate, func21Def, zeroPushScratch, Scratch.words,
    Function.numParams, List.length, List.take, List.cons_append, List.nil_append,
    List.append_nil, Nat.reduceAdd] at hNext ⊢
  convert hNext using 1
  funext c
  cases c <;> rfl

#print axioms appendParents_entry
end Project.Drone.Execution
