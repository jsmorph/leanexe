import Project.Drone.ExecutionInitialStep
import Project.Drone.ExecutionAdvanceInvariant
import Project.ProofKit.RangeGuard
import Project.ProofKit.RangeFoldLoop

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def initialInv (initialHeap : Heap) (initial : Store Unit) (seed : UInt64) (remaining pageLimit : Nat)
    (store : Store Unit) (frame : Locals) : Prop :=
  ∃ (heap : Heap) (node : FreeNode) (row : Array UInt64) (state : Nat) (tracked : Bool)
    (aux : List Value) (s : Scratch) (out0 out1 : UInt64),
    frame = initialFrame seed node.root state tracked aux s out0 out1 ∧
    aux.length = 19 ∧ state ≤ 45 ∧ (tracked = true ↔ 0 < state) ∧
    (node.root = seed ↔ tracked = false) ∧ heap.At store ∧
    Budget store heap (advanceCost (45 - state) row.size + remaining) pageLimit ∧
    heap.OwnsWords store node row ∧ PreservesWords initialHeap initial heap store ∧
    (tracked = true → SeparateWords initialHeap initial node) ∧
    initialRows (45 - state) state row = initialRows 45 0 #[]

end Project.Drone.Execution
