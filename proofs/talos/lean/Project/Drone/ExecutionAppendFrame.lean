import Project.Drone.ExecutionPushBudget
import Project.Drone.ExecutionPredecessorRead
import Project.ProofKit.Annotation

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def appendBody : Wasm.Program :=
  match (func21[6]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def appendFrame (fuel state : Nat) (layerOwner layerPointer historyOwner historyPointer
    tracker resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64) : Locals :=
  { params := [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat state), .i64 layerOwner,
      .i64 layerPointer, .i64 historyOwner, .i64 historyPointer],
    locals := [.i64 0, .i64 tracker, .i64 resultOwner, .i64 resultPointer, .i64 0] ++
      (aux ++ (s.words ++ [.i64 extra])) }

def appendPreparedAux (aux : List Value) (state : Nat)
    (layerOwner layerPointer historyPointer : UInt64) : List Value :=
  (((aux.set 0 (.i64 (UInt64.ofNat (state + 1)))).set 1 (.i64 layerOwner)).set 2
    (.i64 layerPointer) |>.set 3 (.i64 historyPointer))

def appendPreparedScratch (s : Scratch) (state : Nat)
    (layerPointer historyPointer value : UInt64) : Scratch :=
  { s with
    source := historyPointer
    length := 1
    count := UInt64.ofNat (state + 1)
    value := value
    need := layerPointer
    previous := UInt64.ofNat (3 * state + 2)
    current := UInt64.ofNat (3 * state)
    capacity := 2
    next := UInt64.ofNat (3 * state + 2)
    root := 3 }

macro "wp_append_frame" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wp_fixed_frame [appendFrame, Scratch.words, List.length_append, List.length_cons,
    List.length_nil, List.length_set, List.getElem?_append, List.getElem?_set,
    List.set_append, List.cons_append, List.nil_append, Nat.reduceEqDiff,
    UInt64.lt_irrefl, $ts,*])

theorem append_push_shape : (appendBody.drop 55).take 67 = WordArrayPush.program 25 := rfl

theorem appendFrame_as_push (fuel state : Nat) (layerOwner layerPointer historyOwner historyPointer
    tracker resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64) :
    appendFrame fuel state layerOwner layerPointer historyOwner historyPointer tracker resultOwner
      resultPointer aux s extra = WordArrayPush.frame
      [.i64 (UInt64.ofNat fuel), .i64 (UInt64.ofNat state), .i64 layerOwner,
        .i64 layerPointer, .i64 historyOwner, .i64 historyPointer]
      ([.i64 0, .i64 tracker, .i64 resultOwner, .i64 resultPointer, .i64 0] ++ aux)
      [.i64 extra] s := by
  simp only [appendFrame, WordArrayPush.frame, List.append_assoc]

theorem appendPreparedAux_length (aux : List Value) (state : Nat)
    (layerOwner layerPointer historyPointer : UInt64) :
    (appendPreparedAux aux state layerOwner layerPointer historyPointer).length = aux.length := by
  simp [appendPreparedAux]

#print axioms append_push_shape
end Project.Drone.Execution
