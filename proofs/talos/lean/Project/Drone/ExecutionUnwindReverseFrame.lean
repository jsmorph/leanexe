import Project.Drone.ExecutionUnwindFrame
import Project.Drone.ExecutionReverseProgram

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

def unwindReverseBody : Wasm.Program :=
  match (func24[12]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def unwindReverseSaved (row : UInt64) (tracked : Bool) (out0 out1 : UInt64) (aux : List Value) : List Value :=
  [.i64 0, .i64 (if tracked then row else 0), .i64 0, .i64 out0, .i64 out1, .i64 0] ++ aux.take 33

def unwindReverseScratch (s : Scratch) (row : UInt64) (size : Nat) : Scratch :=
  { source := 0, length := row, count := 0, nextLength := row, target := UInt64.ofNat size,
    counter := s.count, value := s.nextLength, spare0 := s.target, spare1 := s.counter,
    need := s.value, previous := s.spare0, current := s.spare1, capacity := s.need,
    next := s.previous, root := s.current }

def unwindReverseTail (s : Scratch) : List Value := [.i64 s.capacity, .i64 s.next, .i64 s.root]

theorem unwind_aux_split (aux : List Value) (hAux : aux.length = 36)
    (h33 : aux[33]? = some (.i64 0)) (h35 : aux[35]? = some (.i64 0)) :
    aux = aux.take 33 ++ [.i64 0, aux[34]'(by omega), .i64 0] := by
  have hTail : aux.drop 33 = [.i64 0, aux[34]'(by omega), .i64 0] := by
    rw [List.drop_eq_getElem?_toList_append, h33]
    rw [List.drop_eq_getElem?_toList_append (i := 34)]
    rw [List.drop_eq_getElem?_toList_append (i := 35), h35]
    simp [hAux]
  rw [← hTail, List.take_append_drop]

set_option maxRecDepth 32768 in
theorem unwind_reverse_shape :
    unwindReverseBody = unwindReverseBody.take 11 ++
      [.iff 0 1 [.localGet 51] (reverseProgram 48) [] [.i64]] ++ unwindReverseBody.drop 12 := rfl

end Project.Drone.Execution
