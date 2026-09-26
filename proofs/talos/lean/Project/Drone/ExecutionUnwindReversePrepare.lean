import Project.Drone.ExecutionUnwindReverseFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

theorem unwind_reverse_frame_eq (index state : Nat) (terrain history row : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (size : Nat) (hAux : aux.length = 36)
    (h33 : aux[33]? = some (.i64 0)) (h35 : aux[35]? = some (.i64 0)) :
    unwindFrame 0 index state terrain history row tracked out0 out1 (aux.set 34 (.i64 row))
        { s with source := row, length := UInt64.ofNat size } =
      frame (unwindParams 0 index state terrain history row) (unwindReverseSaved row tracked out0 out1 aux)
        (unwindReverseTail s) (unwindReverseScratch s row size) := by
  have hPrefix : (aux.take 33).length = 33 := by simp [hAux]
  conv_lhs => rw [unwind_aux_split aux hAux h33 h35]
  simp [unwindFrame, unwindReverseSaved, unwindReverseTail, unwindReverseScratch, frame,
    Scratch.words, List.set_append, hPrefix, List.append_assoc]

set_option maxRecDepth 32768 in
theorem unwind_reverse_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (index state : Nat) (terrain history row : UInt64) (tracked : Bool) (out0 out1 : UInt64)
    (aux : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 36)
    (h33 : aux[33]? = some (.i64 0)) (h35 : aux[35]? = some (.i64 0))
    (hInput : UInt64Array.At store row input) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (frame (unwindParams 0 index state terrain history row) (unwindReverseSaved row tracked out0 out1 aux)
        (unwindReverseTail s) (unwindReverseScratch s row input.size)) env) :
    wp Project.Drone.«module» (unwindReverseBody.take 8 ++ rest) Q store
      (unwindFrame 0 index state terrain history row tracked out0 out1 aux s) env := by
  have hLength := hInput.lengthRead
  have hBound := hInput.generatedLengthBound
  have hAddress := hInput.pointerAddress_eq
  have hRead : store.mem.read64 (UInt32.ofNat (row.toNat % 4294967296)) = UInt64.ofNat input.size := by
    rw [hAddress]; exact hLength
  rw [← unwind_reverse_frame_eq index state terrain history row tracked out0 out1 aux s input.size hAux h33 h35] at hNext
  simp only [unwindReverseBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take,
    List.cons_append, List.nil_append]
  wp_unwind_frame [hAux, hLength, hBound, hAddress, hRead, show 2^32 = 4294967296 by decide,
    UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr hInput.lengthBound]
  exact hNext

#print axioms unwind_reverse_frame_eq
#print axioms unwind_reverse_prepare_spec
end Project.Drone.Execution
