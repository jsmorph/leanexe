import Project.Drone.ExecutionUnwindReverseFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem unwind_reverse_finish_spec (env : HostEnv Unit) (store : Store Unit)
    (index state : Nat) (terrain history row root : UInt64) (tracked : Bool) (out0 out1 : UInt64)
    (aux tail : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 36) (hTail : tail.length = 3)
    (hSource : s.length = row) (hInput : UInt64Array.At store row input) (hSize : 1 < input.size)
    (P : Store Unit → List Value → Prop) (hNext : P store [.i64 root, .i64 root]) :
    wp Project.Drone.«module» (unwindReverseBody.drop 12)
      (fun c => match c with
        | .Fallthrough final f | .Break 0 final f =>
          wp Project.Drone.«module» (func24.drop 13)
            (fun c => match c with
              | .Fallthrough finish f => P finish (f.values.take 2)
              | .Return finish values => P finish (values.take 2)
              | _ => False)
            final { params := f.params, locals := f.locals } env
        | .Return final values => P final (values.take 2)
        | _ => False)
      store { frame (unwindParams 0 index state terrain history row)
        (unwindReverseSaved row tracked out0 out1 aux) tail s with values := [.i64 root] } env := by
  have hPrefix : (aux.take 33).length = 33 := by simp [hAux]
  have hLength := hInput.lengthRead
  have hBound := hInput.generatedLengthBound
  have hAddress := hInput.pointerAddress_eq
  have hRead : store.mem.read64 (UInt32.ofNat (row.toNat % 4294967296)) = UInt64.ofNat input.size := by
    rw [hAddress]; exact hLength
  have hLarge : ¬ UInt64.ofNat input.size ≤ 1 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hInput.size_lt]
    exact Nat.not_le.mpr hSize
  simp only [unwindReverseBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.cons_append, List.nil_append]
  unwind_controls [frame, unwindReverseSaved, hPrefix, hSource, hLength, hBound, hAddress, hRead, hLarge,
    show 2^32 = 4294967296 by decide, UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero,
    Nat.not_lt.mpr hInput.lengthBound, hTail]
  exact hNext

#print axioms unwind_reverse_finish_spec
end Project.Drone.Execution
