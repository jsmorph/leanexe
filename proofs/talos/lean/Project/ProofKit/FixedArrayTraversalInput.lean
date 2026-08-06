import Project.ProofKit.Array

namespace Project.ProofKit.FixedArrayTraversalInput

open Wasm

theorem add_succ_sub_one (offset k : Nat) :
    offset + (k + 1) - 1 = offset + k := by
  omega

macro "wp_traversal_input" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) [
      wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
      Wasm.Locals.validIndex, List.length_set, List.getElem?_set,
      List.getElem?_cons_zero,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left,
      add_succ_sub_one, $ts,*])

def program (offset index : Nat) : Wasm.Program :=
  [
  .localGet 0,
  .localSet (offset + 5),
  .constI64 (UInt64.ofNat index),
  .localSet (offset + 6),
  .localGet (offset + 6),
  .localGet (offset + 5),
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet (offset + 5),
    .localGet (offset + 6),
    .constI64 1,
    .mulI64,
    .constI64 1,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ]
  ]

def resultFrame (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) : Locals :=
  { frame with
    locals := (frame.locals.set (offset + 4) (.i64 inputPtr)).set
      (offset + 5) (.i64 (UInt64.ofNat index)),
    values := [.i64 value] }

def stackedResultFrame (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) (tail : List Value) : Locals :=
  { frame with
    locals := (frame.locals.set (offset + 4) (.i64 inputPtr)).set
      (offset + 5) (.i64 (UInt64.ofNat index)),
    values := .i64 value :: tail }

theorem resultFrame_params (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).params = frame.params := rfl

theorem resultFrame_locals_length (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).locals.length =
      frame.locals.length := by
  simp [resultFrame]

theorem resultFrame_values (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).values = [.i64 value] := rfl

theorem stackedResultFrame_params (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) (tail : List Value) :
    (stackedResultFrame offset frame inputPtr index value tail).params =
      frame.params := rfl

theorem stackedResultFrame_locals_length (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) (tail : List Value) :
    (stackedResultFrame offset frame inputPtr index value tail).locals.length =
      frame.locals.length := by
  simp [stackedResultFrame]

theorem stackedResultFrame_values (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) (tail : List Value) :
    (stackedResultFrame offset frame inputPtr index value tail).values =
      .i64 value :: tail := rfl

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (offset : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (resultFrame offset frame inputPtr index input[index]) env) :
    wp module_ (program offset index ++ rest) Q st frame env := by
  have hNot5 : ¬offset + 5 < 1 := by omega
  have hNot6 : ¬offset + 6 < 1 := by omega
  have hValid5 : offset + 5 < 1 + (offset + 14) := by omega
  have hValid6 : offset + 6 < 1 + (offset + 14) := by omega
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hValue := hInput.generatedElement index hIndex
  have hValueRead :
      st.mem.read64
          (UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
        input[index] := by
    simpa [Nat.mul_comm] using hValue.2
  have hIndex64 : index < UInt64.size := by
    have hSize := hInput.size_lt
    omega
  have hIndexToNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' hIndex64
  have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
    rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
    exact hIndex
  simp only [program, List.cons_append, List.nil_append]
  wp_traversal_input [hParams, hLocals, hValues, hLengthRead, hInputAddress,
    hIndexToNat, hNot5, hNot6, hValid5, hValid6]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hIndexEncoded])]
  wp_traversal_input [hParams, hLocals, hValues, hLengthRead, hInputAddress,
    hIndexToNat, hNot5, hNot6, hValid5, hValid6]
  rw [if_neg (Nat.not_lt.mpr hValue.1)]
  rw [hValueRead]
  simpa [resultFrame, hParams, hLocals, hValues] using hNext

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_stacked_spec
    (offset : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (tail : List Value)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = tail)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (stackedResultFrame offset frame inputPtr index input[index] tail) env) :
    wp module_ (program offset index ++ rest) Q st frame env := by
  have hNot5 : ¬offset + 5 < 1 := by omega
  have hNot6 : ¬offset + 6 < 1 := by omega
  have hValid5 : offset + 5 < 1 + (offset + 14) := by omega
  have hValid6 : offset + 6 < 1 + (offset + 14) := by omega
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hValue := hInput.generatedElement index hIndex
  have hValueRead :
      st.mem.read64
          (UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
        input[index] := by
    simpa [Nat.mul_comm] using hValue.2
  have hIndex64 : index < UInt64.size := by
    have hSize := hInput.size_lt
    omega
  have hIndexToNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' hIndex64
  have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
    rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
    exact hIndex
  simp only [program, List.cons_append, List.nil_append]
  wp_traversal_input [hParams, hLocals, hValues, hLengthRead, hInputAddress,
    hIndexToNat, hNot5, hNot6, hValid5, hValid6]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hIndexEncoded])]
  wp_traversal_input [hParams, hLocals, hValues, hLengthRead, hInputAddress,
    hIndexToNat, hNot5, hNot6, hValid5, hValid6]
  rw [if_neg (Nat.not_lt.mpr hValue.1)]
  rw [hValueRead]
  simpa [stackedResultFrame, hParams, hLocals, hValues] using hNext

end Project.ProofKit.FixedArrayTraversalInput
