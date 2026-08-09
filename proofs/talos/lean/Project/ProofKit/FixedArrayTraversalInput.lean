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

def dynamicProgram (arrayLocal indexLocal itemLocal : Nat) : Wasm.Program :=
  [
  .localGet arrayLocal,
  .localGet indexLocal,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .localSet itemLocal
  ]

def continuingProgram (arrayLocal indexLocal stopLocal itemLocal : Nat) :
    Wasm.Program :=
  [
  .localGet indexLocal,
  .localGet stopLocal,
  .geUI64,
  .br_if 1
  ] ++ dynamicProgram arrayLocal indexLocal itemLocal

def dynamicResultFrame (frame : Locals) (itemLocal : Nat) (value : UInt64)
    (hItem : frame.validIndex itemLocal) : Locals :=
  frame.set itemLocal (.i64 value) hItem

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
theorem dynamicProgram_spec
    (arrayLocal indexLocal itemLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (hValues : frame.values = [])
    (hArrayLocal : frame.get arrayLocal = some (.i64 inputPtr))
    (hIndexLocal : frame.get indexLocal = some (.i64 (UInt64.ofNat index)))
    (hItem : frame.validIndex itemLocal)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (dynamicResultFrame frame itemLocal input[index] hItem) env) :
    wp module_ (dynamicProgram arrayLocal indexLocal itemLocal ++ rest)
      Q st frame env := by
  have hIndexLocalAfter :
      ({ frame with values := [.i64 inputPtr] } : Locals).get indexLocal =
        some (.i64 (UInt64.ofNat index)) := by
    simpa [Wasm.Locals.get] using hIndexLocal
  have hItemBound :
      itemLocal < frame.params.length + frame.locals.length := by
    simpa using hItem
  rcases hInput.generatedElement index hIndex with
    ⟨hElementBound, hElementRead⟩
  have hElementReadGenerated :
      st.mem.read64
          (UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296)) =
        input[index] := by
    simpa [Nat.mul_comm] using hElementRead
  have hOffset :
      (UInt64.ofNat index * 1 + 1) * 8 =
        UInt64.ofNat (8 * (index + 1)) := by
    rw [UInt64.mul_one]
    change
      (UInt64.ofNat index + UInt64.ofNat 1) * UInt64.ofNat 8 =
        UInt64.ofNat (8 * (index + 1))
    rw [← UInt64.ofNat_add]
    rw [← UInt64.ofNat_mul]
    congr 1
    omega
  have hGeneratedAddress :
      UInt32.ofNat
          ((inputPtr + (UInt64.ofNat index * 1 + 1) * 8).toNat % 2 ^ 32) =
        UInt32.ofNat
          ((inputPtr.toNat + (index + 1) * 8) % 4294967296) := by
    rw [hOffset]
    rw [show 2 ^ 32 = 4294967296 by norm_num]
    calc
      UInt32.ofNat
          ((inputPtr + UInt64.ofNat (8 * (index + 1))).toNat %
            4294967296) =
          (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 :=
        (Memory.toUInt32_eq_ofNat _).symm
      _ = UInt32.ofNat
          ((inputPtr.toNat + 8 * (index + 1)) % 4294967296) :=
        (hInput.elementAddress_eq index hIndex).symm
      _ = UInt32.ofNat
          ((inputPtr.toNat + (index + 1) * 8) % 4294967296) := by
        rw [Nat.mul_comm 8]
  simp only [dynamicProgram, List.cons_append, List.nil_append, wp_simp,
    hValues, hArrayLocal, hIndexLocalAfter]
  rw [UInt32.add_zero, hGeneratedAddress]
  rw [if_neg (by
    apply Nat.not_lt.mpr
    simpa using hElementBound)]
  rw [hElementReadGenerated]
  by_cases hParam : itemLocal < frame.params.length
  · simpa [dynamicResultFrame, Wasm.Locals.set?, hItem, hItemBound,
      hValues, hParam] using hNext
  · simpa [dynamicResultFrame, Wasm.Locals.set?, hItem, hItemBound,
      hValues, hParam] using hNext

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem continuingProgram_spec
    (arrayLocal indexLocal stopLocal itemLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr indexValue stopValue : UInt64)
    (input : Array UInt64) (index : Nat)
    (hValues : frame.values = [])
    (hArrayLocal : frame.get arrayLocal = some (.i64 inputPtr))
    (hIndexLocal : frame.get indexLocal = some (.i64 indexValue))
    (hStopLocal : frame.get stopLocal = some (.i64 stopValue))
    (hIndexValue : indexValue = UInt64.ofNat index)
    (hContinue : indexValue < stopValue)
    (hItem : frame.validIndex itemLocal)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (dynamicResultFrame frame itemLocal input[index] hItem) env) :
    wp module_
      (continuingProgram arrayLocal indexLocal stopLocal itemLocal ++ rest)
      Q st frame env := by
  have hStopLocalAfter :
      ({ frame with values := [.i64 indexValue] } : Locals).get stopLocal =
        some (.i64 stopValue) := by
    simpa [Wasm.Locals.get] using hStopLocal
  unfold continuingProgram
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append, wp_simp, hValues,
    hIndexLocal, hStopLocalAfter]
  rw [if_neg (by simpa [UInt64.not_le] using hContinue)]
  change wp module_ (dynamicProgram arrayLocal indexLocal itemLocal ++ rest)
    Q st { frame with values := [] } env
  have hFrame : ({ frame with values := [] } : Locals) = frame := by
    cases frame
    simp_all
  rw [hFrame]
  exact dynamicProgram_spec arrayLocal indexLocal itemLocal module_ env st frame
    inputPtr input index hValues hArrayLocal
    (by simpa [hIndexValue] using hIndexLocal) hItem hInput hIndex Q rest hNext

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
