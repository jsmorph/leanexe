import Project.ProofKit.Array

namespace Project.ProofKit.FixedArrayInput

open Wasm

theorem add_succ_sub_one (offset k : Nat) :
    offset + (k + 1) - 1 = offset + k := by
  omega

macro "wp_input_window" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      List.length_set, List.getElem?_set, List.getElem?_cons_zero,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left,
      add_succ_sub_one, $ts,*])

def program (offset index : Nat) : Wasm.Program :=
  [
  .localGet 0,
  .localSet (offset + 9),
  .constI64 (UInt64.ofNat index),
  .localSet (offset + 10),
  .localGet (offset + 10),
  .localGet (offset + 9),
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet (offset + 9),
    .localGet (offset + 10),
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
  ],
  .localSet (offset + 8)
  ]

def resultFrame (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) : Locals :=
  { frame with
    locals := ((frame.locals.set (offset + 8) (.i64 inputPtr)).set
      (offset + 9) (.i64 (UInt64.ofNat index))).set
      (offset + 7) (.i64 value) }

theorem resultFrame_params (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).params = frame.params := rfl

theorem resultFrame_locals_length (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).locals.length =
      frame.locals.length := by
  simp [resultFrame]

theorem resultFrame_values (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) :
    (resultFrame offset frame inputPtr index value).values = frame.values := rfl

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (offset : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64) (index : Nat)
    (hParamsValue : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (resultFrame offset frame inputPtr index input[index]) env) :
    wp module_ (program offset index ++ rest) Q st frame env := by
  have hNot8 : ¬offset + 8 < 1 := by omega
  have hNot9 : ¬offset + 9 < 1 := by omega
  have hNot10 : ¬offset + 10 < 1 := by omega
  have hValid8 : offset + 8 < 1 + (offset + 14) := by omega
  have hValid9 : offset + 9 < 1 + (offset + 14) := by omega
  have hValid10 : offset + 10 < 1 + (offset + 14) := by omega
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.lengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hValueRead := hInput.elementRead index hIndex
  have hValueBound := hInput.elementBound index hIndex
  have hValueAddress := hInput.elementAddress_eq index hIndex
  have hValueAddress' :
      UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296) =
        (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
    simpa [Nat.mul_comm] using hValueAddress
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
  have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
  have hValueBound' :
      (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
    have hBound :
        (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
          4294967296)).toNat + 8 ≤ st.mem.pages * 65536 := by
      rw [hValueAddress]
      exact hValueBound
    simpa [Nat.mul_comm] using hBound
  simp only [program, List.cons_append, List.nil_append]
  wp_input_window [hParamsValue, hLocals, hValues, hLengthRead,
    hInputAddress, hValueRead, hValueAddress, hIndexToNat, hIndex,
    hNot8, hNot9, hNot10, hValid8, hValid9, hValid10]
  rw [if_neg (Nat.not_lt.mpr hLengthBound')]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hIndexEncoded])]
  wp_input_window [hParamsValue, hLocals, hValues, hLengthRead,
    hInputAddress, hValueRead, hValueAddress, hIndexToNat, hIndex,
    hNot8, hNot9, hNot10, hValid8, hValid9, hValid10]
  rw [if_neg (Nat.not_lt.mpr hValueBound')]
  rw [hValueAddress', hValueRead]
  simpa [resultFrame, hParamsValue, hLocals, hValues,
    List.getElem?_set] using hNext

end Project.ProofKit.FixedArrayInput
