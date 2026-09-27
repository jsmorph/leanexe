import Project.ProofKit.FixedArrayTraversalInput

namespace Project.ProofKit.CheckedArrayGet

open Wasm

/--
The checked `Array UInt64` element load emitted after the compiler has staged
the array pointer and element index in locals.  The explicit control types
match generated programs; `Project.TalosCompat` proves they do not affect the
modeled execution.
-/
def checkedGetCore (pointerLocal indexLocal : Nat) : Wasm.Program :=
  [
  .localGet indexLocal,
  .localGet pointerLocal,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet pointerLocal,
    .localGet indexLocal,
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
  ] [] [.i64]
  ]

macro "wp_checked_array_get" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) only [
      wp_simp, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      Nat.reducePow, Nat.zero_mod, Nat.add_zero,
      UInt32.add_zero, UInt32.toNat_zero, UInt32.toNat_ofNat,
      Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left, $ts,*])

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem checkedGetCore_spec
    (pointerLocal indexLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (pointer : UInt64) (input : Array UInt64) (index : Nat)
    (tail : List Value)
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hIndex : frame.get indexLocal = some (.i64 (UInt64.ofNat index)))
    (hValues : frame.values = tail)
    (hArray : UInt64Array.At store pointer input)
    (hIndexBound : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i64 input[index] :: tail } env) :
    wp module_ (checkedGetCore pointerLocal indexLocal ++ rest)
      Q store frame env := by
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hPointerAddress := hArray.pointerAddress_eq
  have hElement := hArray.generatedElement index hIndexBound
  have hElementRead :
      store.mem.read64
          (UInt32.ofNat ((pointer.toNat + (index + 1) * 8) % 4294967296)) =
        input[index] := by
    simpa [Nat.mul_comm] using hElement.2
  have hElementBound :
      (UInt32.ofNat
          ((pointer.toNat + (index + 1) * 8) % 4294967296)).toNat + 8 ≤
        store.mem.pages * 65536 := by
    rw [UInt32.toNat_ofNat_of_lt'
      (Nat.mod_lt _ (by norm_num : 0 < 4294967296))]
    exact hElement.1
  have hIndex64 : index < UInt64.size := by
    have hSize := hArray.size_lt
    omega
  have hIndexToNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' hIndex64
  have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hArray.size_lt
  have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
    rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
    exact hIndexBound
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
          ((pointer + (UInt64.ofNat index * 1 + 1) * 8).toNat %
            4294967296) =
        UInt32.ofNat
          ((pointer.toNat + (index + 1) * 8) % 4294967296) := by
    rw [hOffset]
    calc
      UInt32.ofNat
          ((pointer + UInt64.ofNat (8 * (index + 1))).toNat %
            4294967296) =
          (pointer + UInt64.ofNat (8 * (index + 1))).toUInt32 :=
        (Memory.toUInt32_eq_ofNat _).symm
      _ = UInt32.ofNat
          ((pointer.toNat + 8 * (index + 1)) % 4294967296) :=
        (hArray.elementAddress_eq index hIndexBound).symm
      _ = UInt32.ofNat
          ((pointer.toNat + (index + 1) * 8) % 4294967296) := by
        rw [Nat.mul_comm 8]
  have hPointerAfterIndex :
      ({ frame with values := .i64 (UInt64.ofNat index) :: tail } : Locals).get
          pointerLocal = some (.i64 pointer) := by
    simpa only [Wasm.Locals.get] using hPointer
  have hPointerAtTail :
      ({ frame with values := tail } : Locals).get pointerLocal =
        some (.i64 pointer) := by
    simpa only [Wasm.Locals.get] using hPointer
  have hIndexAfterPointer :
      ({ frame with values := .i64 pointer :: tail } : Locals).get indexLocal =
        some (.i64 (UInt64.ofNat index)) := by
    simpa only [Wasm.Locals.get] using hIndex
  simp only [checkedGetCore, List.cons_append, List.nil_append]
  wp_checked_array_get [hPointerAfterIndex, hIndex, hValues, hLengthRead,
    hPointerAddress, hIndexToNat]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hIndexEncoded])]
  wp_checked_array_get [hPointerAtTail, hIndexAfterPointer, hValues, hLengthRead,
    hPointerAddress, hIndexToNat]
  rw [hGeneratedAddress]
  rw [if_neg (Nat.not_lt.mpr hElementBound)]
  rw [hElementRead]
  simpa [hValues] using hNext

#print axioms checkedGetCore_spec

end Project.ProofKit.CheckedArrayGet
