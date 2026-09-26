import Project.Beck.ExecutionInputEligible

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def inputTooShort : Wasm.Program :=
  match (func6[7]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def inputTooLarge : Wasm.Program :=
  match (inputInBounds[20]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 2048 in
theorem input_validate_shape : func6.take 8 =
    [.localGet 1, .localSet 52, .localGet 52, .wrapI64, .load64 0,
      .constI64 2, .ltUI64, .iff 0 0 inputTooShort inputInBounds] := rfl

set_option maxRecDepth 2048 in
theorem input_capacity_shape : inputInBounds = inputInBounds.take 20 ++ [.iff 0 0 inputTooLarge inputEligible] := rfl

def inputJoin (Q : Assertion Unit) : Assertion Unit := fun cont => match cont with
  | .Fallthrough st frame | .Break 0 st frame => Q (.Fallthrough st { frame with values := [] })
  | .Break (k + 1) st frame => Q (.Break k st frame)
  | other => Q other

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem inputValidate_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (saved : InputSaved) (tail : InputTail) (words : Array UInt64)
    (wordsAt : UInt64Array.At initial pointer words) (lengthBound : 2 ≤ words.size)
    (countBound : words[0]!.toNat ≤ 6) (categoryBound : words[1]!.toNat ≤ 8)
    (Q : Assertion Unit)
    (next : ∀ saved tail, wp Project.Beck.«module» inputEligible
      (inputJoin (inputJoin Q))
      initial (inputFrame pointer saved tail) env) :
    wp Project.Beck.«module» (func6.take 8) Q initial (inputFrame pointer saved tail) env := by
  have headerBound : pointer.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [wordsAt.pointerAddress_toNat]
    have := wordsAt.2.1
    omega
  have sizeFit := wordsAt.size_lt
  have headerGuard : ¬UInt64.ofNat words.size < 2 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' sizeFit]
    change ¬words.size < 2
    omega
  have firstRead : words[0] = words[0]! := (getElem!_pos words 0 (by omega)).symm
  have secondRead : words[1] = words[1]! := (getElem!_pos words 1 (by omega)).symm
  have firstGuard : ¬(6 : UInt64) < words[0]! := by rw [UInt64.lt_iff_toNat_lt]; change ¬6 < words[0]!.toNat; omega
  have secondGuard : ¬(8 : UInt64) < words[1]! := by rw [UInt64.lt_iff_toNat_lt]; change ¬8 < words[1]!.toNat; omega
  rw [input_validate_shape]
  generalize inBoundsEq : inputInBounds = code
  simp only [inputFrame, inputPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr headerBound, reduceIte, wordsAt.lengthRead]
  wp_fixed_frame [headerGuard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  rw [← inBoundsEq, input_capacity_shape]
  generalize eligibleEq : inputEligible = eligibleCode
  simp only [inputInBounds, func6, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 52 53 Project.Beck.«module» env initial _ pointer words 0 [.i64 6]
    rfl rfl rfl wordsAt (by omega) _ _ ?_
  wp_fixed_frame [firstRead, firstGuard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine CheckedArrayGet.checkedGetCore_spec 52 53 Project.Beck.«module» env initial _ pointer words 1 [.i64 8]
    rfl rfl rfl wordsAt (by omega) _ _ ?_
  repeat' ((try wp_fixed_frame [secondRead, secondGuard, List.take, List.drop, List.append_nil]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  wp_fixed_frame [secondRead, secondGuard, List.take, List.drop, List.append_nil]
  rw [← eligibleEq]
  convert next saved (inputPreparedTail tail pointer) using 2 <;> try rfl
  rename_i cont
  cases cont with
  | Break k st frame =>
    cases k with
    | zero => rfl
    | succ k => cases k <;> rfl
  | _ => rfl

#print axioms inputValidate_exact

end Project.Beck.Execution
