import Project.SequenceSoftmax.Scalar
import Project.SequenceSoftmax.Model
import Project.ProofKit.ExactCall
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.BlockLoop

namespace Project.SequenceSoftmax.Spec
open Wasm Project.ProofKit

def maximumPrefix (input : Array UInt64) := ArrayFold.foldPrefix input Softmax.maximum input[0]!

def maximumSuffix : Wasm.Program :=
  [.localGet 2, .localSet 4, .localGet 3, .localSet 5,
   .localGet 4, .localGet 5, .call 7, .localSet 6,
   .localGet 6, .localSet 7, .localGet 7, .localSet 15,
   .constI64 0, .localSet 14, .localGet 15, .localSet 2,
   .constI64 1, .localSet 16, .localGet 14, .constI64 0, .neI64, .br_if 1,
   .localGet 11, .constI64 1, .addI64, .localSet 11, .br 0]

def maximumBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 9 11 13 3 ++ maximumSuffix

def maximumFrame (owner ptr : UInt64) (size index : Nat)
    (acc last arg0 arg1 result mid scratch carry ready : UInt64) : Locals :=
  { params := [.i64 owner, .i64 ptr]
    locals := [.i64 acc, .i64 last, .i64 arg0, .i64 arg1, .i64 result, .i64 mid,
      .i64 0, .i64 ptr, .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat size), .i64 scratch,
      .i64 carry, .i64 ready, .i64 0, .i64 0, .i64 0]
    values := [] }

def maximumInv (initial : Store Unit) (owner ptr : UInt64) (input : Array UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧ ∃ index last arg0 arg1 result mid scratch carry ready,
    index ≤ input.size ∧ frame = maximumFrame owner ptr input.size index
      (maximumPrefix input index) last arg0 arg1 result mid scratch carry ready

def maximumDone (initial : Store Unit) (owner ptr : UInt64) (input : Array UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧ ∃ last arg0 arg1 result mid scratch carry ready,
    frame = maximumFrame owner ptr input.size input.size
      (maximum input) last arg0 arg1 result mid scratch carry ready

def maximumMeasure (input : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 11 with
  | some (.i64 index) => input.size-index.toNat
  | _ => 0

macro "wp_maximum" : tactic => `(tactic|
  simp +arith [wp_simp, Locals.get, Locals.set?, Locals.set, Locals.validIndex,
    maximumFrame, FixedArrayTraversalInput.dynamicResultFrame])

theorem maximum_step (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial ptr input)
    (st : Store Unit) (frame : Locals) (hInv : maximumInv initial owner ptr input st frame) :
    wp module maximumBody
      (BlockLoop.stepPost (maximumInv initial owner ptr input) (maximumDone initial owner ptr input)
        (maximumMeasure input) (maximumMeasure input st frame)) st frame env := by
  rcases hInv with ⟨rfl, index, last, arg0, arg1, result, mid, scratch, carry, ready, hIndex, rfl⟩
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = input.size
  · subst index
    unfold maximumBody
    refine FixedArrayTraversalInput.continuingProgram_exit_spec 9 11 13 3 module env st _
      (UInt64.ofNat input.size) rfl (by simp +arith [maximumFrame, Locals.get])
      (by simp +arith [maximumFrame, Locals.get]) _ _ ?_
    refine ⟨rfl, last, arg0, arg1, result, mid, scratch, carry, ready, ?_⟩
    simp [maximumFrame, maximumPrefix, maximum, ArrayFold.foldPrefix_size]
  · have hi : index < input.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold maximumBody
    refine FixedArrayTraversalInput.continuingProgram_spec 9 11 13 3 module env st _
      ptr (UInt64.ofNat index) (UInt64.ofNat input.size) input index rfl
      (by simp +arith [maximumFrame, Locals.get]) (by simp +arith [maximumFrame, Locals.get])
      (by simp +arith [maximumFrame, Locals.get]) rfl hlt
      (by simp [maximumFrame, Locals.validIndex]) hInput hi _ _ ?_
    unfold maximumSuffix
    wp_maximum
    refine wp_call_exact_append (scalarMaximum_exact env st (maximumPrefix input index) input[index])
      rfl rfl rfl [] rfl ?_
    wp_maximum
    constructor
    · let next := Softmax.maximum (maximumPrefix input index) input[index]
      refine ⟨rfl, index+1, input[index], maximumPrefix input index, input[index],
        next, next, 0, next, 1, by omega, ?_⟩
      simp [maximumFrame, UInt64.ofNat_add, maximumPrefix, next, ArrayFold.foldPrefix_succ _ _ _ _ hi]
    · have hNextMod : (index+1)%18446744073709551616 = index+1 :=
        Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hInput.size_lt)
      simp +arith [maximumMeasure, Locals.get, hNextMod, hIndexNat]
      omega

theorem maximum_exact (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial ptr input) (hNonempty : 0 < input.size) :
    TerminatesWith env module 8 initial [.i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (maximum input)]) := by
  have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  have hPositive : (0 : UInt64) < UInt64.ofNat input.size := by
    simpa [UInt64.lt_iff_toNat_lt, hSizeNat] using hNonempty
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_ (by decide)
  change wp module func8 _ initial (func8Def.toLocals [.i64 owner, .i64 ptr]) env
  unfold func8
  wp_fixed_frame [func8Def]
  simp [hInput.pointerAddress_eq, hInput.lengthRead, hInput.generatedLengthBound]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [hPositive])]
  wp_fixed_frame [func8Def]
  have hBound := hInput.elementBound 0 hNonempty
  have hRead := hInput.elementRead 0 hNonempty
  simp +arith [Memory.toUInt32_eq_ofNat] at hBound hRead
  simp +arith [hBound, hRead]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp)]
  wp_fixed_frame [func8Def]
  change wp module ([.block 0 0 [.loop 0 0 maximumBody]] ++ _) _ initial
    (maximumFrame owner ptr input.size 0 input[0] 0 0 0 0 0 ptr 0 0) env
  refine BlockLoop.program_spec module env initial _ maximumBody
    (maximumInv initial owner ptr input) (maximumDone initial owner ptr input) (maximumMeasure input)
    ?_ ?_ ?_ (maximum_step env initial owner ptr input hInput) _ _ ?_
  · rintro st frame ⟨_, index, last, arg0, arg1, result, mid, scratch, carry, ready, _, rfl⟩
    rfl
  · rintro st frame ⟨_, last, arg0, arg1, result, mid, scratch, carry, ready, rfl⟩
    rfl
  · refine ⟨rfl, 0, 0, 0, 0, 0, 0, ptr, 0, 0, Nat.zero_le _, ?_⟩
    simp [maximumPrefix, ArrayFold.foldPrefix, hNonempty]
  · rintro st frame ⟨rfl, last, arg0, arg1, result, mid, scratch, carry, ready, rfl⟩
    wp_maximum

#print axioms maximum_step
#print axioms maximum_exact
end Project.SequenceSoftmax.Spec
