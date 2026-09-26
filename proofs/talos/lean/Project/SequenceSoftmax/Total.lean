import Project.SequenceSoftmax.Program
import Project.SequenceSoftmax.Model
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.BlockLoop
import Project.ProofKit.FixedFrame

namespace Project.SequenceSoftmax.Spec
open Wasm Project.ProofKit

def totalPrefix (input : Array UInt64) := ArrayFold.foldPrefix input Wasm.IEEE64.add 0

def totalSuffix : Wasm.Program :=
  [.localGet 2, .f64ReinterpretI64, .localGet 3, .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .localSet 4, .localGet 4, .localSet 12,
   .constI64 0, .localSet 11, .localGet 12, .localSet 2, .localGet 11, .constI64 0, .neI64, .br_if 1,
   .localGet 8, .constI64 1, .addI64, .localSet 8, .br 0]

def totalBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 6 8 10 3 ++ totalSuffix

def totalFrame (owner ptr : UInt64) (size index : Nat) (acc last result scratch carry ready : UInt64) : Locals :=
  { params := [.i64 owner, .i64 ptr]
    locals := [.i64 acc, .i64 last, .i64 result, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat index),
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat size),
      .i64 scratch, .i64 carry, .i64 ready, .i64 0, .i64 0]
    values := [] }

def totalInv (initial : Store Unit) (owner ptr : UInt64) (input : Array UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧ ∃ index last result scratch carry ready,
    index ≤ input.size ∧
    frame = totalFrame owner ptr input.size index (totalPrefix input index) last result scratch carry ready

def totalDone (initial : Store Unit) (owner ptr : UInt64) (input : Array UInt64) : AssertionF Unit :=
  fun st frame => st = initial ∧ ∃ last result scratch carry ready,
    frame = totalFrame owner ptr input.size input.size (total input) last result scratch carry ready

def totalMeasure (input : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 8 with
  | some (.i64 index) => input.size-index.toNat
  | _ => 0

macro "wp_total" : tactic => `(tactic|
  simp +arith [wp_simp, Locals.get, Locals.set?, Locals.set, Locals.validIndex,
    totalFrame, FixedArrayTraversalInput.dynamicResultFrame, Wasm.f64Add])

theorem total_step (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial ptr input)
    (st : Store Unit) (frame : Locals) (hInv : totalInv initial owner ptr input st frame) :
    wp module totalBody
      (BlockLoop.stepPost (totalInv initial owner ptr input) (totalDone initial owner ptr input)
        (totalMeasure input) (totalMeasure input st frame)) st frame env := by
  rcases hInv with ⟨rfl, index, last, result, scratch, carry, ready, hIndex, rfl⟩
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = input.size
  · subst index
    unfold totalBody
    refine FixedArrayTraversalInput.continuingProgram_exit_spec 6 8 10 3 module env st _
      (UInt64.ofNat input.size) rfl (by simp +arith [totalFrame, Locals.get])
      (by simp +arith [totalFrame, Locals.get]) _ _ ?_
    refine ⟨rfl, last, result, scratch, carry, ready, ?_⟩
    simp [totalFrame, totalPrefix, total, ArrayFold.foldPrefix_size]
  · have hi : index < input.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold totalBody
    refine FixedArrayTraversalInput.continuingProgram_spec 6 8 10 3 module env st _
      ptr (UInt64.ofNat index) (UInt64.ofNat input.size) input index rfl
      (by simp +arith [totalFrame, Locals.get]) (by simp +arith [totalFrame, Locals.get])
      (by simp +arith [totalFrame, Locals.get]) rfl hlt
      (by simp [totalFrame, Locals.validIndex]) hInput hi _ _ ?_
    unfold totalSuffix
    wp_total
    constructor
    · refine ⟨rfl, index+1, input[index], Wasm.IEEE64.add (totalPrefix input index) input[index],
        0, Wasm.IEEE64.add (totalPrefix input index) input[index], ready, by omega, ?_⟩
      simp [totalFrame, UInt64.ofNat_add, totalPrefix, ArrayFold.foldPrefix_succ _ _ _ _ hi]
    · have hNextMod : (index+1)%18446744073709551616 = index+1 :=
        Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hInput.size_lt)
      simp +arith [totalMeasure, Locals.get, hNextMod, hIndexNat]
      omega

theorem total_exact (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial ptr input) :
    TerminatesWith env module 10 initial [.i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (total input)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_ (by decide)
  change wp module func10 _ initial (func10Def.toLocals [.i64 owner, .i64 ptr]) env
  unfold func10
  wp_fixed_frame [func10Def]
  simp [hInput.pointerAddress_eq, hInput.lengthRead, hInput.generatedLengthBound]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simp)]
  wp_fixed_frame [func10Def]
  change wp module ([.block 0 0 [.loop 0 0 totalBody]] ++ _) _ initial
    (totalFrame owner ptr input.size 0 0 0 0 ptr 0 0) env
  refine BlockLoop.program_spec module env initial _ totalBody
    (totalInv initial owner ptr input) (totalDone initial owner ptr input) (totalMeasure input)
    ?_ ?_ ?_ (total_step env initial owner ptr input hInput) _ _ ?_
  · rintro st frame ⟨_, index, last, result, scratch, carry, ready, _, rfl⟩
    rfl
  · rintro st frame ⟨_, last, result, scratch, carry, ready, rfl⟩
    rfl
  · refine ⟨rfl, 0, 0, 0, ptr, 0, 0, Nat.zero_le _, ?_⟩
    simp [totalPrefix, ArrayFold.foldPrefix]
  · rintro st frame ⟨rfl, last, result, scratch, carry, ready, rfl⟩
    wp_total

#print axioms total_step
#print axioms total_exact
end Project.SequenceSoftmax.Spec
