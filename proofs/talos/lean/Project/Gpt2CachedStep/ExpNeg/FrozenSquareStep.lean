import Project.Gpt2CachedStep.ExpNeg.FrozenReduceStep

namespace Project.Gpt2CachedStep.Frozen.ExpNeg
open Wasm Project.ProofKit PackedFloatFrame

def squareStepCode : Wasm.Program :=
  match (branchCode[42]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

set_option maxRecDepth 16384 in
theorem emitted_squaring : branchCode.drop 17 = (branchCode.drop 17).take 25 ++
    RangeFoldLoop.program 27 28 squareStepCode ++ branchCode.drop 43 := rfl

def Squared (input value : UInt32) (index : Nat) (frame : Locals) : Prop :=
  frame.params = [.i64 input.toUInt64] ∧
  frame.locals.length = 36 ∧
  frame.locals[18]? = some (.i64 (squarePrefix value index).toUInt64) ∧
  frame.locals[28]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem squareStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (input value : UInt32) (count index : Nat) (frame : Locals)
    (hcount : count < UInt64.size) (hindex : index < count)
    (hready : RangeFoldLoop.Ready 27 28 count index frame)
    (hacc : Squared input value index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 27 28 count (index + 1) result →
      Squared input value (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (squareStepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, hvalue, hstride⟩
  have hcounter : frame.locals[26]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[27]? = some (.i64 (UInt64.ofNat count)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hsafeInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by
    simpa only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using
      CheckedNatAdd.guard_of_fits index 1 (by omega)
  simp only [squareStepCode, branchCode, func27, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, List.dropLast, List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hlength, hvalue, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeInc)]
  wp_packed_frame [hparams, hlength, hvalue, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
  · simp only [Squared, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, squarePrefix_succ, and_self]

#print axioms squareStep_spec

end Project.Gpt2CachedStep.Frozen.ExpNeg
