import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.ExpNeg.Source
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2CachedStep.ExpNeg
open Wasm Project.ProofKit PackedFloatFrame

def branchCode : Wasm.Program :=
  match (func27[3]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ code _ _) => code
  | _ => []

def reduceStepCode : Wasm.Program :=
  match (branchCode[14]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

set_option maxRecDepth 16384 in
theorem emitted_reduction : branchCode = branchCode.take 14 ++
    RangeFoldLoop.program 27 28 reduceStepCode ++ branchCode.drop 15 := rfl

def Reduced (input : UInt32) (index : Nat) (frame : Locals) : Prop :=
  frame.params = [.i64 input.toUInt64] ∧
  frame.locals.length = 37 ∧
  frame.locals[2]? = some (.i64 (reducePrefix input index).1.toUInt64) ∧
  frame.locals[3]? = some (.i64 (UInt64.ofNat (reducePrefix input index).2)) ∧
  frame.locals[28]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem reduceStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (input : UInt32) (index : Nat) (frame : Locals)
    (hindex : index < 6) (hready : RangeFoldLoop.Ready 27 28 6 index frame)
    (hacc : Reduced input index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 27 28 6 (index + 1) result →
      Reduced input (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (reduceStepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, hvalue, hsquares, hstride⟩
  have hcounter : frame.locals[26]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[27]? = some (.i64 6) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hcount := reducePrefix_count input index
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hsquaresInc : UInt64.ofNat (reducePrefix input index).2 + 1 =
      UInt64.ofNat ((reducePrefix input index).2 + 1) := by simp
  have hsafeInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by
    simpa only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using
      CheckedNatAdd.guard_of_fits index 1 (by change index + 1 < 18446744073709551616; omega)
  have hsafeSquares : ¬ UInt64.ofNat (reducePrefix input index).2 + 1 <
      UInt64.ofNat (reducePrefix input index).2 := by
    simpa only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using
      CheckedNatAdd.guard_of_fits (reducePrefix input index).2 1
        (by change (reducePrefix input index).2 + 1 < 18446744073709551616; omega)
  have hcompare : 3212836864 < (reducePrefix input index).1.toUInt64 ↔
      3212836864 < (reducePrefix input index).1 :=
    UInt32.toUInt64_lt (a := 3212836864) (b := (reducePrefix input index).1)
  by_cases hchoice : 3212836864 < (reducePrefix input index).1
  all_goals
    simp only [reduceStepCode, branchCode, func27, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.drop, List.dropLast, List.cons_append, List.nil_append]
    repeat' first
      | wp_packed_frame [hparams, hlength, hvalue, hsquares, hcounter, hstop, hstride, hready.1,
          hcompare, hchoice, hsafeInc, hsafeSquares]
      | rw [ite_eq_left (by decide)]
      | rw [ite_eq_right (by decide)]
      | (refine wp_iff_cons rfl ?_
         first
         | rw [ite_eq_left (by decide)]
         | rw [ite_eq_right (by decide)])
    apply hnext
    · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
      rfl
    · simp only [Reduced, hlength, List.length_set, List.getElem?_set,
        Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, reducePrefix_succ,
        reduceStep, hchoice, hsquaresInc, Project.ProofKit.F32Mul.mul_eq, true_and, and_true] <;> rfl

#print axioms reduceStep_spec

end Project.Gpt2CachedStep.ExpNeg
