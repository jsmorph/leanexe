import LeanExe.Models.Gpt2.Numerics
import Project.ProofKit.F32Mul

namespace Project.Gpt2CachedStep.ExpNeg
open LeanExe.Models.Gpt2

def reduceStep (state : UInt32 × Nat) : UInt32 × Nat :=
  if state.1 > 0xBF800000 then (LeanExe.Float32.mulBits state.1 0x3F000000, state.2 + 1)
  else state

def reducePrefix (input : UInt32) (count : Nat) : UInt32 × Nat :=
  (List.range count).foldl (fun state _ => reduceStep state) (input, 0)

@[simp] theorem reducePrefix_zero (input : UInt32) : reducePrefix input 0 = (input, 0) := rfl

theorem reducePrefix_succ (input : UInt32) (count : Nat) :
    reducePrefix input (count + 1) = reduceStep (reducePrefix input count) := by
  simp only [reducePrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem reducePrefix_count (input : UInt32) (count : Nat) : (reducePrefix input count).2 ≤ count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [reducePrefix_succ]
    unfold reduceStep
    split <;> omega

def squarePrefix (input : UInt32) (count : Nat) : UInt32 :=
  (List.range count).foldl (fun value _ => LeanExe.Float32.mulBits value value) input

@[simp] theorem squarePrefix_zero (input : UInt32) : squarePrefix input 0 = input := rfl

theorem squarePrefix_succ (input : UInt32) (count : Nat) :
    squarePrefix input (count + 1) =
      Wasm.IEEE32.mul (squarePrefix input count) (squarePrefix input count) := by
  simp only [squarePrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Mul.mul_eq]

theorem expNeg_eq (input : UInt32) :
    expNeg input = if input > 0xC2800000 then 0 else
      squarePrefix (expPolynomial (reducePrefix input 6).1) (reducePrefix input 6).2 := by
  have step (state : UInt32 × Nat) :
      (if state.1 > 0xBF800000 then
        pure (ForInStep.yield (LeanExe.Float32.mulBits state.1 0x3F000000, state.2 + 1))
      else pure (ForInStep.yield state) : Id (ForInStep (UInt32 × Nat))) =
      pure (ForInStep.yield (reduceStep state)) := by
    unfold reduceStep
    split <;> rfl
  simp only [expNeg, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', Nat.sub_zero, Nat.add_sub_cancel_right, Nat.div_one,
    step, List.forIn_pure_yield_eq_foldl]
  split
  · rfl
  · rfl

#print axioms expNeg_eq
#print axioms reducePrefix_count

end Project.Gpt2CachedStep.ExpNeg
