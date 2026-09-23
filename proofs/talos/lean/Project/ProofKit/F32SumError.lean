import Project.ProofKit.F32AdditionBounds
import Project.ProofKit.F32Add

namespace Project.ProofKit.F32SumError
open CodeLib.IEEE32

def sumPrefix (input : Nat → UInt32) (count : Nat) : UInt32 :=
  (List.range count).foldl (fun total i => LeanExe.Float32.addBits total (input i)) 0

theorem sumPrefix_succ (input : Nat → UInt32) (count : Nat) :
    sumPrefix input (count + 1) = LeanExe.Float32.addBits (sumPrefix input count) (input count) := by
  simp only [sumPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ordered_error (input : Nat → UInt32) (reference inputError : Nat → ℝ)
    (bounds : Nat → Nat) (count : Nat)
    (hFinite : ∀ i < count, Finite (input i))
    (hError : ∀ i < count, |value (input i) - reference i| ≤ inputError i)
    (hBound : ∀ i < count, bounds i ≤ 276)
    (hRange : ∀ i < count,
      (Wasm.IEEE32.scaledValue (sumPrefix input i) + Wasm.IEEE32.scaledValue (input i)).natAbs < 2 ^ bounds i) :
    Finite (sumPrefix input count) ∧
      |value (sumPrefix input count) - ∑ i ∈ Finset.range count, reference i| ≤
        ∑ i ∈ Finset.range count, (inputError i + F32AdditionBounds.epsilon (bounds i)) := by
  induction count with
  | zero =>
    norm_num [sumPrefix, CodeLib.IEEE32.Finite, Wasm.IEEE32.isFinite, Wasm.IEEE32.exponent, value,
      Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude, Wasm.IEEE32.fraction]
  | succ count ih =>
    have hPrevious := ih (fun i hi => hFinite i (by omega)) (fun i hi => hError i (by omega))
      (fun i hi => hBound i (by omega)) (fun i hi => hRange i (by omega))
    have hAdd := F32AdditionBounds.add_real_error (sumPrefix input count) (input count) (bounds count)
      (hBound count (by omega)) hPrevious.1 (hFinite count (by omega)) (hRange count (by omega))
    rw [← F32Add.add_eq] at hAdd
    rw [sumPrefix_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    refine ⟨hAdd.1, ?_⟩
    have hOperands : |(value (sumPrefix input count) + value (input count)) -
        ((∑ i ∈ Finset.range count, reference i) + reference count)| ≤
        (∑ i ∈ Finset.range count, (inputError i + F32AdditionBounds.epsilon (bounds i))) + inputError count := by
      rw [add_sub_add_comm]
      exact (abs_add_le _ _).trans (add_le_add hPrevious.2 (hError count (by omega)))
    exact (abs_sub_le _ _ _).trans ((add_le_add hAdd.2 hOperands).trans_eq (by ring))

#print axioms ordered_error
end Project.ProofKit.F32SumError
