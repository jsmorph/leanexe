import Project.ProofKit.F32UniformRange

namespace Project.ProofKit.F32UniformRange

theorem dotFits_sound (x w : Nat → UInt32) (count inputMagnitude weightMagnitude mulBound addBound : Nat)
    (h : dotFits count inputMagnitude weightMagnitude mulBound addBound = true)
    (hx : ∀ i < count, CodeLib.IEEE32.Finite (x i))
    (hw : ∀ i < count, CodeLib.IEEE32.Finite (w i))
    (hX : ∀ i < count, Wasm.IEEE32.scaledMagnitude (x i) ≤ inputMagnitude)
    (hW : ∀ i < count, Wasm.IEEE32.scaledMagnitude (w i) ≤ weightMagnitude) :
    F32DotError.Ranges x w count ⟨fun _ => mulBound, fun _ => addBound⟩ := by
  simp only [dotFits, sumFits, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  exact dot_ranges x w count mulBound addBound h.1 h.2.1 h.2.2.2.1 hx hw
    (fun i hi => (Nat.mul_le_mul (hX i hi) (hW i hi)).trans_lt h.2.2.1) h.2.2.2.2

theorem sumFits_sound (input : Nat → UInt32) (count magnitude bound : Nat)
    (h : sumFits count magnitude bound = true)
    (hf : ∀ i < count, CodeLib.IEEE32.Finite (input i))
    (hm : ∀ i < count, (Wasm.IEEE32.scaledValue (input i)).natAbs ≤ magnitude) :
    (∀ i < count, (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input i) +
      Wasm.IEEE32.scaledValue (input i)).natAbs < 2 ^ bound) ∧
    CodeLib.IEEE32.Finite (F32SumError.sumPrefix input count) ∧
      (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count)).natAbs ≤
        count * (magnitude + 2 ^ (bound - 25)) := by
  simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨sum_ranges input count bound magnitude h.1 hf hm h.2,
    sum_prefix input count bound magnitude h.1 hf hm h.2⟩

#print axioms dotFits_sound
#print axioms sumFits_sound
end Project.ProofKit.F32UniformRange
