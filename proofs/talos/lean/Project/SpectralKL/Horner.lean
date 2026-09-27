import Project.ProofKit.F64Horner

namespace Project.SpectralKL
open CodeLib.IEEE64 Project.ProofKit.F64Horner Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

def hornerBits (d : UInt64) : List UInt64 → UInt64
  | [] => 0
  | c :: cs => Wasm.IEEE64.add (Wasm.IEEE64.mul (hornerBits d cs) d) c

noncomputable def hornerReal (d : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: cs => hornerReal d cs*d+c

/-- On the half-unit interval, Horner errors contract at each step. The bound
is independent of the polynomial length; each coefficient is at most 1/2. -/
theorem horner_step {a d c : UInt64} {p q : ℝ}
    (ha : Approximation a p 2 (8*arithmeticEpsilon))
    (hc : Approximation c q (1/2) arithmeticEpsilon)
    (hd : Finite d) (bd : |value d| ≤ 1/2) :
    Approximation (Wasm.IEEE64.add (Wasm.IEEE64.mul a d) c)
      (p*value d+q) 2 (8*arithmeticEpsilon) := by
  have heps : 0 ≤ arithmeticEpsilon ∧ arithmeticEpsilon ≤ 1/100 := by
    norm_num [arithmeticEpsilon]
  have bprod : |value a*value d| ≤ 1 := by
    rw [abs_mul]
    nlinarith [ha.magnitude, abs_nonneg (value a), abs_nonneg (value d)]
  obtain ⟨hf, he⟩ := mul_error a d ha.finite hd 1 (by norm_num) (by norm_num) bprod
  have bm := magnitude_of_error _ _ _ _ he bprod
  have bsum : |value (Wasm.IEEE64.mul a d)+value c| ≤ 2 := by
    have h := abs_add_le (value (Wasm.IEEE64.mul a d)) (value c)
    linarith [hc.magnitude]
  obtain ⟨hg, eg⟩ := add_error _ c hf hc.finite 2 (by norm_num) (by norm_num) bsum
  have localError :
      |value (Wasm.IEEE64.add (Wasm.IEEE64.mul a d) c) - (value a*value d+value c)| ≤
        3*arithmeticEpsilon := by
    have h := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a d) c)-(value (Wasm.IEEE64.mul a d)+value c))
      (value (Wasm.IEEE64.mul a d)-value a*value d)
    ring_nf at h he eg ⊢
    linarith
  refine ⟨hg, ?_, ?_⟩
  · have h := magnitude_of_error _ _ _ _ localError
      ((abs_add_le _ _).trans (add_le_add bprod hc.magnitude))
    linarith
  · have ep : |(value a-p)*value d| ≤ 4*arithmeticEpsilon := by
      rw [abs_mul]
      nlinarith [ha.accuracy, abs_nonneg (value a-p), abs_nonneg (value d)]
    have h₁ := abs_add_le ((value a-p)*value d) (value c-q)
    have h₂ := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a d) c)-(value a*value d+value c))
      ((value a-p)*value d+(value c-q))
    ring_nf at h₁ h₂ localError ep ⊢
    linarith [hc.accuracy]

theorem horner_error (cs : List (UInt64 × ℝ)) (d : UInt64)
    (hc : ∀ c ∈ cs, Approximation c.1 c.2 (1/2) arithmeticEpsilon)
    (hd : Finite d) (bd : |value d| ≤ 1/2) :
    Approximation (hornerBits d (cs.map Prod.fst))
      (hornerReal (value d) (cs.map Prod.snd)) 2 (8*arithmeticEpsilon) := by
  induction cs with
  | nil =>
    simp only [List.map_nil, hornerBits, hornerReal]
    constructor
    · unfold CodeLib.IEEE64.Finite; decide
    all_goals norm_num [hornerBits, hornerReal, value, Wasm.IEEE64.scaledValue,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign, Wasm.IEEE64.exponent,
      Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]
  | cons c cs ih =>
    exact horner_step (ih (fun a h => hc a (List.mem_cons_of_mem _ h)))
      (hc c (List.mem_cons_self ..)) hd bd

#print axioms horner_error
end Project.SpectralKL
