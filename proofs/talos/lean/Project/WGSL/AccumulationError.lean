import Project.WGSL.FusedError

namespace Project.WGSL.Binary32

open LeanExe.WGSL CodeLib.IEEE32

theorem epsilon_pos : 0 < arithmeticEpsilon := by norm_num [arithmeticEpsilon]

private theorem magnitude_of_error {x target error : ℝ} (h : |x - target| ≤ error) :
    |x| ≤ |target| + error := by
  have ht := abs_add_le (x - target) target
  have heq : x - target + target = x := by ring
  rw [heq] at ht
  linarith

/-- A single loop update covers both permitted evaluation choices. The domain
ensures separate multiplication also stays within the addition lemma's range. -/
theorem accumulation_error {p : Profile} {acc a b result : UInt32}
    (hc : Finite acc) (ha : Finite a) (hb : Finite b)
    (hcBound : |value acc| ≤ 1) (haBound : |value a| ≤ 1) (hbBound : |value b| ≤ 1)
    (productBound : |value a * value b| + arithmeticEpsilon ≤ 1)
    (update : Accumulate semantics p acc a b result) :
    Finite result ∧
      |value result - (value acc + value a * value b)| ≤ 2 * arithmeticEpsilon := by
  cases update with
  | @separate product result cm ca _ _ _ mul add =>
      have hm : product = Wasm.IEEE32.mul a b := mul.2
      have ha' : result = Wasm.IEEE32.add acc product := add.2
      subst product; subst result
      have mulError := mul_real_error a b ha hb haBound hbBound
      change _ ∧ _ ≤ arithmeticEpsilon at mulError
      have mulBound : |value (Wasm.IEEE32.mul a b)| ≤ 1 :=
        (magnitude_of_error mulError.2).trans productBound
      have addError := add_real_error acc (Wasm.IEEE32.mul a b) hc mulError.1 hcBound mulBound
      refine ⟨addError.1, ?_⟩
      calc
        _ = |(value (Wasm.IEEE32.add acc (Wasm.IEEE32.mul a b)) -
              (value acc + value (Wasm.IEEE32.mul a b))) +
            (value (Wasm.IEEE32.mul a b) - value a * value b)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 2 * arithmeticEpsilon := by linarith [addError.2, mulError.2]
  | fused _ _ op =>
      have equal : result = fma a b acc := op.2
      subst result
      have h := fma_real_error a b acc ha hb hc haBound hbBound hcBound
      refine ⟨h.1, ?_⟩
      have he := epsilon_pos
      rw [add_comm (value acc)]
      linarith [h.2]

noncomputable def realDot (config : GemmConfig) (a b : WordBuffer) (row col : Nat) : Nat → ℝ
  | 0 => 0
  | k + 1 => realDot config a b row col k +
      value (a (row * config.inner + k)) * value (b (k * config.cols + col))

/-- Explicit finite input domain. `productBudget` bounds each exact product,
and the cumulative budget leaves room for two rounding errors per iteration. -/
structure DotDomain (config : GemmConfig) (a b : WordBuffer) (row col : Nat)
    (productBudget : ℝ) : Prop where
  nonnegative : 0 ≤ productBudget
  product_small : productBudget + arithmeticEpsilon ≤ 1
  accumulation_small : config.inner * (productBudget + 2 * arithmeticEpsilon) ≤ 1
  inputs : ∀ k, k < config.inner →
    Finite (a (row * config.inner + k)) ∧ Finite (b (k * config.cols + col)) ∧
    |value (a (row * config.inner + k))| ≤ 1 ∧ |value (b (k * config.cols + col))| ≤ 1 ∧
    |value (a (row * config.inner + k)) * value (b (k * config.cols + col))| ≤ productBudget

theorem dot_error {p config a b row col budget k result}
    (domain : DotDomain config a b row col budget)
    (run : Dot semantics p config a b row col k result) (hk : k ≤ config.inner) :
    Finite result ∧ |value result| ≤ k * (budget + 2 * arithmeticEpsilon) ∧
      |value result - realDot config a b row col k| ≤ 2 * k * arithmeticEpsilon := by
  induction run with
  | zero =>
      have hz : Finite (0 : UInt32) ∧ value (0 : UInt32) = 0 := by
        constructor
        · unfold CodeLib.IEEE32.Finite; decide +kernel
        · norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
            Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
      simp only [hz.1, hz.2, realDot, Nat.cast_zero, zero_mul, sub_self, abs_zero,
        mul_zero, le_refl, and_self]
  | @next k acc result previous update ih =>
      have hk' : k < config.inner := by omega
      have prev := ih (by omega)
      have entries := domain.inputs k hk'
      have nonneg : 0 ≤ budget + 2 * arithmeticEpsilon := by linarith [domain.nonnegative, epsilon_pos]
      have accBound : |value acc| ≤ 1 := by
        calc
          _ ≤ k * (budget + 2 * arithmeticEpsilon) := prev.2.1
          _ ≤ config.inner * (budget + 2 * arithmeticEpsilon) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hk') nonneg
          _ ≤ 1 := domain.accumulation_small
      have step := accumulation_error prev.1 entries.1 entries.2.1 accBound entries.2.2.1
        entries.2.2.2.1 (by linarith [entries.2.2.2.2, domain.product_small]) update
      refine ⟨step.1, ?_, ?_⟩
      · have mag := magnitude_of_error step.2
        have triangle := abs_add_le (value acc)
          (value (a (row * config.inner + k)) * value (b (k * config.cols + col)))
        push_cast
        nlinarith [prev.2.1, entries.2.2.2.2]
      · calc
          _ = |(value result - (value acc + value (a (row * config.inner + k)) *
                value (b (k * config.cols + col)))) +
              (value acc - realDot config a b row col k)| := by rw [realDot]; congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ 2 * (k + 1 : Nat) * arithmeticEpsilon := by
            push_cast
            nlinarith [step.2, prev.2.2]

#print axioms accumulation_error
#print axioms dot_error

end Project.WGSL.Binary32
