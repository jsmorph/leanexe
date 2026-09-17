import Project.WGSL.WideScalarError
import Project.WGSL.AccumulationError

namespace Project.WGSL.Binary32
open LeanExe.WGSL CodeLib.IEEE32 Project.ProofKit

/-- Finite products and sufficient room for all intermediate rounded sums.
Unlike DotDomain, operands and intermediate sums need not be below one. -/
structure WideDotDomain (config : GemmConfig) (a b : WordBuffer) (row col : Nat)
    (accBudget productBudget : ℝ) : Prop where
  acc_nonnegative : 0 ≤ accBudget
  product_nonnegative : 0 ≤ productBudget
  finite_range : accBudget + productBudget + F32AddBounds.unitRoundoff * productBudget +
    F32MulBounds.multiplicationUnderflowEpsilon < (2:ℝ)^127
  accumulation_bound : config.inner * (productBudget + stepError accBudget productBudget) ≤ accBudget
  inputs : ∀ k, k < config.inner →
    Finite (a (row * config.inner + k)) ∧ Finite (b (k * config.cols + col)) ∧
    |value (a (row * config.inner + k)) * value (b (k * config.cols + col))| ≤ productBudget

theorem dot_error_wide {p config a b row col cBudget pBudget k result}
    (domain : WideDotDomain config a b row col cBudget pBudget)
    (run : Dot semantics p config a b row col k result) (hk : k ≤ config.inner) :
    Finite result ∧ |value result| ≤ k * (pBudget + stepError cBudget pBudget) ∧
      |value result - realDot config a b row col k| ≤ k * stepError cBudget pBudget := by
  induction run with
  | zero =>
      have hz : Finite (0:UInt32) ∧ value (0:UInt32) = 0 := signed_zero_value false
      simp only [hz.1, hz.2, realDot, Nat.cast_zero, zero_mul, sub_self, abs_zero,
        le_refl, and_self]
  | @next k acc result previous update ih =>
      have hk' : k < config.inner := by omega
      have prev := ih (by omega)
      have entries := domain.inputs k hk'
      have he0 := stepError_nonneg domain.acc_nonnegative domain.product_nonnegative
      have hsum0 := add_nonneg domain.product_nonnegative he0
      have accBound : |value acc| ≤ cBudget := by
        calc
          _ ≤ k * (pBudget + stepError cBudget pBudget) := prev.2.1
          _ ≤ config.inner * (pBudget + stepError cBudget pBudget) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hk') hsum0
          _ ≤ cBudget := domain.accumulation_bound
      have step := accumulation_error_wide prev.1 entries.1 entries.2.1
        domain.acc_nonnegative domain.product_nonnegative accBound entries.2.2 domain.finite_range update
      refine ⟨step.1, ?_, ?_⟩
      · have ht := abs_sub_le (value result)
          (value acc + value (a (row * config.inner + k)) * value (b (k * config.cols + col))) 0
        simp only [sub_zero] at ht
        have hsum := abs_add_le (value acc)
          (value (a (row * config.inner + k)) * value (b (k * config.cols + col)))
        push_cast
        nlinarith [prev.2.1, entries.2.2, step.2]
      · calc
          _ = |(value result - (value acc + value (a (row * config.inner + k)) *
                value (b (k * config.cols + col)))) +
              (value acc - realDot config a b row col k)| := by rw [realDot]; congr 1; ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ (k + 1 : Nat) * stepError cBudget pBudget := by
            push_cast
            nlinarith [step.2, prev.2.2]

#print axioms dot_error_wide
end Project.WGSL.Binary32
