import Project.ProofKit.F64Bounds
import Project.ProofKit.F64Numerical
import CodeLib.Attrs

/-!
# Numerical contract for the guarded binary64 quadratic Horner entry

The executable Lean entry uses native `Float` only as a regression oracle.
This source-facing contract assigns its compiler-recognized intrinsics the
pure Talos binary64 meaning and proves the guarded finite/error result without
asserting equality with Lean's native evaluator.
-/

namespace Project.F64Horner2CheckedBits.Spec

/-- Pure proof-visible meaning of the two explicitly rounded Horner stages. -/
def horner2BitsModel (x c₂ c₁ c₀ : UInt64) : UInt64 :=
  Project.ProofKit.F64Numerical.horner2Bits x c₂ c₁ c₀

/-- Proof-side copy of the conjunction of the source entry's four raw-bit
half-unit guards. -/
def horner2Guard (x c₂ c₁ c₀ : UInt64) : Bool :=
  Project.ProofKit.F64Bounds.boundedByHalfBits x &&
    Project.ProofKit.F64Bounds.boundedByHalfBits c₂ &&
    Project.ProofKit.F64Bounds.boundedByHalfBits c₁ &&
    Project.ProofKit.F64Bounds.boundedByHalfBits c₀

/-- Status word returned by the guarded source contract. -/
def horner2StatusModel (x c₂ c₁ c₀ : UInt64) : UInt64 :=
  if horner2Guard x c₂ c₁ c₀ then 0 else 1

/-- Result-bits word returned by the guarded source contract.  Rejection
returns positive-zero bits without entering the modeled arithmetic branch. -/
def horner2ResultBitsModel (x c₂ c₁ c₀ : UInt64) : UInt64 :=
  if horner2Guard x c₂ c₁ c₀ then horner2BitsModel x c₂ c₁ c₀ else 0

/-- Finite-result and accumulated absolute-error conclusion for the accepted
quadratic. -/
noncomputable def RealErrorResult
    (x c₂ c₁ c₀ result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result -
        ((CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value c₁) * CodeLib.IEEE64.value x +
          CodeLib.IEEE64.value c₀)| ≤
      3 * CodeLib.Numerical.Kernels.f64Epsilon

/-- Total two-word behavior contract.  Success fixes both returned words and
carries the numerical theorem; rejection fixes status one and zero bits. -/
noncomputable def CheckedResult
    (x c₂ c₁ c₀ status bits : UInt64) : Prop :=
  (horner2Guard x c₂ c₁ c₀ = true ∧
      status = 0 ∧
      bits = horner2BitsModel x c₂ c₁ c₀ ∧
      RealErrorResult x c₂ c₁ c₀ bits) ∨
    (horner2Guard x c₂ c₁ c₀ = false ∧
      status = 1 ∧ bits = 0)

/-- Source-level contract associated with the LeanExe entry. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.horner2CheckedBits"]
noncomputable def Horner2CheckedBitsSourceSpec : Prop :=
  ∀ (x c₂ c₁ c₀ : UInt64),
    CheckedResult x c₂ c₁ c₀
      (horner2StatusModel x c₂ c₁ c₀)
      (horner2ResultBitsModel x c₂ c₁ c₀)

/-- The guarded source contract is total.  Accepted inputs produce a finite
pure-model result within `3 * 2^-52` of the exact quadratic; rejected inputs
produce status one and positive-zero result bits. -/
@[proves Project.F64Horner2CheckedBits.Spec.Horner2CheckedBitsSourceSpec]
theorem horner2CheckedBits_source_real_error :
    Horner2CheckedBitsSourceSpec := by
  intro x c₂ c₁ c₀
  cases hguard : horner2Guard x c₂ c₁ c₀ with
  | false =>
      right
      simp [horner2StatusModel, horner2ResultBitsModel, hguard]
  | true =>
      left
      refine ⟨hguard, by simp [horner2StatusModel, hguard],
        by simp [horner2ResultBitsModel, hguard], ?_⟩
      have hguardParts :
          (((Project.ProofKit.F64Bounds.boundedByHalfBits x &&
                Project.ProofKit.F64Bounds.boundedByHalfBits c₂) &&
              Project.ProofKit.F64Bounds.boundedByHalfBits c₁) &&
            Project.ProofKit.F64Bounds.boundedByHalfBits c₀) = true := by
        simpa only [horner2Guard] using hguard
      have hguard₃ := Bool.and_eq_true_iff.mp hguardParts
      have hguard₂ := Bool.and_eq_true_iff.mp hguard₃.1
      have hguard₁ := Bool.and_eq_true_iff.mp hguard₂.1
      have hx := Project.ProofKit.F64Bounds.boundedByHalf_spec x hguard₁.1
      have hc₂ := Project.ProofKit.F64Bounds.boundedByHalf_spec c₂ hguard₁.2
      have hc₁ := Project.ProofKit.F64Bounds.boundedByHalf_spec c₁ hguard₂.2
      have hc₀ := Project.ProofKit.F64Bounds.boundedByHalf_spec c₀ hguard₃.2
      have hnumeric :
          RealErrorResult x c₂ c₁ c₀ (horner2BitsModel x c₂ c₁ c₀) := by
        simpa [RealErrorResult, horner2BitsModel] using
          (Project.ProofKit.F64Numerical.horner2_real_error_of_half
            x c₂ c₁ c₀ hx.1 hc₂.1 hc₁.1 hc₀.1
            hx.2 hc₂.2 hc₁.2 hc₀.2)
      simpa [horner2ResultBitsModel, hguard] using hnumeric

#print axioms horner2CheckedBits_source_real_error

end Project.F64Horner2CheckedBits.Spec
