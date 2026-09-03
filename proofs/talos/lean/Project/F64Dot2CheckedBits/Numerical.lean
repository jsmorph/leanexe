import Project.F64Dot2CheckedBits.Bounds
import CodeLib.Attrs
import CodeLib.Attrs

/-!
# Numerical contract for the guarded binary64 dot product

The Lean entry uses native `Float` only as an executable regression oracle.
The source-facing proof contract below gives its compiler-recognized floating
intrinsics the pure Talos binary64 meaning.  It does not assert an equality
between Lean's native floating-point evaluator and that model.
-/

namespace Project.F64Dot2CheckedBits.Spec

open Wasm

/-- Pure proof-visible meaning of the two multiplication operations followed
by the final addition. -/
def dot2BitsModel (a₀ b₀ a₁ b₁ : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul a₀ b₀) (Wasm.IEEE64.mul a₁ b₁)

/-- Proof-side copy of the conjunction of the four raw-bit guards in the Lean
entry point. -/
def dot2Guard (a₀ b₀ a₁ b₁ : UInt64) : Bool :=
  Bounds.boundedByHalfBits a₀ && Bounds.boundedByHalfBits b₀ &&
    Bounds.boundedByHalfBits a₁ && Bounds.boundedByHalfBits b₁

/-- Status word returned by the guarded source contract: zero on success and
one on rejection. -/
def dot2StatusModel (a₀ b₀ a₁ b₁ : UInt64) : UInt64 :=
  if dot2Guard a₀ b₀ a₁ b₁ then 0 else 1

/-- Result-bits word returned by the guarded source contract.  A rejected
input returns positive-zero bits without performing modeled arithmetic. -/
def dot2ResultBitsModel (a₀ b₀ a₁ b₁ : UInt64) : UInt64 :=
  if dot2Guard a₀ b₀ a₁ b₁ then dot2BitsModel a₀ b₀ a₁ b₁ else 0

/-- Finite-result and accumulated absolute-error conclusion for the accepted
two-term dot product. -/
noncomputable def RealErrorResult
    (a₀ b₀ a₁ b₁ result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result -
        (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
          CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
      3 * CodeLib.Numerical.Kernels.f64Epsilon

/-- Total two-word behavior contract.  The success branch fixes both returned
words and carries the numerical theorem; the rejection branch fixes status one
and zero result bits. -/
noncomputable def CheckedResult
    (a₀ b₀ a₁ b₁ status bits : UInt64) : Prop :=
  (dot2Guard a₀ b₀ a₁ b₁ = true ∧
      status = 0 ∧
      bits = dot2BitsModel a₀ b₀ a₁ b₁ ∧
      RealErrorResult a₀ b₀ a₁ b₁ bits) ∨
    (dot2Guard a₀ b₀ a₁ b₁ = false ∧
      status = 1 ∧ bits = 0)

/-- Source-level contract associated with the LeanExe entry.  The association
is specification metadata; its trusted arithmetic meaning is `dot2BitsModel`,
not evaluation through native `Float`. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.dot2CheckedBits"]
noncomputable def Dot2CheckedBitsSourceSpec : Prop :=
  ∀ (a₀ b₀ a₁ b₁ : UInt64),
    CheckedResult a₀ b₀ a₁ b₁
      (dot2StatusModel a₀ b₀ a₁ b₁)
      (dot2ResultBitsModel a₀ b₀ a₁ b₁)

/-- The guarded compiler contract is total.  Accepted inputs produce the pure
modeled dot product, which is finite and has accumulated absolute error at
most `3 * 2^-52`; rejected inputs produce status one and zero bits. -/
@[proves Project.F64Dot2CheckedBits.Spec.Dot2CheckedBitsSourceSpec]
theorem dot2CheckedBits_source_real_error : Dot2CheckedBitsSourceSpec := by
  intro a₀ b₀ a₁ b₁
  cases hguard : dot2Guard a₀ b₀ a₁ b₁ with
  | false =>
      right
      simp [dot2StatusModel, dot2ResultBitsModel, hguard]
  | true =>
      left
      refine ⟨hguard, by simp [dot2StatusModel, hguard],
        by simp [dot2ResultBitsModel, hguard], ?_⟩
      have hguardParts :
          (((Bounds.boundedByHalfBits a₀ && Bounds.boundedByHalfBits b₀) &&
              Bounds.boundedByHalfBits a₁) &&
            Bounds.boundedByHalfBits b₁) = true := by
        simpa only [dot2Guard] using hguard
      have hguard₃ := Bool.and_eq_true_iff.mp hguardParts
      have hguard₂ := Bool.and_eq_true_iff.mp hguard₃.1
      have hguard₁ := Bool.and_eq_true_iff.mp hguard₂.1
      have ha₀ := Bounds.boundedByHalf_spec a₀ hguard₁.1
      have hb₀ := Bounds.boundedByHalf_spec b₀ hguard₁.2
      have ha₁ := Bounds.boundedByHalf_spec a₁ hguard₂.2
      have hb₁ := Bounds.boundedByHalf_spec b₁ hguard₃.2
      let terms : List (UInt64 × UInt64) := [(a₀, b₀), (a₁, b₁)]
      have hinputs : CodeLib.Numerical.Kernels.Dot64UniformInputs
          ((1 : ℝ) / 2) ((1 : ℝ) / 2) terms := by
        intro term hterm
        have hcases : term = (a₀, b₀) ∨ term = (a₁, b₁) := by
          simpa [terms] using hterm
        rcases hcases with rfl | rfl
        · exact ⟨ha₀.1, hb₀.1, ha₀.2, hb₀.2⟩
        · exact ⟨ha₁.1, hb₁.1, ha₁.2, hb₁.2⟩
      have hbudget :
          (terms.length : ℝ) * (((1 : ℝ) / 2) * ((1 : ℝ) / 2)) +
              CodeLib.Numerical.Kernels.dot64ListErrorBudget terms ≤ 1 := by
        norm_num [terms, CodeLib.Numerical.Kernels.dot64ListErrorBudget,
          CodeLib.Numerical.Kernels.f64Epsilon]
      have hresult :=
        CodeLib.Numerical.Kernels.dot64List_real_error_of_uniform
          ((1 : ℝ) / 2) ((1 : ℝ) / 2) terms
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hinputs hbudget
      have hnumeric :
          RealErrorResult a₀ b₀ a₁ b₁ (dot2BitsModel a₀ b₀ a₁ b₁) := by
        unfold RealErrorResult
        constructor
        · simpa [terms, dot2BitsModel,
            CodeLib.Numerical.Kernels.dot64List,
            CodeLib.Numerical.Kernels.dot64,
            CodeLib.Numerical.Kernels.dot64Acc] using hresult.1
        · have herror := hresult.2
          have herror' :
              |CodeLib.IEEE64.value (dot2BitsModel a₀ b₀ a₁ b₁) -
                  (CodeLib.IEEE64.value a₀ * CodeLib.IEEE64.value b₀ +
                    CodeLib.IEEE64.value a₁ * CodeLib.IEEE64.value b₁)| ≤
                ((2 : ℝ) + 1) * CodeLib.Numerical.Kernels.f64Epsilon := by
            simpa [terms, dot2BitsModel,
              CodeLib.Numerical.Kernels.dot64List,
              CodeLib.Numerical.Kernels.dot64,
              CodeLib.Numerical.Kernels.dot64Acc,
              CodeLib.Numerical.Kernels.dot64ExactSum,
              CodeLib.Numerical.Kernels.dot64ListErrorBudget] using herror
          calc
            _ ≤ ((2 : ℝ) + 1) * CodeLib.Numerical.Kernels.f64Epsilon :=
              herror'
            _ = 3 * CodeLib.Numerical.Kernels.f64Epsilon := by ring
      simpa [dot2ResultBitsModel, hguard] using hnumeric

#print axioms dot2CheckedBits_source_real_error

end Project.F64Dot2CheckedBits.Spec
