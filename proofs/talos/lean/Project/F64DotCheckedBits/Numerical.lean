import CodeLib.Attrs
import CodeLib.Numerical.Kernels

/-!
# Pure numerical contract for the runtime-length binary64 dot product

The two source arrays are represented here by logical lists of raw binary64
words.  `pairTerms` zips those views into the input expected by Talos's pure
list-shaped dot-product model.  Unequal lengths are rejected before any
modeled arithmetic; for equal lengths, including the empty case, the result is
exactly `dot64List (pairTerms left right)`.

Native floating-point evaluation is not used by this module.  The three
quantitative contracts below expose, respectively, the primitive absolute
error budget, the operation-count gamma-times-mass bound, and its conditioned
relative-error corollary.  Every domain, overflow-exclusion, underflow-
exclusion, gamma-pole, and nonzero-exact-result premise remains explicit.
-/

namespace Project.F64DotCheckedBits.Spec

/-- Proof-visible pairing of the two source-array views.  When the views have
equal length this contains every corresponding input pair. -/
def pairTerms (left right : List UInt64) : List (UInt64 × UInt64) :=
  left.zip right

/-- Status returned by the pure source model: zero for equal lengths and one
for a rejected length mismatch. -/
def dotStatusModel (left right : List UInt64) : UInt64 :=
  if left.length = right.length then 0 else 1

/-- Result word returned by the pure source model.  `dot64List` includes both
the positive-zero empty case and the seeded nonempty dot product. -/
def dotResultBitsModel (left right : List UInt64) : UInt64 :=
  if left.length = right.length then
    CodeLib.Numerical.Kernels.dot64List (pairTerms left right)
  else
    0

/-- Total two-word source behavior.  Equal-length inputs return status zero
and the pure Talos dot-product word.  A length mismatch returns status one and
positive-zero payload bits. -/
def CheckedResult (left right : List UInt64) (status bits : UInt64) : Prop :=
  (left.length = right.length ∧
      status = 0 ∧
      bits = CodeLib.Numerical.Kernels.dot64List (pairTerms left right)) ∨
    (left.length ≠ right.length ∧ status = 1 ∧ bits = 0)

/-- The modeled status and payload satisfy the total checked-result contract
for every pair of logical source-array views. -/
theorem checkedResult_model (left right : List UInt64) :
    CheckedResult left right
      (dotStatusModel left right) (dotResultBitsModel left right) := by
  by_cases hlength : left.length = right.length
  · left
    simp [dotStatusModel, dotResultBitsModel, hlength]
  · right
    simp [dotStatusModel, dotResultBitsModel, hlength]

/-- Finite-result and primitive absolute-error conclusion for an accepted
runtime-length dot product. -/
noncomputable def AbsoluteResult
    (terms : List (UInt64 × UInt64)) (bits : UInt64) : Prop :=
  CodeLib.IEEE64.Finite bits ∧
    |CodeLib.IEEE64.value bits -
        CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
      CodeLib.Numerical.Kernels.dot64ListErrorBudget terms

/-- Finite-result and operation-count gamma-times-exact-mass conclusion. -/
noncomputable def GammaResult
    (terms : List (UInt64 × UInt64)) (bits : UInt64) : Prop :=
  CodeLib.IEEE64.Finite bits ∧
    |CodeLib.IEEE64.value bits -
        CodeLib.Numerical.Kernels.dot64ExactSum terms| ≤
      CodeLib.Numerical.gamma (2 * terms.length - 1)
          CodeLib.IEEE64.unitRoundoff64 *
        CodeLib.Numerical.Kernels.dot64AbsMass terms

/-- Finite result together with the condition-number relative-error bound.
The corresponding source contract explicitly assumes a nonzero exact sum. -/
noncomputable def ConditionedResult
    (terms : List (UInt64 × UInt64)) (bits : UInt64) : Prop :=
  CodeLib.IEEE64.Finite bits ∧
    |CodeLib.IEEE64.value bits /
          CodeLib.Numerical.Kernels.dot64ExactSum terms - 1| ≤
      CodeLib.Numerical.gamma (2 * terms.length - 1)
          CodeLib.IEEE64.unitRoundoff64 *
        CodeLib.Numerical.Kernels.dot64ListConditionNumber terms

/-- Source-facing absolute-error specification.  The checked status/payload
behavior is total; the numerical conclusion applies to equal-length views
under the explicit finite-unit-input and aggregate-headroom assumptions. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.dotCheckedBits"]
noncomputable def DotCheckedBitsAbsoluteSourceSpec : Prop :=
  ∀ (left right : List UInt64),
    CheckedResult left right
        (dotStatusModel left right) (dotResultBitsModel left right) ∧
      (left.length = right.length →
        CodeLib.Numerical.Kernels.Dot64UnitInputs
            (pairTerms left right) →
        CodeLib.Numerical.Kernels.dot64AbsMass (pairTerms left right) +
              CodeLib.Numerical.Kernels.dot64ListErrorBudget
                (pairTerms left right) ≤ 1 →
        AbsoluteResult (pairTerms left right)
          (dotResultBitsModel left right))

/-- The runtime-length source model satisfies its total checked behavior and,
on accepted inputs with aggregate headroom, Talos's absolute-error theorem. -/
@[proves Project.F64DotCheckedBits.Spec.DotCheckedBitsAbsoluteSourceSpec]
theorem dotCheckedBits_source_absolute_error :
    DotCheckedBitsAbsoluteSourceSpec := by
  intro left right
  refine ⟨checkedResult_model left right, ?_⟩
  intro hlength hinputs hbudget
  have hresult :=
    CodeLib.Numerical.Kernels.dot64List_real_error_of_abs_mass
      (pairTerms left right) hinputs hbudget
  simpa [AbsoluteResult, dotResultBitsModel, hlength] using hresult

/-- Source-facing gamma-times-mass specification.  In addition to aggregate
headroom, it exposes normal-or-zero exact products and the strict gamma-pole
condition for the `2*n - 1` rounded operations. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.dotCheckedBits"]
noncomputable def DotCheckedBitsGammaSourceSpec : Prop :=
  ∀ (left right : List UInt64),
    CheckedResult left right
        (dotStatusModel left right) (dotResultBitsModel left right) ∧
      (left.length = right.length →
        CodeLib.Numerical.Kernels.Dot64UnitInputs
            (pairTerms left right) →
        CodeLib.Numerical.Kernels.dot64AbsMass (pairTerms left right) +
              CodeLib.Numerical.Kernels.dot64ListErrorBudget
                (pairTerms left right) ≤ 1 →
        CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts
            (pairTerms left right) →
        (((2 * (pairTerms left right).length - 1 : ℕ) : ℝ) *
            CodeLib.IEEE64.unitRoundoff64) < 1 →
        GammaResult (pairTerms left right)
          (dotResultBitsModel left right))

/-- The accepted source result satisfies the standard operation-count
gamma-times-exact-mass bound; mismatched lengths retain their exact rejection
behavior through `CheckedResult`. -/
@[proves Project.F64DotCheckedBits.Spec.DotCheckedBitsGammaSourceSpec]
theorem dotCheckedBits_source_gamma_error :
    DotCheckedBitsGammaSourceSpec := by
  intro left right
  refine ⟨checkedResult_model left right, ?_⟩
  intro hlength hinputs hbudget hnormalOrZero hku
  have hresult :=
    CodeLib.Numerical.Kernels.dot64List_real_gamma_error_of_abs_mass
      (pairTerms left right) hinputs hbudget hnormalOrZero hku
  simpa [GammaResult, dotResultBitsModel, hlength] using hresult

/-- Source-facing condition-number specification.  The nonzero exact sum is
explicit, as are every premise inherited from the gamma-times-mass theorem. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.dotCheckedBits"]
noncomputable def DotCheckedBitsConditionedSourceSpec : Prop :=
  ∀ (left right : List UInt64),
    CheckedResult left right
        (dotStatusModel left right) (dotResultBitsModel left right) ∧
      (left.length = right.length →
        CodeLib.Numerical.Kernels.Dot64UnitInputs
            (pairTerms left right) →
        CodeLib.Numerical.Kernels.dot64AbsMass (pairTerms left right) +
              CodeLib.Numerical.Kernels.dot64ListErrorBudget
                (pairTerms left right) ≤ 1 →
        CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts
            (pairTerms left right) →
        (((2 * (pairTerms left right).length - 1 : ℕ) : ℝ) *
            CodeLib.IEEE64.unitRoundoff64) < 1 →
        CodeLib.Numerical.Kernels.dot64ExactSum (pairTerms left right) ≠ 0 →
        ConditionedResult (pairTerms left right)
          (dotResultBitsModel left right))

/-- On the nonzero-exact-result domain, the accepted source result satisfies
the condition-number relative-error bound. -/
@[proves Project.F64DotCheckedBits.Spec.DotCheckedBitsConditionedSourceSpec]
theorem dotCheckedBits_source_conditioned_relative_error :
    DotCheckedBitsConditionedSourceSpec := by
  intro left right
  refine ⟨checkedResult_model left right, ?_⟩
  intro hlength hinputs hbudget hnormalOrZero hku hexact
  unfold ConditionedResult
  constructor
  · have hresult :=
      CodeLib.Numerical.Kernels.dot64List_real_gamma_error_of_abs_mass
        (pairTerms left right) hinputs hbudget hnormalOrZero hku
    simpa [dotResultBitsModel, hlength] using hresult.1
  · have hresult :=
      CodeLib.Numerical.Kernels.dot64List_conditioned_relative_error_of_abs_mass
        (pairTerms left right) hinputs hbudget hnormalOrZero hku hexact
    simpa [dotResultBitsModel, hlength] using hresult

#print axioms checkedResult_model
#print axioms dotCheckedBits_source_absolute_error
#print axioms dotCheckedBits_source_gamma_error
#print axioms dotCheckedBits_source_conditioned_relative_error

end Project.F64DotCheckedBits.Spec
