import Project.F64DotCheckedBits.Execution

/-!
# Runtime-length binary64 dot-product artifact

This public proof root combines exact, fuel-independent execution of the
compiler-generated WAT with the source-level Talos bounds.  Each numerical
contract keeps its accepted-input assumptions explicit and concludes both the
total checked-result behavior and the corresponding finite/error theorem.
-/

namespace Project.F64DotCheckedBits.Spec

open Wasm

/-- WAT-level primitive absolute-error specification. -/
noncomputable def AbsoluteErrorSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64),
    Project.ProofKit.UInt64Array.At initial leftPtr left →
    Project.ProofKit.UInt64Array.At initial rightPtr right →
    left.size = right.size →
    CodeLib.Numerical.Kernels.Dot64UnitInputs
      (pairTerms left.toList right.toList) →
    CodeLib.Numerical.Kernels.dot64AbsMass
          (pairTerms left.toList right.toList) +
        CodeLib.Numerical.Kernels.dot64ListErrorBudget
          (pairTerms left.toList right.toList) ≤ 1 →
    TerminatesWith env module_ 0 initial [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (dotResultBitsModel left.toList right.toList),
             .i64 (dotStatusModel left.toList right.toList)] ∧
          CheckedResult left.toList right.toList
            (dotStatusModel left.toList right.toList)
            (dotResultBitsModel left.toList right.toList) ∧
          AbsoluteResult (pairTerms left.toList right.toList)
            (dotResultBitsModel left.toList right.toList))

/-- Exact generated-WAT execution carries the source primitive absolute-error
bound for every accepted pair of logical arrays. -/
theorem dotCheckedBits_wat_absolute_error :
    AbsoluteErrorSpecFor Project.F64DotCheckedBits.«module» := by
  intro env initial leftPtr rightPtr left right
    hLeft hRight hLength hInputs hBudget
  have hLengthList : left.toList.length = right.toList.length := by
    simpa using hLength
  have hSource :=
    dotCheckedBits_source_absolute_error left.toList right.toList
  refine TerminatesWith.mono
    (dotCheckedBits_exact env initial leftPtr rightPtr left right
      hLeft hRight) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, hSource.1,
    hSource.2 hLengthList hInputs hBudget⟩

/-- WAT-level operation-count gamma-times-mass specification. -/
noncomputable def GammaErrorSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64),
    Project.ProofKit.UInt64Array.At initial leftPtr left →
    Project.ProofKit.UInt64Array.At initial rightPtr right →
    left.size = right.size →
    CodeLib.Numerical.Kernels.Dot64UnitInputs
      (pairTerms left.toList right.toList) →
    CodeLib.Numerical.Kernels.dot64AbsMass
          (pairTerms left.toList right.toList) +
        CodeLib.Numerical.Kernels.dot64ListErrorBudget
          (pairTerms left.toList right.toList) ≤ 1 →
    CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts
      (pairTerms left.toList right.toList) →
    (((2 * (pairTerms left.toList right.toList).length - 1 : Nat) : ℝ) *
        CodeLib.IEEE64.unitRoundoff64) < 1 →
    TerminatesWith env module_ 0 initial [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (dotResultBitsModel left.toList right.toList),
             .i64 (dotStatusModel left.toList right.toList)] ∧
          CheckedResult left.toList right.toList
            (dotStatusModel left.toList right.toList)
            (dotResultBitsModel left.toList right.toList) ∧
          GammaResult (pairTerms left.toList right.toList)
            (dotResultBitsModel left.toList right.toList))

/-- Exact generated-WAT execution carries the source gamma-times-mass bound
for every accepted pair satisfying the normal-product and gamma premises. -/
theorem dotCheckedBits_wat_gamma_error :
    GammaErrorSpecFor Project.F64DotCheckedBits.«module» := by
  intro env initial leftPtr rightPtr left right
    hLeft hRight hLength hInputs hBudget hNormalOrZero hGamma
  have hLengthList : left.toList.length = right.toList.length := by
    simpa using hLength
  have hSource :=
    dotCheckedBits_source_gamma_error left.toList right.toList
  refine TerminatesWith.mono
    (dotCheckedBits_exact env initial leftPtr rightPtr left right
      hLeft hRight) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, hSource.1,
    hSource.2 hLengthList hInputs hBudget hNormalOrZero hGamma⟩

/-- WAT-level condition-number relative-error specification. -/
noncomputable def ConditionedRelativeErrorSpecFor
    (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (leftPtr rightPtr : UInt64) (left right : Array UInt64),
    Project.ProofKit.UInt64Array.At initial leftPtr left →
    Project.ProofKit.UInt64Array.At initial rightPtr right →
    left.size = right.size →
    CodeLib.Numerical.Kernels.Dot64UnitInputs
      (pairTerms left.toList right.toList) →
    CodeLib.Numerical.Kernels.dot64AbsMass
          (pairTerms left.toList right.toList) +
        CodeLib.Numerical.Kernels.dot64ListErrorBudget
          (pairTerms left.toList right.toList) ≤ 1 →
    CodeLib.Numerical.Kernels.Dot64NormalOrZeroProducts
      (pairTerms left.toList right.toList) →
    (((2 * (pairTerms left.toList right.toList).length - 1 : Nat) : ℝ) *
        CodeLib.IEEE64.unitRoundoff64) < 1 →
    CodeLib.Numerical.Kernels.dot64ExactSum
      (pairTerms left.toList right.toList) ≠ 0 →
    TerminatesWith env module_ 0 initial [.i64 rightPtr, .i64 leftPtr]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (dotResultBitsModel left.toList right.toList),
             .i64 (dotStatusModel left.toList right.toList)] ∧
          CheckedResult left.toList right.toList
            (dotStatusModel left.toList right.toList)
            (dotResultBitsModel left.toList right.toList) ∧
          ConditionedResult (pairTerms left.toList right.toList)
            (dotResultBitsModel left.toList right.toList))

/-- Exact generated-WAT execution carries the source condition-number bound
when the exact dot product is nonzero. -/
theorem dotCheckedBits_wat_conditioned_relative_error :
    ConditionedRelativeErrorSpecFor
      Project.F64DotCheckedBits.«module» := by
  intro env initial leftPtr rightPtr left right
    hLeft hRight hLength hInputs hBudget hNormalOrZero hGamma hExact
  have hLengthList : left.toList.length = right.toList.length := by
    simpa using hLength
  have hSource :=
    dotCheckedBits_source_conditioned_relative_error
      left.toList right.toList
  refine TerminatesWith.mono
    (dotCheckedBits_exact env initial leftPtr rightPtr left right
      hLeft hRight) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, hSource.1,
    hSource.2 hLengthList hInputs hBudget hNormalOrZero hGamma hExact⟩

#print axioms dotCheckedBits_wat_absolute_error
#print axioms dotCheckedBits_wat_gamma_error
#print axioms dotCheckedBits_wat_conditioned_relative_error

end Project.F64DotCheckedBits.Spec
