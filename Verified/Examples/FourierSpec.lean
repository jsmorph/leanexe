import Verified.Examples.Fourier
import CodeLib.IEEE64.Roundoff
import CodeLib.IEEE64.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Verified.Examples.FourierSpec

open CodeLib.IEEE64
open scoped BigOperators

noncomputable def phase (n m : Nat) : ℝ :=
  2 * Real.pi * (m : ℝ) / (n : ℝ)

noncomputable def realDFT (xs : Array Float) (k : Nat) : ℝ :=
  let n := xs.size / 2
  ∑ j ∈ Finset.range n,
    (value xs[2 * j]!.toBits * Real.cos (phase n (j * k)) +
      value xs[2 * j + 1]!.toBits * Real.sin (phase n (j * k)))

noncomputable def imagDFT (xs : Array Float) (k : Nat) : ℝ :=
  let n := xs.size / 2
  ∑ j ∈ Finset.range n,
    (value xs[2 * j + 1]!.toBits * Real.cos (phase n (j * k)) -
      value xs[2 * j]!.toBits * Real.sin (phase n (j * k)))

noncomputable def inputNorm (xs : Array Float) : ℝ :=
  ∑ j ∈ Finset.range (xs.size / 2),
    (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)

noncomputable def growth (n : Nat) : ℝ :=
  (1 + unitRoundoff64) ^ (n + 2) * (1 + 32 * unitRoundoff64)

noncomputable def underflow (n : Nat) : ℝ :=
  2 * (n : ℝ) * (1 + unitRoundoff64) ^ (n + 1) * multiplicationUnderflowEpsilon

noncomputable def magnitudeBound (xs : Array Float) : ℝ :=
  growth (xs.size / 2) * inputNorm xs + underflow (xs.size / 2)

noncomputable def errorBound (xs : Array Float) : ℝ :=
  (growth (xs.size / 2) - 1) * inputNorm xs + underflow (xs.size / 2)

def Admissible (xs : Array Float) : Prop :=
  xs.size / 2 ≤ 2 ^ 32 ∧
    (∀ i, i < 2 * (xs.size / 2) → Finite xs[i]!.toBits) ∧
    magnitudeBound xs < (2 : ℝ) ^ 1022

def Accuracy (xs : Array Float) : Prop :=
  (Fourier.dft xs).size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite (Fourier.dft xs)[2 * k]!.toBits ∧
      Finite (Fourier.dft xs)[2 * k + 1]!.toBits ∧
      |value (Fourier.dft xs)[2 * k]!.toBits - realDFT xs k| ≤ errorBound xs ∧
      |value (Fourier.dft xs)[2 * k + 1]!.toBits - imagDFT xs k| ≤ errorBound xs

end Verified.Examples.FourierSpec
