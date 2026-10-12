import Verified.Examples.FFT
import Verified.Examples.FFTArithmetic
import Verified.Examples.FourierMath
import Verified.Examples.FourierInverse
import Verified.Examples.FourierPowerSpec

namespace Verified.Examples.FFTSpec

open CodeLib.IEEE64

noncomputable def underflow : Nat → ℝ
  | 0 => 0
  | p + 1 => 2 * FFTArithmetic.r * underflow p + FFTArithmetic.nu

noncomputable def radixMagnitude (p : Nat) (A : ℝ) : ℝ :=
  FFTArithmetic.r ^ p * A + underflow p

noncomputable def radixError (p : Nat) (A : ℝ) : ℝ :=
  (FFTArithmetic.r ^ p - 1) * A + underflow p

noncomputable def radixSafety (p : Nat) (A : ℝ) : ℝ :=
  2 * FFTArithmetic.q * radixMagnitude p A +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

noncomputable def magnitudeBound (xs : Array Float) : ℝ :=
  if FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) then
    radixMagnitude (Nat.log2 (xs.size / 2)) (FourierSpec.inputNorm xs)
  else FourierSpec.magnitudeBound xs

noncomputable def errorBound (xs : Array Float) : ℝ :=
  if FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) then
    radixError (Nat.log2 (xs.size / 2)) (FourierSpec.inputNorm xs)
  else FourierSpec.errorBound xs

def Radix2Admissible (xs : Array Float) (p : Nat) : Prop :=
  xs.size / 2 = 2 ^ p ∧ p ≤ 32 ∧
    (∀ i, i < 2 * (xs.size / 2) → Finite xs[i]!.toBits) ∧
    radixSafety p (FourierSpec.inputNorm xs) < (2 : ℝ) ^ 1022

def Admissible (xs : Array Float) : Prop :=
  xs.size / 2 ≤ 2 ^ 32 ∧
    (∀ i, i < 2 * (xs.size / 2) → Finite xs[i]!.toBits) ∧
    (if FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) then
      radixSafety (Nat.log2 (xs.size / 2)) (FourierSpec.inputNorm xs) < (2 : ℝ) ^ 1022
    else FourierSpec.magnitudeBound xs < (2 : ℝ) ^ 1022)

def AccurateOutput (xs ys : Array Float) : Prop :=
  ys.size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite ys[2 * k]!.toBits ∧ Finite ys[2 * k + 1]!.toBits ∧
      |value ys[2 * k]!.toBits - FourierSpec.realDFT xs k| ≤ errorBound xs ∧
      |value ys[2 * k + 1]!.toBits - FourierSpec.imagDFT xs k| ≤ errorBound xs

noncomputable def inverseError (xs : Array Float) : ℝ :=
  (errorBound xs + unitRoundoff64 * magnitudeBound xs) / (xs.size / 2 : ℕ) +
    multiplicationUnderflowEpsilon

def AccurateInverse (xs ys : Array Float) : Prop :=
  ys.size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite ys[2 * k]!.toBits ∧ Finite ys[2 * k + 1]!.toBits ∧
      |value ys[2 * k]!.toBits - FourierInverse.realReference xs k| ≤ inverseError xs ∧
      |value ys[2 * k + 1]!.toBits - FourierInverse.imagReference xs k| ≤ inverseError xs

noncomputable def powerError (samples : Array Float) : ℝ :=
  let E := errorBound (FourierPowerEmbedding.embed samples)
  let B := magnitudeBound (FourierPowerEmbedding.embed samples)
  let A := FourierPowerEmbedding.sampleNorm samples
  4 * A * E + 2 * E ^ 2 + 2 * unitRoundoff64 * (2 + unitRoundoff64) * B ^ 2 +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

def PowerAdmissible (samples : Array Float) : Prop :=
  samples.size ≤ 2 ^ 32 ∧ (∀ i, i < samples.size → Finite samples[i]!.toBits) ∧
    (if FFT.isRadix2 (UInt64.ofNat samples.size) then
      radixSafety (Nat.log2 samples.size) (FourierPowerEmbedding.sampleNorm samples) <
        (2 : ℝ) ^ 1022 ∧
      FourierPowerArithmetic.squareMagnitude
        (radixMagnitude (Nat.log2 samples.size) (FourierPowerEmbedding.sampleNorm samples)) <
        (2 : ℝ) ^ 1022
    else FourierPowerArithmetic.squareMagnitude (FourierPowerSpec.magnitudeBound samples) <
      (2 : ℝ) ^ 1022)

def AccuratePower (samples ys : Array Float) : Prop :=
  ys.size = FourierPowerEmbedding.powerCount samples.size ∧
    ∀ k, k < FourierPowerEmbedding.powerCount samples.size →
      Finite ys[k]!.toBits ∧ 0 ≤ value ys[k]!.toBits ∧
      |value ys[k]!.toBits - FourierPowerSpec.realPower samples k| ≤ powerError samples

end Verified.Examples.FFTSpec
