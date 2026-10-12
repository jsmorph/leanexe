import Verified.Examples.FourierPowerArithmetic
import Verified.Examples.FourierPowerEmbedding

namespace Verified.Examples.FourierPowerSpec
open CodeLib.IEEE64 FourierPowerEmbedding

noncomputable def componentError (samples : Array Float) : ℝ :=
  (FourierSpec.growth samples.size - 1) * sampleNorm samples + FourierSpec.underflow samples.size

noncomputable def magnitudeBound (samples : Array Float) : ℝ :=
  FourierSpec.growth samples.size * sampleNorm samples + FourierSpec.underflow samples.size

noncomputable def errorBound (samples : Array Float) : ℝ :=
  4 * sampleNorm samples * componentError samples + 2 * componentError samples ^ 2 +
    2 * unitRoundoff64 * (2 + unitRoundoff64) * magnitudeBound samples ^ 2 +
    2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon

noncomputable def realPower (samples : Array Float) (k : Nat) : ℝ :=
  realPart samples k ^ 2 + imagPart samples k ^ 2

def Admissible (samples : Array Float) : Prop :=
  samples.size ≤ 2 ^ 32 ∧
    (∀ j, j < samples.size → Finite samples[j]!.toBits) ∧
    FourierPowerArithmetic.squareMagnitude (magnitudeBound samples) < (2 : ℝ) ^ 1022

def Accuracy (samples : Array Float) : Prop :=
  (Fourier.powerSpectrum samples).size = powerCount samples.size ∧
    ∀ k, k < powerCount samples.size →
      Finite (Fourier.powerSpectrum samples)[k]!.toBits ∧
      0 ≤ value (Fourier.powerSpectrum samples)[k]!.toBits ∧
      |value (Fourier.powerSpectrum samples)[k]!.toBits - realPower samples k| ≤ errorBound samples

end Verified.Examples.FourierPowerSpec
