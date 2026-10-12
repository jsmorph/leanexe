import Verified.Examples.FFTTheorem
import Verified.Examples.FFTDivision

namespace Verified.Examples.FFTInverse

open CodeLib.IEEE64 LeanExe.ProofKit.F64Approx FFTSpec

theorem normalize_near (xs : Array Float) (h : Admissible xs) (hn : 0 < xs.size / 2)
    (y : Float) (R : ℝ) (hy : FApprox y R (errorBound xs))
    (hR : |R| ≤ FourierSpec.inputNorm xs) :
    FApprox (y / (xs.size.toUInt64 / 2).toFloat) (R / (xs.size / 2 : ℕ))
      (inverseError xs) := by
  have hnNat : (xs.size.toUInt64 / 2).toNat = xs.size / 2 := FourierLoop.nWord_toNat xs h.1
  have ha := FFTDivision.normalize_near (xs.size.toUInt64 / 2)
    (by rw [hnNat]; exact hn)
    (by rw [hnNat]; exact h.1.trans (by norm_num))
    y R (FourierSpec.inputNorm xs) (errorBound xs) hy hR
    (by rw [← FFTTheorem.magnitudeBound_eq]; exact FFTTheorem.magnitude_safe xs h)
  rw [hnNat, ← FFTTheorem.magnitudeBound_eq] at ha
  exact ha

theorem inverse_accuracy (xs : Array Float) (h : Admissible xs) :
    AccurateInverse xs (FFT.inverse xs) := by
  have ha := FFTTheorem.transform_accuracy xs true h
  refine ⟨FFTLoop.inverse_size xs h.1, ?_⟩
  intro k hk
  have hn : 0 < xs.size / 2 := by omega
  have row := ha.2 k hk
  have hre := normalize_near xs h hn _ _ row.1 (FourierPositive.realReference_abs xs k)
  have him := normalize_near xs h hn _ _ row.2.1 (FourierPositive.imagReference_abs xs k)
  change Finite (FFT.inverseWith Trig.invPi Trig.halfPi xs)[2 * k]!.toBits ∧
    Finite (FFT.inverseWith Trig.invPi Trig.halfPi xs)[2 * k + 1]!.toBits ∧
    |value (FFT.inverseWith Trig.invPi Trig.halfPi xs)[2 * k]!.toBits -
      FourierInverse.realReference xs k| ≤ inverseError xs ∧
    |value (FFT.inverseWith Trig.invPi Trig.halfPi xs)[2 * k + 1]!.toBits -
      FourierInverse.imagReference xs k| ≤ inverseError xs
  rw [FFTLoop.inverseWith_get _ _ xs h.1 (2 * k) (by omega),
    FFTLoop.inverseWith_get _ _ xs h.1 (2 * k + 1) (by omega)]
  exact ⟨hre.1, him.1, hre.2, him.2⟩

#print axioms normalize_near
#print axioms inverse_accuracy

end Verified.Examples.FFTInverse
