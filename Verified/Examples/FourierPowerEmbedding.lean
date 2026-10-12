import Verified.Examples.FourierMath
import LeanExe.ProofKit.F64Magnitude
import LeanExe.IR.Combinators

namespace Verified.Examples.FourierPowerEmbedding
open CodeLib.IEEE64
open scoped BigOperators

def embed (samples : Array Float) : Array Float :=
  LeanExe.build (2 * samples.size.toUInt64) fun i =>
    if i % 2 == 0 then samples[(i / 2).toNat]! else 0.0

def powerCount (n : Nat) : Nat := if n = 0 then 0 else n / 2 + 1

noncomputable def sampleNorm (samples : Array Float) : ℝ :=
  ∑ j ∈ Finset.range samples.size, |value samples[j]!.toBits|

noncomputable def realPart (samples : Array Float) (k : Nat) : ℝ :=
  ∑ j ∈ Finset.range samples.size,
    value samples[j]!.toBits * Real.cos (FourierSpec.phase samples.size (j * k))

noncomputable def imagPart (samples : Array Float) (k : Nat) : ℝ :=
  -(∑ j ∈ Finset.range samples.size,
    value samples[j]!.toBits * Real.sin (FourierSpec.phase samples.size (j * k)))

theorem sampleWord_toNat (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    samples.size.toUInt64.toNat = samples.size := by
  change (UInt64.ofNat samples.size).toNat = samples.size
  apply UInt64.toNat_ofNat_of_lt'
  norm_num [UInt64.size]
  norm_num at hn
  omega

private theorem double_toNat (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (2 * samples.size.toUInt64).toNat = 2 * samples.size := by
  rw [UInt64.toNat_mul, sampleWord_toNat samples hn]
  simp only [UInt64.reduceToNat]
  apply Nat.mod_eq_of_lt
  norm_num at hn ⊢
  omega

theorem embed_size (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (embed samples).size = 2 * samples.size := by
  rw [embed, LeanExe.IR.build_size, double_toNat samples hn]

theorem embed_nSamples (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (embed samples).size / 2 = samples.size := by rw [embed_size samples hn]; omega

private theorem index_toNat (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (i : Nat) (hi : i < 2 * samples.size) : (UInt64.ofNat i).toNat = i := by
  apply UInt64.toNat_ofNat_of_lt'
  norm_num [UInt64.size]
  norm_num at hn
  omega

theorem embed_real (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (j : Nat) (hj : j < samples.size) : (embed samples)[2 * j]! = samples[j]! := by
  have hi64 := index_toNat samples hn (2 * j) (by omega)
  have heven : UInt64.ofNat (2 * j) % 2 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, hi64]
    simp
  have hdiv : (UInt64.ofNat (2 * j) / 2).toNat = j := by
    rw [UInt64.toNat_div, hi64]
    simp
  unfold embed
  rw [LeanExe.IR.build_get (by rw [double_toNat samples hn]; omega)]
  simp only [heven, beq_self_eq_true, hdiv, ite_true]

theorem embed_imag (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (j : Nat) (hj : j < samples.size) : (embed samples)[2 * j + 1]! = (0.0 : Float) := by
  have hi64 := index_toNat samples hn (2 * j + 1) (by omega)
  have hodd : UInt64.ofNat (2 * j + 1) % 2 ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_mod, hi64] at this
    simp only [UInt64.reduceToNat] at this
    omega
  unfold embed
  rw [LeanExe.IR.build_get (by rw [double_toNat samples hn]; omega)]
  simp only [beq_iff_eq, hodd, ite_false]

theorem embed_finite (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (hf : ∀ j, j < samples.size → Finite samples[j]!.toBits)
    (i : Nat) (hi : i < (embed samples).size) : Finite (embed samples)[i]!.toBits := by
  rw [embed_size samples hn] at hi
  have hi64 := index_toNat samples hn i hi
  unfold embed
  rw [LeanExe.IR.build_get (by rw [double_toNat samples hn]; exact hi)]
  split
  · apply hf
    rw [UInt64.toNat_div, hi64]
    simp only [UInt64.reduceToNat]
    omega
  · change Finite (0 : UInt64)
    unfold CodeLib.IEEE64.Finite
    decide +kernel

theorem sampleNorm_nonneg (samples : Array Float) : 0 ≤ sampleNorm samples := by
  unfold sampleNorm
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem inputNorm_embed (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    FourierSpec.inputNorm (embed samples) = sampleNorm samples := by
  unfold FourierSpec.inputNorm sampleNorm
  rw [embed_nSamples samples hn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [embed_real samples hn j (Finset.mem_range.mp hj),
    embed_imag samples hn j (Finset.mem_range.mp hj)]
  simp only [show (0.0 : Float).toBits = (0 : UInt64) from rfl,
    LeanExe.ProofKit.F64Magnitude.value_zero, abs_zero, add_zero]

theorem realDFT_embed (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) (k : Nat) :
    FourierSpec.realDFT (embed samples) k = realPart samples k := by
  unfold FourierSpec.realDFT realPart
  rw [embed_nSamples samples hn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [embed_real samples hn j (Finset.mem_range.mp hj),
    embed_imag samples hn j (Finset.mem_range.mp hj)]
  simp only [show (0.0 : Float).toBits = (0 : UInt64) from rfl,
    LeanExe.ProofKit.F64Magnitude.value_zero, zero_mul, add_zero]

theorem imagDFT_embed (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) (k : Nat) :
    FourierSpec.imagDFT (embed samples) k = imagPart samples k := by
  unfold FourierSpec.imagDFT imagPart
  rw [embed_nSamples samples hn, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [embed_real samples hn j (Finset.mem_range.mp hj),
    embed_imag samples hn j (Finset.mem_range.mp hj)]
  simp only [show (0.0 : Float).toBits = (0 : UInt64) from rfl,
    LeanExe.ProofKit.F64Magnitude.value_zero, zero_mul, zero_sub]

theorem powerSpectrum_eq_build (samples : Array Float) :
    Fourier.powerSpectrum samples =
      LeanExe.build (if samples.size.toUInt64 == 0 then 0 else samples.size.toUInt64 / 2 + 1)
        (fun k =>
          let ys := Fourier.dft (embed samples)
          let a := ys[(2 * k).toNat]!
          let b := ys[(2 * k + 1).toNat]!
          a * a + b * b) := by rfl

private theorem count_toNat (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (if samples.size.toUInt64 == 0 then 0 else samples.size.toUInt64 / 2 + 1).toNat =
      powerCount samples.size := by
  by_cases hz : samples.size = 0
  · have hw : samples.size.toUInt64 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [sampleWord_toNat samples hn]
      exact hz
    rw [hw]
    simp only [beq_self_eq_true, ite_true, UInt64.reduceToNat, powerCount, hz]
  · have hw : samples.size.toUInt64 ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      rw [sampleWord_toNat samples hn] at this
      exact hz this
    simp only [beq_iff_eq, hw, ite_false, UInt64.toNat_add, UInt64.toNat_div,
      sampleWord_toNat samples hn, UInt64.reduceToNat, powerCount, hz]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega

theorem powerSpectrum_size (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (Fourier.powerSpectrum samples).size = powerCount samples.size := by
  rw [powerSpectrum_eq_build, LeanExe.IR.build_size, count_toNat samples hn]

theorem powerSpectrum_get (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (k : Nat) (hk : k < powerCount samples.size) :
    (Fourier.powerSpectrum samples)[k]! =
      (Fourier.dft (embed samples))[2 * k]! * (Fourier.dft (embed samples))[2 * k]! +
      (Fourier.dft (embed samples))[2 * k + 1]! * (Fourier.dft (embed samples))[2 * k + 1]! := by
  have hkbound : k < samples.size := by
    unfold powerCount at hk
    split at hk <;> omega
  have hk64 : (UInt64.ofNat k).toNat = k :=
    index_toNat samples hn k (by omega)
  have htwice : (2 * UInt64.ofNat k).toNat = 2 * k := by
    rw [UInt64.toNat_mul, hk64]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega
  have hodd : (2 * UInt64.ofNat k + 1).toNat = 2 * k + 1 := by
    rw [UInt64.toNat_add, htwice]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega
  rw [powerSpectrum_eq_build, LeanExe.IR.build_get (by rw [count_toNat samples hn]; exact hk)]
  simp only [htwice, hodd]

#print axioms embed_size
#print axioms embed_real
#print axioms embed_imag
#print axioms embed_finite
#print axioms inputNorm_embed
#print axioms realDFT_embed
#print axioms imagDFT_embed
#print axioms powerSpectrum_eq_build
#print axioms powerSpectrum_size
#print axioms powerSpectrum_get

end Verified.Examples.FourierPowerEmbedding
