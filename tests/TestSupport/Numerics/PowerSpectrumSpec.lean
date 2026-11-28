module

public import Library.Numerics.Fourier.Master

@[expose] public section

/-!
A test of `Library.Numerics.Fourier.powerSpectrum_spec`, the theorem of the Lean function
`powerSpectrum`, for a caller that computes the power spectrum in Lean and needs the error of each
float.  Eight finite samples of magnitude at most 1 have five bins, each finite and within
`2 ^ -30` of the squared magnitude of the transform, which the theorem's bound gives with the mass
of the samples at most 8.
-/

namespace TestSupport.Numerics.PowerSpectrumSpec

open Library.Numerics.Fourier
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-- The mass of eight samples of magnitude at most 1 is at most 8. -/
theorem mass_le (s : Array Float) (hs : s.size = 8) (h1 : ∀ j < 8, |value s[j]!.toBits| ≤ 1) :
    ∑ j ∈ Finset.range s.size, |value s[j]!.toBits| ≤ 8 := by
  rw [hs]
  calc ∑ j ∈ Finset.range 8, |value s[j]!.toBits|
      ≤ ∑ _j ∈ Finset.range 8, (1 : ℝ) :=
        Finset.sum_le_sum fun j hj => h1 j (Finset.mem_range.mp hj)
    _ = 8 := by norm_num

/-- The bound of `powerSpectrum_spec` for eight samples of mass `M ≤ 8` is at most `2 ^ -30`. -/
theorem bound_le (M : ℝ) (h0 : 0 ≤ M) (h8 : M ≤ 8) :
    let E := (((8 - 1 : ℕ) : ℝ) / (2 ^ 53 - (8 - 1 : ℕ)) + 1 / 2 ^ 46) * M + (8 : ℕ) / 2 ^ 1071
    5 * M * E + 3 * E ^ 2 + 5 * M ^ 2 / 2 ^ 53 + 3 / 2 ^ 1075 ≤ 1 / 2 ^ 30 := by
  intro E
  have hE0 : 0 ≤ E := by positivity
  have hE : E ≤ 1 / 2 ^ 40 := by
    show (((8 - 1 : ℕ) : ℝ) / (2 ^ 53 - (8 - 1 : ℕ)) + 1 / 2 ^ 46) * M + (8 : ℕ) / 2 ^ 1071 ≤ _
    norm_num
    nlinarith
  have h1 : 5 * M * E ≤ 5 * 8 * (1 / 2 ^ 40) := by gcongr
  have h2 : 3 * E ^ 2 ≤ 3 * (1 / 2 ^ 40) ^ 2 := by gcongr
  have h3 : 5 * M ^ 2 / 2 ^ 53 ≤ 5 * 8 ^ 2 / 2 ^ 53 := by gcongr
  linarith [show 5 * 8 * (1 / 2 ^ 40 : ℝ) + 3 * (1 / 2 ^ 40) ^ 2 + 5 * 8 ^ 2 / 2 ^ 53 +
    3 / 2 ^ 1075 ≤ 1 / 2 ^ 30 by norm_num]

/-- The power spectrum of eight finite samples of magnitude at most 1 has five finite bins, each
within `2 ^ -30` of the squared magnitude of the transform. -/
theorem eight_samples (s : Array Float) (hs : s.size = 8) (hf : ∀ v ∈ s, Finite v.toBits)
    (h1 : ∀ j < 8, |value s[j]!.toBits| ≤ 1) :
    (powerSpectrum s).size = 5 ∧ ∀ k < 5, Finite (powerSpectrum s)[k]!.toBits ∧
      |value (powerSpectrum s)[k]!.toBits -
          ((∑ j ∈ Finset.range s.size,
              value s[j]!.toBits * Real.cos (2 * Real.pi * j * k / s.size)) ^ 2 +
            (∑ j ∈ Finset.range s.size,
              value s[j]!.toBits * Real.sin (2 * Real.pi * j * k / s.size)) ^ 2)| ≤
        1 / 2 ^ 30 := by
  have hM8 := mass_le s hs h1
  obtain ⟨hsize, hk⟩ := powerSpectrum_spec s (by omega) hf (hM8.trans (by norm_num))
  have h5 : (powerSpectrum s).size = 5 := by rw [hsize, hs]; rfl
  refine ⟨h5, fun k hk5 => ?_⟩
  obtain ⟨hfin, hb⟩ := hk k (by omega)
  refine ⟨hfin, hb.trans ?_⟩
  have h0 : 0 ≤ ∑ j ∈ Finset.range s.size, |value s[j]!.toBits| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have := bound_le _ h0 hM8
  rw [hs] at this ⊢
  exact this

#print axioms eight_samples

end TestSupport.Numerics.PowerSpectrumSpec
