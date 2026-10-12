import Verified.Examples.FourierMath
import Verified.Examples.FourierLoop
import Verified.Examples.FourierTwiddle
import Verified.Examples.FourierProduct
import LeanExe.ProofKit.F64SequentialSum

namespace Verified.Examples.FourierTheorem

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx FourierSpec FourierLoop
open scoped BigOperators

set_option exponentiation.threshold 1200

private noncomputable def sampleMagnitude (xs : Array Float) (j : Nat) : ℝ :=
  FourierProduct.productMagnitude (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits)

private noncomputable def sampleError (xs : Array Float) (j : Nat) : ℝ :=
  FourierProduct.productError (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits)

private noncomputable def realReference (xs : Array Float) (k j : Nat) : ℝ :=
  value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2))) +
    value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))

private noncomputable def imagReference (xs : Array Float) (k j : Nat) : ℝ :=
  value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2))) -
    value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))

private theorem sampleMagnitude_nonneg (xs : Array Float) (j : Nat) :
    0 ≤ sampleMagnitude xs j := FourierProduct.productMagnitude_nonneg _ _

private theorem magnitude_sum (xs : Array Float) :
    (1 + unitRoundoff64) ^ (xs.size / 2) *
      (∑ j ∈ Finset.range (xs.size / 2), sampleMagnitude xs j) = magnitudeBound xs := by
  unfold magnitudeBound growth underflow inputNorm
  simp only [sampleMagnitude, FourierProduct.productMagnitude, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [pow_succ, pow_zero]
  ring

private theorem error_sum (xs : Array Float) :
    ((1 + unitRoundoff64) ^ (xs.size / 2) - 1) *
      (∑ j ∈ Finset.range (xs.size / 2), sampleMagnitude xs j) +
      (∑ j ∈ Finset.range (xs.size / 2), sampleError xs j) = errorBound xs := by
  have hpoint (j : Nat) : sampleError xs j = sampleMagnitude xs j -
      (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) := by
    unfold sampleError sampleMagnitude
    rw [FourierProduct.productMagnitude_eq]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  have hmag := magnitude_sum xs
  unfold errorBound magnitudeBound at *
  unfold inputNorm at hmag ⊢
  linear_combination hmag

private theorem sample_safe (xs : Array Float) (h : Admissible xs) (j : Nat)
    (hj : j < xs.size / 2) : sampleMagnitude xs j < (2 : ℝ) ^ 1022 := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range (xs.size / 2), sampleMagnitude xs i :=
    Finset.sum_nonneg (fun i _ => sampleMagnitude_nonneg xs i)
  have hq : 1 ≤ 1 + unitRoundoff64 := by norm_num [unitRoundoff64]
  calc
    sampleMagnitude xs j ≤ ∑ i ∈ Finset.range (xs.size / 2), sampleMagnitude xs i :=
      Finset.single_le_sum (fun i _ => sampleMagnitude_nonneg xs i) (Finset.mem_range.mpr hj)
    _ ≤ (1 + unitRoundoff64) ^ (xs.size / 2) *
        (∑ i ∈ Finset.range (xs.size / 2), sampleMagnitude xs i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hq) hsum
    _ = magnitudeBound xs := magnitude_sum xs
    _ < (2 : ℝ) ^ 1022 := h.2.2

private theorem row_terms (xs : Array Float) (h : Admissible xs) (k j : Nat)
    (hk : k < xs.size / 2) (hj : j < xs.size / 2) :
    FApprox (realTerm xs (UInt64.ofNat k) (UInt64.ofNat j)) (realReference xs k j)
        (sampleError xs j) ∧
      FApprox (imagTerm xs (UInt64.ofNat k) (UInt64.ofNat j)) (imagReference xs k j)
        (sampleError xs j) ∧
      |value (realTerm xs (UInt64.ofNat k) (UInt64.ofNat j)).toBits| ≤ sampleMagnitude xs j ∧
      |value (imagTerm xs (UInt64.ofNat k) (UInt64.ofNat j)).toBits| ≤ sampleMagnitude xs j := by
  have hn : 0 < xs.size / 2 := by omega
  have hn32 : nSamples xs ≤ 2 ^ 32 := h.1
  have hjword := ofNat_lt_nWord xs hn32 j hj
  have hkword := ofNat_lt_nWord xs hn32 k hk
  have hj64 : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by
    norm_num [UInt64.size]
    norm_num at hn32
    dsimp [nSamples] at hn32
    omega)
  have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by
    norm_num [UInt64.size]
    norm_num at hn32
    dsimp [nSamples] at hn32
    omega)
  obtain ⟨hc, hs⟩ := FourierTwiddle.twiddle_near (nWord xs)
    (UInt64.ofNat j * UInt64.ofNat k % nWord xs)
    (by rw [nWord_toNat xs hn32]; exact hn)
    (by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by rw [nWord_toNat xs hn32]; exact hn))
    ((nWord_le xs hn32).trans (by norm_num))
  have hp : 2 * Real.pi *
      (UInt64.ofNat j * UInt64.ofNat k % nWord xs).toNat / (nWord xs).toNat =
      phase (xs.size / 2) (j * k % (xs.size / 2)) := by
    rw [phase_index xs hn32 _ _ hjword hkword, hj64, hk64, nWord_toNat xs hn32]
    rfl
  rw [hp] at hc hs
  have hd : FApprox ((-1.0 : Float) *
      (Fourier.twiddle (nWord xs) (UInt64.ofNat j * UInt64.ofNat k % nWord xs)).2)
      (-Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))) (32 * unitRoundoff64) := by
    obtain ⟨hf, hv⟩ := FourierTwiddle.negOne_mul_exact _ hs.1
    refine ⟨hf, ?_⟩
    rw [hv, show -value (Fourier.twiddle (nWord xs)
      (UInt64.ofNat j * UInt64.ofNat k % nWord xs)).2.toBits -
      -Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2))) =
      -(value (Fourier.twiddle (nWord xs)
        (UInt64.ofNat j * UInt64.ofNat k % nWord xs)).2.toBits -
        Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))) by ring, abs_neg]
    exact hs.2
  have ha : Finite xs[2 * j]!.toBits := h.2.1 _ (by omega)
  have hb : Finite xs[2 * j + 1]!.toBits := h.2.1 _ (by omega)
  have hC := Real.abs_cos_le_one (phase (xs.size / 2) (j * k % (xs.size / 2)))
  have hD : |-Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))| ≤ 1 := by
    rw [abs_neg]
    exact Real.abs_sin_le_one _
  have hsafe := sample_safe xs h j hj
  have hr := FourierProduct.sub_near _ _ _ _ _ _ ha hb hc hd hC hD hsafe
  have hi := FourierProduct.add_near _ _ _ _ _ _ ha hb hd hc hD hC hsafe
  have hrmag := FourierProduct.sub_magnitude _ _ _ _ _ _ ha hb hc hd hC hD hsafe
  have himag := FourierProduct.add_magnitude _ _ _ _ _ _ ha hb hd hc hD hC hsafe
  have hjreal := sample_real_index xs hn32 _ hjword
  have hjimag := sample_imag_index xs hn32 _ hjword
  rw [hj64] at hjreal hjimag
  unfold realTerm imagTerm
  rw [hjreal, hjimag]
  refine ⟨hr.congr ?_, hi.congr ?_, hrmag, himag⟩
  · unfold realReference
    ring
  · unfold imagReference
    ring

private theorem accumulate_near (xs : Array Float) (h : Admissible xs)
    (terms : UInt64 → Float) (reference : Nat → ℝ)
    (hterms : ∀ j, j < xs.size / 2 →
      FApprox (terms (UInt64.ofNat j)) (reference j) (sampleError xs j))
    (hmag : ∀ j, j < xs.size / 2 →
      |value (terms (UInt64.ofNat j)).toBits| ≤ sampleMagnitude xs j) :
    FApprox (LeanExe.loop (nWord xs) (0.0 : Float) (fun j acc => acc + terms j))
      (∑ j ∈ Finset.range (xs.size / 2), reference j) (errorBound xs) := by
  have hn32 : nSamples xs ≤ 2 ^ 32 := h.1
  have hs := F64SequentialSum.loop_sum_bound (nWord xs) terms (sampleMagnitude xs)
    (by intro j hj; rw [nWord_toNat xs hn32] at hj; exact (hterms j hj).1)
    (fun j _ => sampleMagnitude_nonneg xs j)
    (by intro j hj; rw [nWord_toNat xs hn32] at hj; exact hmag j hj)
    (by
      rw [nWord_toNat xs hn32]
      change (1 + unitRoundoff64) ^ (xs.size / 2) *
        (∑ j ∈ Finset.range (xs.size / 2), sampleMagnitude xs j) < (2 : ℝ) ^ 1023
      rw [magnitude_sum xs]
      exact h.2.2.trans (by norm_num))
  rw [nWord_toNat xs hn32] at hs
  have he : |(∑ j ∈ Finset.range (xs.size / 2), value (terms (UInt64.ofNat j)).toBits) -
      (∑ j ∈ Finset.range (xs.size / 2), reference j)| ≤
      ∑ j ∈ Finset.range (xs.size / 2), sampleError xs j := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j hj => (hterms j (Finset.mem_range.mp hj)).2))
  refine ⟨hs.1, ?_⟩
  calc
    |value (LeanExe.loop (nWord xs) (0.0 : Float) (fun j acc => acc + terms j)).toBits -
        (∑ j ∈ Finset.range (xs.size / 2), reference j)| ≤
      |value (LeanExe.loop (nWord xs) (0.0 : Float) (fun j acc => acc + terms j)).toBits -
        (∑ j ∈ Finset.range (xs.size / 2), value (terms (UInt64.ofNat j)).toBits)| +
      |(∑ j ∈ Finset.range (xs.size / 2), value (terms (UInt64.ofNat j)).toBits) -
        (∑ j ∈ Finset.range (xs.size / 2), reference j)| := abs_sub_le _ _ _
    _ ≤ ((1 + unitRoundoff64) ^ (xs.size / 2) - 1) *
        (∑ j ∈ Finset.range (xs.size / 2), sampleMagnitude xs j) +
        (∑ j ∈ Finset.range (xs.size / 2), sampleError xs j) := add_le_add hs.2.1 he
    _ = errorBound xs := error_sum xs

theorem dft_accuracy (xs : Array Float) (h : Admissible xs) : Accuracy xs := by
  refine ⟨dft_size xs h.1, ?_⟩
  intro k hk
  have hn : 0 < xs.size / 2 := by omega
  have hr := accumulate_near xs h (realTerm xs (UInt64.ofNat k)) (realReference xs k)
    (fun j hj => (row_terms xs h k j hk hj).1)
    (fun j hj => (row_terms xs h k j hk hj).2.2.1)
  have hi := accumulate_near xs h (imagTerm xs (UInt64.ofNat k)) (imagReference xs k)
    (fun j hj => (row_terms xs h k j hk hj).2.1)
    (fun j hj => (row_terms xs h k j hk hj).2.2.2)
  change FApprox (realAccum xs (UInt64.ofNat k)) _ _ at hr
  change FApprox (imagAccum xs (UInt64.ofNat k)) _ _ at hi
  rw [dft_get_real xs h.1 k hk, dft_get_imag xs h.1 k hk]
  rw [realDFT_mod xs k hn, imagDFT_mod xs k hn]
  exact ⟨hr.1, hi.1, hr.2, hi.2⟩

#print axioms dft_accuracy

end Verified.Examples.FourierTheorem
