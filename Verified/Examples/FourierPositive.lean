import Verified.Examples.FourierTheorem

namespace Verified.Examples.FourierPositive

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx FourierSpec FourierLoop
open scoped BigOperators

def transform (xs : Array Float) : Array Float :=
  Fourier.transformWith Trig.invPi Trig.halfPi 1.0 xs

noncomputable def realReference (xs : Array Float) (k : Nat) : ℝ :=
  ∑ j ∈ Finset.range (xs.size / 2),
    (value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k)) -
      value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k)))

noncomputable def imagReference (xs : Array Float) (k : Nat) : ℝ :=
  ∑ j ∈ Finset.range (xs.size / 2),
    (value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k)) +
      value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k)))

private noncomputable def realReferenceTerm (xs : Array Float) (k j : Nat) : ℝ :=
  value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2))) -
    value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))

private noncomputable def imagReferenceTerm (xs : Array Float) (k j : Nat) : ℝ :=
  value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2))) +
    value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2)))

theorem one_mul_exact (s : Float) (hs : Finite s.toBits) :
    Finite ((1.0 : Float) * s).toBits ∧ value ((1.0 : Float) * s).toBits = value s.toBits := by
  rw [F64Bits.toBits_mul, show (1.0 : Float).toBits = 0x3FF0000000000000 by decide]
  exact FourierTwiddle.one_mul_exact s.toBits hs

theorem one_mul_near {s : Float} {v e : ℝ} (hs : FApprox s v e) :
    FApprox ((1.0 : Float) * s) v e := by
  obtain ⟨hf, hv⟩ := one_mul_exact s hs.1
  exact ⟨hf, by rw [hv]; exact hs.2⟩

private theorem reference_mod (xs : Array Float) (k : Nat) (hn : 0 < xs.size / 2) :
    realReference xs k = ∑ j ∈ Finset.range (xs.size / 2), realReferenceTerm xs k j ∧
    imagReference xs k = ∑ j ∈ Finset.range (xs.size / 2), imagReferenceTerm xs k j := by
  constructor
  · unfold realReference realReferenceTerm
    apply Finset.sum_congr rfl
    intro j _
    rw [cos_phase_mod _ _ hn, sin_phase_mod _ _ hn]
  · unfold imagReference imagReferenceTerm
    apply Finset.sum_congr rfl
    intro j _
    rw [cos_phase_mod _ _ hn, sin_phase_mod _ _ hn]

private theorem row_terms (xs : Array Float) (h : Admissible xs) (k j : Nat)
    (hk : k < xs.size / 2) (hj : j < xs.size / 2) :
    FApprox (realTermWith 1.0 xs (UInt64.ofNat k) (UInt64.ofNat j))
        (realReferenceTerm xs k j)
        (FourierProduct.productError (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits)) ∧
      FApprox (imagTermWith 1.0 xs (UInt64.ofNat k) (UInt64.ofNat j))
        (imagReferenceTerm xs k j)
        (FourierProduct.productError (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits)) ∧
      |value (realTermWith 1.0 xs (UInt64.ofNat k) (UInt64.ofNat j)).toBits| ≤
        FourierProduct.productMagnitude (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits) ∧
      |value (imagTermWith 1.0 xs (UInt64.ofNat k) (UInt64.ofNat j)).toBits| ≤
        FourierProduct.productMagnitude (value xs[2 * j]!.toBits) (value xs[2 * j + 1]!.toBits) := by
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
  have hd := one_mul_near hs
  have ha : Finite xs[2 * j]!.toBits := h.2.1 _ (by omega)
  have hb : Finite xs[2 * j + 1]!.toBits := h.2.1 _ (by omega)
  have hC := Real.abs_cos_le_one (phase (xs.size / 2) (j * k % (xs.size / 2)))
  have hD := Real.abs_sin_le_one (phase (xs.size / 2) (j * k % (xs.size / 2)))
  have hsafe := FourierTheorem.sample_safe xs h j hj
  have hr := FourierProduct.sub_near _ _ _ _ _ _ ha hb hc hd hC hD hsafe
  have hi := FourierProduct.add_near _ _ _ _ _ _ ha hb hd hc hD hC hsafe
  have hrmag := FourierProduct.sub_magnitude _ _ _ _ _ _ ha hb hc hd hC hD hsafe
  have himag := FourierProduct.add_magnitude _ _ _ _ _ _ ha hb hd hc hD hC hsafe
  have hjreal := sample_real_index xs hn32 _ hjword
  have hjimag := sample_imag_index xs hn32 _ hjword
  rw [hj64] at hjreal hjimag
  unfold realTermWith imagTermWith
  rw [hjreal, hjimag]
  exact ⟨hr, hi, hrmag, himag⟩

theorem accuracy (xs : Array Float) (h : Admissible xs) :
    (transform xs).size = 2 * (xs.size / 2) ∧
      ∀ k, k < xs.size / 2 →
        FApprox (transform xs)[2 * k]! (realReference xs k) (errorBound xs) ∧
        FApprox (transform xs)[2 * k + 1]! (imagReference xs k) (errorBound xs) := by
  refine ⟨transform_size 1.0 xs h.1, ?_⟩
  intro k hk
  have hn : 0 < xs.size / 2 := by omega
  have hr := FourierTheorem.accumulate_near xs h
    (realTermWith 1.0 xs (UInt64.ofNat k)) (realReferenceTerm xs k)
    (fun j hj => (row_terms xs h k j hk hj).1)
    (fun j hj => (row_terms xs h k j hk hj).2.2.1)
  have hi := FourierTheorem.accumulate_near xs h
    (imagTermWith 1.0 xs (UInt64.ofNat k)) (imagReferenceTerm xs k)
    (fun j hj => (row_terms xs h k j hk hj).2.1)
    (fun j hj => (row_terms xs h k j hk hj).2.2.2)
  change FApprox (realAccumWith 1.0 xs (UInt64.ofNat k)) _ _ at hr
  change FApprox (imagAccumWith 1.0 xs (UInt64.ofNat k)) _ _ at hi
  unfold transform
  rw [transform_get_real 1.0 xs h.1 k hk, transform_get_imag 1.0 xs h.1 k hk,
    (reference_mod xs k hn).1, (reference_mod xs k hn).2]
  exact ⟨hr, hi⟩

private theorem pair_norm (A B C D : ℝ) (hC : |C| ≤ 1) (hD : |D| ≤ 1) :
    |A * C| + |B * D| ≤ |A| + |B| := by
  rw [abs_mul, abs_mul]
  simpa only [mul_one] using add_le_add
    (mul_le_mul_of_nonneg_left hC (abs_nonneg A))
    (mul_le_mul_of_nonneg_left hD (abs_nonneg B))

theorem realReference_abs (xs : Array Float) (k : Nat) :
    |realReference xs k| ≤ inputNorm xs := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (abs_sub _ _).trans (pair_norm _ _ _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _))

theorem imagReference_abs (xs : Array Float) (k : Nat) :
    |imagReference xs k| ≤ inputNorm xs := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (abs_add_le _ _).trans (pair_norm _ _ _ _ (Real.abs_sin_le_one _) (Real.abs_cos_le_one _))

#print axioms one_mul_exact
#print axioms one_mul_near
#print axioms accuracy
#print axioms realReference_abs
#print axioms imagReference_abs

end Verified.Examples.FourierPositive
