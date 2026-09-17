import Project.TinyGpt2.CheckpointContract
import Project.TinyGpt2.CheckpointComputedResidual

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem normFinal_scale (i : Fin 4) : |(decodeNorm words 2480).scale i| ≤ 13/5 := by
  have h : |F64Rational.decode words[2480+i.val]!| ≤ 13/5 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem normFinal_bias (i : Fin 4) : |(decodeNorm words 2480).bias i| ≤ 1 := by
  have h : |F64Rational.decode words[2484+i.val]!| ≤ 1 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem normFinal_real_magnitude (x : Real.Row) (i : Fin 4) :
    |Real.norm (decodeNorm words 2480) x i| ≤ 31/5 := by
  have hn := LayerNorm.Real.normalized_magnitude (1/100000) (by norm_num) x i
  have hp := mul_le_mul hn (normFinal_scale i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [← abs_mul] at hp
  change |LayerNorm.Real.normalized (1/100000) x i*(decodeNorm words 2480).scale i+
    (decodeNorm words 2480).bias i| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add hp (normFinal_bias i)).trans_eq (by norm_num))

theorem normFinal_error (x : Row) (hx : ∀ i, Affine.Bounded (rowWords x i) 16) (i : Fin 4) :
    Approximation (rowWords (norm words 2480 x) i)
      (Real.norm (decodeNorm words 2480) (decodeRow x) i) 7 (1/100000) := by
  have hn := norm_error_bounded words 2480 x 16 (by norm_num) (by norm_num) hx
    (loaded_valid 2480 (by rw [words_size]; decide))
    (loaded_valid 2484 (by rw [words_size]; decide)) i
  have he : |decodeRow (norm words 2480 x) i-Real.norm (decodeNorm words 2480) (decodeRow x) i| ≤
      1/100000 := hn.2.trans (by norm_num [arithmeticEpsilon])
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he (normFinal_real_magnitude (decodeRow x) i)
  exact ⟨hn.1, hm.trans (by norm_num), he⟩

theorem computedFinal_bound (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (i : Fin 4) :
    Affine.Bounded (rowWords
      (norm words 2480 (addRows x (contractRow words (computedActivated x)))) i) 7 := by
  have hr := computedResidual2_bound x hx
  have h := normFinal_error _ (fun j => ⟨(hr j).1, (hr j).2.trans (by norm_num)⟩) i
  exact ⟨h.finite, h.magnitude⟩

#print axioms normFinal_error
#print axioms computedFinal_bound
end Project.TinyGpt2.Checkpoint
