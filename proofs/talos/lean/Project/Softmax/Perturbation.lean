import Project.Softmax.Numerical
import Project.Softmax.RealPerturbation

namespace Project.Softmax
open CodeLib.IEEE64

def visible (n : UInt64) (i : Fin 4) : Bool := decide (indexWord i < n)

theorem reference_eq_real (n : UInt64) (s : Fin 4 → UInt64) (i : Fin 4) :
    reference n s i = Real.probability (visible n) (fun j => value (s j)) i := by
  simp only [reference, unshifted, Real.probability, Real.weight, visible, decide_eq_true_eq]

theorem reference_perturbation (n : UInt64) (s : Fin 4 → UInt64)
    (target : Fin 4 → ℝ) (delta : ℝ) (hn : 0 < n) (hd : 0 ≤ delta)
    (he : ∀ j, |value (s j)-target j| ≤ delta) (i : Fin 4) :
    |reference n s i-Real.probability (visible n) target i| ≤ 2*delta := by
  rw [reference_eq_real]
  exact Real.probability_perturbation (visible n) _ target delta
    ⟨0, by change decide ((0 : UInt64) < n) = true; exact decide_eq_true hn⟩ hd he i

theorem compute_spread_perturbed (n a b c d : UInt64) (h : SpreadValid n a b c d)
    (target : Fin 4 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (he : ∀ j, |value (scores a b c d j)-target j| ≤ delta) (i : Fin 4) :
    |value (outputs (compute n a b c d) i)-Real.probability (visible n) target i| ≤
      1/64+2*delta := by
  have hn := ((compute_numerical_spread n a b c d h).2.1 i).2.2.2.2
  exact (abs_sub_le _ _ _).trans
    (add_le_add hn (reference_perturbation n _ target delta h.1 hd he i))

theorem compute_perturbed (n a b c d : UInt64) (h : Valid n a b c d)
    (target : Fin 4 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (he : ∀ j, |value (scores a b c d j)-target j| ≤ delta) (i : Fin 4) :
    |value (outputs (compute n a b c d) i)-Real.probability (visible n) target i| ≤
      1/64+2*delta :=
  compute_spread_perturbed n a b c d (valid_spread n a b c d h) target delta hd he i

theorem softmax_perturbed (n a b c d : UInt64) (h : Valid n a b c d)
    (target : Fin 4 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (he : ∀ j, |value (scores a b c d j)-target j| ≤ delta) (i : Fin 4) :
    |value (outputs (softmax n a b c d) i)-Real.probability (visible n) target i| ≤
      1/64+2*delta := by
  rw [softmax_success n a b c d h]
  exact compute_perturbed n a b c d h target delta hd he i

#print axioms softmax_perturbed
end Project.Softmax
