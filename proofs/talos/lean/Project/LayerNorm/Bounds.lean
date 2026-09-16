import Project.LayerNorm.Numerical
import Project.Softmax.Order

namespace Project.LayerNorm
open CodeLib.IEEE64

def words (a b c d : UInt64) : Fin 4 → UInt64 := ![a, b, c, d]
def outputs (r : Result) : Fin 4 → UInt64 := ![r.y0, r.y1, r.y2, r.y3]
def ValidRow (x : Fin 4 → UInt64) : Prop := ∀ i, Finite (x i) ∧ |value (x i)| ≤ 4

def Valid (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) : Prop :=
  ValidRow (words x0 x1 x2 x3) ∧ ValidRow (words g0 g1 g2 g3) ∧ ValidRow (words b0 b1 b2 b3)

theorem bounded_iff (x : UInt64) : bounded x = true ↔ Finite x ∧ |value x| ≤ 4 :=
  Softmax.bounded_iff x

theorem rowBounded_iff (a b c d : UInt64) : rowBounded a b c d = true ↔ ValidRow (words a b c d) := by
  simp only [rowBounded, Bool.and_eq_true, bounded_iff, ValidRow]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ i
    fin_cases i <;> simp [words, ha, hb, hc, hd]
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

def NumericalResult (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) (r : Result) : Prop :=
  r.status = 0 ∧ ∀ i, Finite (outputs r i) ∧
    |value (outputs r i) - Real.layerNorm (1/100000)
      (fun j => value (words x0 x1 x2 x3 j))
      (fun j => value (words g0 g1 g2 g3 j))
      (fun j => value (words b0 b1 b2 b3 j)) i| ≤ 1/1000000

theorem compute_numerical (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64)
    (h : Valid x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) :
    NumericalResult x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3
      (compute x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) := by
  refine ⟨rfl, ?_⟩
  intro i
  have hi := component_error (words x0 x1 x2 x3) (words g0 g1 g2 g3 i) (words b0 b1 b2 b3 i)
    (fun j => (h.1 j).1) (fun j => (h.1 j).2)
    (h.2.1 i).1 (h.2.2 i).1 (h.2.1 i).2 (h.2.2 i).2 i
  fin_cases i <;> simpa [compute, outputs, words, centeredWords, Real.layerNorm] using hi

theorem layerNorm_numerical (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64)
    (h : Valid x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) :
    NumericalResult x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3
      (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) := by
  have hx := (rowBounded_iff x0 x1 x2 x3).mpr h.1
  have hg := (rowBounded_iff g0 g1 g2 g3).mpr h.2.1
  have hb := (rowBounded_iff b0 b1 b2 b3).mpr h.2.2
  simpa [layerNorm, hx, hg, hb] using compute_numerical x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 h

theorem layerNorm_perturbed (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64)
    (h : Valid x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)
    (target gamma beta : Real.Row) (delta lower gain eta theta : ℝ)
    (hd : 0 ≤ delta) (hl : 0 < lower)
    (ht : lower ≤ Real.deviation (1/100000) target)
    (hx : lower ≤ Real.deviation (1/100000) (fun j => value (words x0 x1 x2 x3 j)))
    (hinput : ∀ j, |target j - value (words x0 x1 x2 x3 j)| ≤ delta)
    (hg : ∀ j, |value (words g0 g1 g2 g3 j)| ≤ gain)
    (hgamma : ∀ j, |value (words g0 g1 g2 g3 j) - gamma j| ≤ eta)
    (hbeta : ∀ j, |value (words b0 b1 b2 b3 j) - beta j| ≤ theta) (i : Fin 4) :
    |value (outputs (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) i) -
      Real.layerNorm (1/100000) target gamma beta i| ≤
        1/1000000 + gain*(2*delta/lower) + 2*eta + theta := by
  have hn := layerNorm_numerical x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 h
  exact Real.implementation_perturbation (1/100000) delta lower gain eta theta (1/1000000)
    (by norm_num) hd hl target (fun j => value (words x0 x1 x2 x3 j))
    gamma (fun j => value (words g0 g1 g2 g3 j)) beta (fun j => value (words b0 b1 b2 b3 j))
    (fun j => value (outputs (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) j))
    ht hx hinput hg hgamma hbeta (fun j => (hn.2 j).2) i

#print axioms rowBounded_iff
#print axioms layerNorm_numerical
#print axioms layerNorm_perturbed
end Project.LayerNorm
