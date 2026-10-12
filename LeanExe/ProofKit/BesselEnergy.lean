import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
Energy bounds for the error of an approximate solution of the system
`P'' = 2 Q' - (κ/x ^ 2) P`, `Q'' = -2 P' - (κ/x ^ 2) Q` that the large-argument functions
`P` and `Q` of the Bessel functions satisfy, with `κ = 1/4` for order 0 and `κ = -3/4` for order
1.  For the errors `p = P - A` and `q = Q - B` of an approximation `(A, B)` with residuals
`r₁ = A'' - 2 B' + (κ/x ^ 2) A` and `r₂ = B'' + 2 A' + (κ/x ^ 2) B`, the vector
`(p' - q, q' + p)` is the derivative of `(p + i q) e ^ (i x)` turned back by `e ^ (-i x)`, and

* for `κ ≥ 0`, `E = (p' - q) ^ 2 + (q' + p) ^ 2 + (1 + κ/x ^ 2) (p ^ 2 + q ^ 2)` satisfies
  `E' = -2 (r₁ (p' - q) + r₂ (q' + p)) - (2κ/x ^ 3) (p ^ 2 + q ^ 2) ≤ 2 (|r₁| + |r₂|) √E`;
* for `κ < 0` with `m = 1 + κ/x ^ 2 ≥ 81/100`,
  `E = ((p' - q) ^ 2 + (q' + p) ^ 2)/m + p ^ 2 + q ^ 2` satisfies
  `E' ≤ 2 (10/9) (|r₁| + |r₂|) √E`.

`sqrt_le_of_deriv` turns `E' ≤ 2 g √E` into `√E x ≤ √E a + ∫ₐˣ g`, with the integral given as
`G x - G a` for an antiderivative `G` of `g`.  Both energies bound `p ^ 2 + q ^ 2`, so the error of
the approximation stays within the residuals' integral of its value at `a`.
-/

namespace LeanExe.ProofKit.BesselEnergy

open Set

theorem sqrt_le_of_deriv {E E' G g : ℝ → ℝ} {a b : ℝ} (hE : ∀ x ∈ Icc a b, HasDerivAt E (E' x) x)
    (hE0 : ∀ x ∈ Icc a b, 0 ≤ E x) (hG : ∀ x ∈ Icc a b, HasDerivAt G (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) (hd : ∀ x ∈ Icc a b, E' x ≤ 2 * g x * √(E x)) :
    ∀ x ∈ Icc a b, √(E x) ≤ √(E a) + (G x - G a) := by
  intro x hx
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set ε := (δ / 2) ^ 2 with hε
  have hεpos : 0 < ε := by positivity
  set φ : ℝ → ℝ := fun y => √(E y + ε) - G y with hφ
  have hφd : ∀ y ∈ Icc a b, HasDerivAt φ (E' y / (2 * √(E y + ε)) - g y) y := by
    intro y hy
    have hpos : 0 < E y + ε := by linarith [hE0 y hy]
    exact (((hE y hy).add_const ε).sqrt hpos.ne').sub (hG y hy)
  have hanti : AntitoneOn φ (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · exact fun y hy => (hφd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun y hy => (hφd y (Ioo_subset_Icc_self hy)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      have hy' := Ioo_subset_Icc_self hy
      rw [(hφd y hy').deriv]
      have hpos : 0 < E y + ε := by linarith [hE0 y hy']
      have hs : 0 < √(E y + ε) := Real.sqrt_pos.mpr hpos
      have hle : √(E y) ≤ √(E y + ε) := Real.sqrt_le_sqrt (by linarith)
      have h1 := hd y hy'
      have h2 : 2 * g y * √(E y) ≤ 2 * g y * √(E y + ε) := by
        have := hg y hy'
        gcongr
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      linarith
  have hφx := hanti ha hx hx.1
  simp only [hφ] at hφx
  have h1 : √(E x) ≤ √(E x + ε) := Real.sqrt_le_sqrt (by linarith)
  have h2 : √(E a + ε) ≤ √(E a) + δ / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt (hE0 a ha)
    have := Real.sqrt_nonneg (E a)
    nlinarith
  linarith

/-- The energy for `κ ≥ 0`. -/
noncomputable def energy0 (κ x p q p' q' : ℝ) : ℝ :=
  (p' - q) ^ 2 + (q' + p) ^ 2 + (1 + κ / x ^ 2) * (p ^ 2 + q ^ 2)

/-- The energy for `κ < 0`. -/
noncomputable def energy1 (κ x p q p' q' : ℝ) : ℝ :=
  ((p' - q) ^ 2 + (q' + p) ^ 2) / (1 + κ / x ^ 2) + p ^ 2 + q ^ 2

/-- The hypotheses on the errors `p`, `q` with derivatives `p'`, `q'` on `[a, b]`. -/
structure ErrorSystem (κ a b : ℝ) (p q p' q' r₁ r₂ : ℝ → ℝ) : Prop where
  pos : 0 < a
  hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x
  hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x
  hp' : ∀ x ∈ Icc a b, HasDerivAt p' (2 * q' x - κ / x ^ 2 * p x - r₁ x) x
  hq' : ∀ x ∈ Icc a b, HasDerivAt q' (-2 * p' x - κ / x ^ 2 * q x - r₂ x) x

theorem hasDerivAt_kappa (κ x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => 1 + κ / y ^ 2) (-2 * κ / x ^ 3) x := by
  have h := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)).const_mul κ |>.const_add 1
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
    simp [div_eq_mul_inv])
  field_simp
  ring

theorem energy0_bound {κ a b : ℝ} {p q p' q' r₁ r₂ G g : ℝ → ℝ}
    (hs : ErrorSystem κ a b p q p' q' r₁ r₂) (hκ : 0 ≤ κ)
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (g x) x) (hg : ∀ x ∈ Icc a b, |r₁ x| + |r₂ x| ≤ g x) :
    ∀ x ∈ Icc a b, √(energy0 κ x (p x) (q x) (p' x) (q' x)) ≤
      √(energy0 κ a (p a) (q a) (p' a) (q' a)) + (G x - G a) := by
  refine sqrt_le_of_deriv (E := fun x => energy0 κ x (p x) (q x) (p' x) (q' x))
    (E' := fun x => -2 * (r₁ x * (p' x - q x) + r₂ x * (q' x + p x)) +
      -2 * κ / x ^ 3 * (p x ^ 2 + q x ^ 2)) ?_ ?_ hG
    (fun x hx => (abs_nonneg _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans (hg x hx))) ?_
  · intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hs.pos hx.1).ne'
    have h := ((((hs.hp' x hx).sub (hs.hq x hx)).pow 2).add (((hs.hq' x hx).add (hs.hp x hx)).pow 2)).add
      ((hasDerivAt_kappa κ x hx0).mul (((hs.hp x hx).pow 2).add ((hs.hq x hx).pow 2)))
    refine h.congr_deriv ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    push_cast
    ring
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs.pos hx.1
    unfold energy0
    have : 0 ≤ κ / x ^ 2 := by positivity
    positivity
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs.pos hx.1
    set u := p' x - q x
    set v := q' x + p x
    have hE : u ^ 2 + v ^ 2 ≤ energy0 κ x (p x) (q x) (p' x) (q' x) := by
      unfold energy0
      have : 0 ≤ κ / x ^ 2 := by positivity
      nlinarith [sq_nonneg (p x), sq_nonneg (q x)]
    have hu : |u| ≤ √(energy0 κ x (p x) (q x) (p' x) (q' x)) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg v])
    have hv : |v| ≤ √(energy0 κ x (p x) (q x) (p' x) (q' x)) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg u])
    have hκx : -2 * κ / x ^ 3 * (p x ^ 2 + q x ^ 2) ≤ 0 := by
      have : 0 ≤ κ / x ^ 3 * (p x ^ 2 + q x ^ 2) := by positivity
      have e : -2 * κ / x ^ 3 * (p x ^ 2 + q x ^ 2) = -2 * (κ / x ^ 3 * (p x ^ 2 + q x ^ 2)) := by ring
      linarith
    have h1 : -(r₁ x * u) ≤ |r₁ x| * √(energy0 κ x (p x) (q x) (p' x) (q' x)) := by
      have := neg_abs_le (r₁ x * u)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (r₁ x), mul_le_mul_of_nonneg_left hu (abs_nonneg (r₁ x))]
    have h2 : -(r₂ x * v) ≤ |r₂ x| * √(energy0 κ x (p x) (q x) (p' x) (q' x)) := by
      have := neg_abs_le (r₂ x * v)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (r₂ x), mul_le_mul_of_nonneg_left hv (abs_nonneg (r₂ x))]
    have hgx := hg x hx
    have hsq := Real.sqrt_nonneg (energy0 κ x (p x) (q x) (p' x) (q' x))
    nlinarith [mul_le_mul_of_nonneg_right hgx hsq]

theorem energy1_bound {κ a b : ℝ} {p q p' q' r₁ r₂ G g : ℝ → ℝ}
    (hs : ErrorSystem κ a b p q p' q' r₁ r₂) (hκ : κ ≤ 0)
    (hm : ∀ x ∈ Icc a b, 81 / 100 ≤ 1 + κ / x ^ 2)
    (hG : ∀ x ∈ Icc a b, HasDerivAt G (g x) x)
    (hg : ∀ x ∈ Icc a b, 10 / 9 * (|r₁ x| + |r₂ x|) ≤ g x) :
    ∀ x ∈ Icc a b, √(energy1 κ x (p x) (q x) (p' x) (q' x)) ≤
      √(energy1 κ a (p a) (q a) (p' a) (q' a)) + (G x - G a) := by
  refine sqrt_le_of_deriv (E := fun x => energy1 κ x (p x) (q x) (p' x) (q' x))
    (E' := fun x => -2 * (r₁ x * (p' x - q x) + r₂ x * (q' x + p x)) / (1 + κ / x ^ 2) -
      ((p' x - q x) ^ 2 + (q' x + p x) ^ 2) * (-2 * κ / x ^ 3) / (1 + κ / x ^ 2) ^ 2) ?_ ?_ hG
    (fun x hx => le_trans (by positivity) (hg x hx)) ?_
  · intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hs.pos hx.1).ne'
    have hmx : 1 + κ / x ^ 2 ≠ 0 := by linarith [hm x hx]
    have h := (((((hs.hp' x hx).sub (hs.hq x hx)).pow 2).add
      (((hs.hq' x hx).add (hs.hp x hx)).pow 2)).div (hasDerivAt_kappa κ x hx0) hmx).add
      (((hs.hp x hx).pow 2).add ((hs.hq x hx).pow 2))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
      simp only [energy1, Pi.add_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply]; ring)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    have hmx2 : x ^ 2 + κ ≠ 0 := by
      intro h0
      apply hmx
      rw [show 1 + κ / x ^ 2 = (x ^ 2 + κ) / x ^ 2 by field_simp, h0, zero_div]
    field_simp
    ring
  · intro x hx
    have hmx : 0 < 1 + κ / x ^ 2 := by linarith [hm x hx]
    unfold energy1
    positivity
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs.pos hx.1
    have hm81 := hm x hx
    set m := 1 + κ / x ^ 2 with hmdef
    have hmpos : 0 < m := by linarith
    set u := p' x - q x
    set v := q' x + p x
    set E := energy1 κ x (p x) (q x) (p' x) (q' x) with hEdef
    have hE : (u ^ 2 + v ^ 2) / m ≤ E := by
      rw [hEdef]
      unfold energy1
      nlinarith [sq_nonneg (p x), sq_nonneg (q x)]
    have hsE := Real.sqrt_nonneg E
    have hE0 : 0 ≤ E := le_trans (by positivity) hE
    have hEsq : E = √E ^ 2 := (Real.sq_sqrt hE0).symm
    have hmE : 0 ≤ m * E * (100 / 81 * m - 1) :=
      mul_nonneg (mul_nonneg hmpos.le hE0) (by linarith)
    have hu2 : u ^ 2 ≤ m * E := by
      have := (div_le_iff₀ hmpos).mp hE
      nlinarith [sq_nonneg v]
    have hv2 : v ^ 2 ≤ m * E := by
      have := (div_le_iff₀ hmpos).mp hE
      nlinarith [sq_nonneg u]
    have hum : |u| ≤ m * (10 / 9 * √E) := by
      refine (sq_le_sq₀ (abs_nonneg u) (by positivity)).mp ?_
      rw [sq_abs, mul_pow, mul_pow, ← hEsq]
      nlinarith
    have hvm : |v| ≤ m * (10 / 9 * √E) := by
      refine (sq_le_sq₀ (abs_nonneg v) (by positivity)).mp ?_
      rw [sq_abs, mul_pow, mul_pow, ← hEsq]
      nlinarith
    have hk : 0 ≤ (u ^ 2 + v ^ 2) * (-2 * κ / x ^ 3) / m ^ 2 := by
      have : 0 ≤ -2 * κ / x ^ 3 := by
        apply div_nonneg (by linarith) (by positivity)
      positivity
    have hr : -2 * (r₁ x * u + r₂ x * v) / m ≤ 2 * (10 / 9 * (|r₁ x| + |r₂ x|)) * √E := by
      rw [div_le_iff₀ hmpos]
      have h1 : -(r₁ x * u) ≤ |r₁ x| * (m * (10 / 9 * √E)) := by
        have := neg_abs_le (r₁ x * u)
        rw [abs_mul] at this
        nlinarith [mul_le_mul_of_nonneg_left hum (abs_nonneg (r₁ x))]
      have h2 : -(r₂ x * v) ≤ |r₂ x| * (m * (10 / 9 * √E)) := by
        have := neg_abs_le (r₂ x * v)
        rw [abs_mul] at this
        nlinarith [mul_le_mul_of_nonneg_left hvm (abs_nonneg (r₂ x))]
      nlinarith
    have hgx := hg x hx
    have : 2 * (10 / 9 * (|r₁ x| + |r₂ x|)) * √E ≤ 2 * g x * √E := by
      have := mul_le_mul_of_nonneg_right hgx hsE
      linarith
    show -2 * (r₁ x * u + r₂ x * v) / m - (u ^ 2 + v ^ 2) * (-2 * κ / x ^ 3) / m ^ 2 ≤ 2 * g x * √E
    linarith

#print axioms energy0_bound
#print axioms energy1_bound

end LeanExe.ProofKit.BesselEnergy
