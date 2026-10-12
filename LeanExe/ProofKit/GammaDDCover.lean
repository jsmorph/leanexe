import LeanExe.ProofKit.GammaConvex

/-!
Bounds on the divided difference `g s = (lgamma (x0 + s) - lgamma x0)/s` against a function `Q` on
an interval that contains 0, for the polynomials next to the zeros of `lgamma`.  Kernel checks of
Taylor models bound `g - Q` for `|s| ≥ τ`, where Stirling's remainder divided by `s` stays small,
and the convexity of `lgamma` (`GammaConvex.dd_center`) covers `|s| < τ` with the variation `V` of
`Q` there: `dd_abs_fact` gives the absolute bound `ε + 2 V` on the whole interval, and
`dd_rel_center` turns relative bounds at `±τ` into a relative bound between them, which
`dd_rel_fact` joins with relative bounds for `|s| ≥ τ`.
-/

namespace LeanExe.ProofKit.GammaDDCover

open Real GammaBasic GammaConvex

/-- The absolute bound on the divided difference over `[lo, hi] ∋ 0`. -/
theorem dd_abs_fact {x0 lo hi τ ε V : ℝ} (hx0 : 0 < x0) (hτ : 0 < τ) (hτx : τ < x0)
    (hlo : lo ≤ -τ) (hhi : τ ≤ hi) (Q : ℝ → ℝ)
    (hneg : ∀ s, lo ≤ s → s ≤ -τ → |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ ε)
    (hpos : ∀ s, τ ≤ s → s ≤ hi → |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ ε)
    (hV : ∀ s, |s| ≤ τ → |Q s - Q 0| ≤ V) :
    ∀ s, lo ≤ s → s ≤ hi → s ≠ 0 → |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ ε + 2 * V := by
  intro s h1 h2 hs0
  have hV0 : 0 ≤ V := by
    have := hV 0 (by rw [abs_zero]; exact hτ.le)
    rw [sub_self, abs_zero] at this
    exact this
  rcases le_or_gt s (-τ) with h | h
  · linarith [hneg s h1 h]
  rcases le_or_gt τ s with h' | h'
  · linarith [hpos s h' h2]
  exact dd_center hx0 hτ hτx Q hV (hpos τ le_rfl hhi) (hneg (-τ) hlo le_rfl) hs0
    (abs_le.mpr ⟨h.le, h'.le⟩)

/-- Relative bounds at `±τ` give a relative bound between them, when `g` keeps its sign there:
`g τ ≤ -m` or `m ≤ g (-τ)`. -/
theorem dd_rel_center {x0 τ εr V m M : ℝ} (hx0 : 0 < x0) (hτ : 0 < τ) (hτx : τ < x0)
    (hm0 : 0 < m) (Q : ℝ → ℝ) (hV : ∀ s, |s| ≤ τ → |Q s - Q 0| ≤ V)
    (hp : |(lgamma (x0 + τ) - lgamma x0) / τ - Q τ| ≤ εr * |(lgamma (x0 + τ) - lgamma x0) / τ|)
    (hm : |(lgamma (x0 + -τ) - lgamma x0) / -τ - Q (-τ)| ≤
      εr * |(lgamma (x0 + -τ) - lgamma x0) / -τ|)
    (hεr : 0 ≤ εr)
    (hMp : |(lgamma (x0 + τ) - lgamma x0) / τ| ≤ M)
    (hMm : |(lgamma (x0 + -τ) - lgamma x0) / -τ| ≤ M)
    (hsgn : (lgamma (x0 + τ) - lgamma x0) / τ ≤ -m ∨ m ≤ (lgamma (x0 + -τ) - lgamma x0) / -τ)
    {s : ℝ} (hs0 : s ≠ 0) (hs : |s| ≤ τ) :
    |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤
      (εr * M + 2 * V) / m * |(lgamma (x0 + s) - lgamma x0) / s| := by
  have hsl := abs_le.mp hs
  have hb := dd_center hx0 hτ hτx Q hV (hp.trans (mul_le_mul_of_nonneg_left hMp hεr))
    (hm.trans (mul_le_mul_of_nonneg_left hMm hεr)) hs0 hs
  have g1 := dd_mono (s1 := -τ) (s2 := s) hx0 (by linarith) (by linarith)
    (neg_ne_zero.mpr hτ.ne') hs0 hsl.1
  have g2 := dd_mono (s1 := s) (s2 := τ) hx0 (by linarith) (by linarith) hs0 hτ.ne' hsl.2
  have hlow : m ≤ |(lgamma (x0 + s) - lgamma x0) / s| := by
    rcases hsgn with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hnum : 0 ≤ εr * M + 2 * V := by
    have hV0 : 0 ≤ V := by
      have := hV 0 (by rw [abs_zero]; exact hτ.le)
      rw [sub_self, abs_zero] at this
      exact this
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hMp
    exact add_nonneg (mul_nonneg hεr hM0) (by linarith)
  calc |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ εr * M + 2 * V := hb
    _ = (εr * M + 2 * V) / m * m := (div_mul_cancel₀ _ hm0.ne').symm
    _ ≤ (εr * M + 2 * V) / m * |(lgamma (x0 + s) - lgamma x0) / s| :=
        mul_le_mul_of_nonneg_left hlow (div_nonneg hnum hm0.le)

/-- Relative bounds for `|s| ≥ τ`, a bound `Qm` on `|Q|` at `±τ`, and the sign of `Q` there give
a relative bound on the whole interval, `0` excluded, through `dd_rel_center`. -/
theorem dd_rel_fact {x0 lo hi τ ε εf V m M Qm : ℝ} (hx0 : 0 < x0) (hτ : 0 < τ) (hτx : τ < x0)
    (hlo : lo ≤ -τ) (hhi : τ ≤ hi) (hm0 : 0 < m) (hε : 0 ≤ ε) (hε1 : ε < 1) (Q : ℝ → ℝ)
    (hneg : ∀ s, lo ≤ s → s ≤ -τ →
      |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ ε * |(lgamma (x0 + s) - lgamma x0) / s|)
    (hpos : ∀ s, τ ≤ s → s ≤ hi →
      |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ ε * |(lgamma (x0 + s) - lgamma x0) / s|)
    (hV : ∀ s, |s| ≤ τ → |Q s - Q 0| ≤ V) (hQp : |Q τ| ≤ Qm) (hQm : |Q (-τ)| ≤ Qm)
    (hM : Qm ≤ (1 - ε) * M) (hsgn : Q τ + ε * M ≤ -m ∨ m ≤ Q (-τ) - ε * M)
    (hεf : ε ≤ εf) (hfin : ε * M + 2 * V ≤ εf * m) :
    ∀ s, lo ≤ s → s ≤ hi → s ≠ 0 →
      |(lgamma (x0 + s) - lgamma x0) / s - Q s| ≤ εf * |(lgamma (x0 + s) - lgamma x0) / s| := by
  intro s h1 h2 hs0
  rcases le_or_gt s (-τ) with h | h
  · exact (hneg s h1 h).trans (mul_le_mul_of_nonneg_right hεf (abs_nonneg _))
  rcases le_or_gt τ s with h' | h'
  · exact (hpos s h' h2).trans (mul_le_mul_of_nonneg_right hεf (abs_nonneg _))
  have hp := hpos τ le_rfl hhi
  have hm := hneg (-τ) hlo le_rfl
  have hMp : |(lgamma (x0 + τ) - lgamma x0) / τ| ≤ M := by
    have h3 := abs_sub_abs_le_abs_sub ((lgamma (x0 + τ) - lgamma x0) / τ) (Q τ)
    nlinarith [abs_nonneg ((lgamma (x0 + τ) - lgamma x0) / τ)]
  have hMm : |(lgamma (x0 + -τ) - lgamma x0) / -τ| ≤ M := by
    have h3 := abs_sub_abs_le_abs_sub ((lgamma (x0 + -τ) - lgamma x0) / -τ) (Q (-τ))
    nlinarith [abs_nonneg ((lgamma (x0 + -τ) - lgamma x0) / -τ)]
  have hsgn' : (lgamma (x0 + τ) - lgamma x0) / τ ≤ -m ∨
      m ≤ (lgamma (x0 + -τ) - lgamma x0) / -τ := by
    rcases hsgn with hs | hs
    · left
      have h4 := (abs_le.mp hp).2
      have h5 := mul_le_mul_of_nonneg_left hMp hε
      linarith
    · right
      have h4 := (abs_le.mp hm).1
      have h5 := mul_le_mul_of_nonneg_left hMm hε
      linarith
  have hc := dd_rel_center hx0 hτ hτx hm0 Q hV hp hm hε hMp hMm hsgn' hs0
    (abs_le.mpr ⟨h.le, h'.le⟩)
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  rw [div_le_iff₀ hm0]
  exact hfin

#print axioms dd_abs_fact
#print axioms dd_rel_center
#print axioms dd_rel_fact

end LeanExe.ProofKit.GammaDDCover
