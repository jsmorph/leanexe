import LeanExe.ProofKit.PolyBound

/-!
Tools built on `PolyBound.check`: products of polynomials, bounds over a union of intervals,
one-sided bounds, and bounds against a weight.

`Bounded p lo hi ε` states `|eval p x| ≤ ε` on `[lo, hi]`.  `Covers p ε d lo hi ms` is a
conjunction of checks over the intervals that the breakpoints `ms` cut from `[lo, hi]`.  The kernel's
cost for one `decide +kernel` grows faster than the work, so each conjunct is proved as its own
declaration and the conjunction assembled from them.  `Bounded (addP p [M]) lo hi M` gives `p ≤ 0`
and `Bounded (subP p [M]) lo hi M` gives `0 ≤ p`.  Two such bounds on `A - ε W` and `A + ε W` give
`|A| ≤ ε W`, a relative error when `W` is the denominator of a rational approximation or the cosine
in `tan = sin/cos`.  `sub_div_le` turns `|f q - p| ≤ e q` into `|f - p/q| ≤ e` for positive `q`.
-/

namespace LeanExe.ProofKit.PolyChecks
open PolyBound

/-- The product of two polynomials. -/
def mulP : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => addP (scaleP a q) (0 :: mulP p q)

theorem eval_mulP (p q : List ℚ) (x : ℝ) : eval (mulP p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mulP]
  | cons a p ih =>
    simp only [mulP, eval_addP, eval_scaleP, eval_cons, ih, Rat.cast_zero]
    ring

/-- `|eval p x| ≤ ε` for every real `x` in `[lo, hi]`. -/
def Bounded (p : List ℚ) (lo hi ε : ℚ) : Prop :=
  ∀ x : ℝ, (lo : ℝ) ≤ x → x ≤ hi → |eval p x| ≤ ε

theorem bounded_of_check (p : List ℚ) (lo hi ε : ℚ) (d : Nat)
    (hc : check p lo hi ε d = true) : Bounded p lo hi ε :=
  fun x hlo hhi => check_sound p lo hi ε d hc x hlo hhi

/-- The checks over `[lo, m₁], [m₁, m₂], ..., [mₖ, hi]` for the breakpoints `m₁, ..., mₖ`. -/
def Covers (p : List ℚ) (ε : ℚ) (d : Nat) : ℚ → ℚ → List ℚ → Prop
  | lo, hi, [] => check p lo hi ε d = true
  | lo, hi, m :: ms => check p lo m ε d = true ∧ Covers p ε d m hi ms

theorem bounded_of_covers (p : List ℚ) (ε : ℚ) (d : Nat) (ms : List ℚ) :
    ∀ lo hi : ℚ, Covers p ε d lo hi ms → Bounded p lo hi ε := by
  induction ms with
  | nil => exact fun lo hi hc => bounded_of_check p lo hi ε d hc
  | cons m ms ih =>
    intro lo hi hc x hlo hhi
    rcases le_total x (m : ℝ) with hm | hm
    · exact check_sound p lo m ε d hc.1 x hlo hm
    · exact ih m hi hc.2 x hm hhi

theorem nonpos_of_bounded (p : List ℚ) (lo hi M : ℚ) (hb : Bounded (addP p [M]) lo hi M)
    (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) : eval p x ≤ 0 := by
  have h := hb x hlo hhi
  rw [eval_addP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have := (abs_le.mp h).2
  linarith

theorem nonneg_of_bounded (p : List ℚ) (lo hi M : ℚ) (hb : Bounded (subP p [M]) lo hi M)
    (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) : 0 ≤ eval p x := by
  have h := hb x hlo hhi
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have := (abs_le.mp h).1
  linarith

/-- `|A| ≤ ε W` on `[lo, hi]` from bounds showing `A - ε W ≤ 0` and `A + ε W ≥ 0`. -/
theorem abs_le_weighted (A W : List ℚ) (ε lo hi M N : ℚ)
    (hu : Bounded (addP (subP A (scaleP ε W)) [M]) lo hi M)
    (hl : Bounded (subP (addP A (scaleP ε W)) [N]) lo hi N)
    (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) : |eval A x| ≤ ε * eval W x := by
  have h1 := nonpos_of_bounded _ _ _ _ hu x hlo hhi
  have h2 := nonneg_of_bounded _ _ _ _ hl x hlo hhi
  rw [eval_subP, eval_scaleP] at h1
  rw [eval_addP, eval_scaleP] at h2
  rw [abs_le]
  constructor <;> linarith

theorem sub_div_le (f p q e : ℝ) (hq : 0 < q) (h : |f * q - p| ≤ e * q) : |f - p / q| ≤ e := by
  have he : f - p / q = (f * q - p) / q := by field_simp
  rw [he, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  exact h

#print axioms eval_mulP
#print axioms bounded_of_covers
#print axioms nonpos_of_bounded
#print axioms nonneg_of_bounded
#print axioms abs_le_weighted
#print axioms sub_div_le

end LeanExe.ProofKit.PolyChecks
