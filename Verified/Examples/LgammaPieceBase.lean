import LeanExe.ProofKit.GammaRel
import Verified.Examples.GammaPi
import Verified.Examples.Lgamma
import Verified.Examples.TgammaFactsBase

/-!
The data of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]` (`lgamma.c` lines 759-870 and
990-1008, commit `ff2f71f6`), read from the port's `Lgamma.mainTable` in the forms of the
floating-point proof's statements (`LgammaApprox` on branch `w/expm1`): the borders `ubrd` at words
0 to 19, as the top 27 bits of a double, the offsets `offs` at 20 to 38, the doubles `cl` in rows of
8 from 39, and the double-double `ch` in rows of 5 pairs from 191.  Piece `j` evaluates `pieceP j`
at `x - off j`: `polydddfst` adds `z · (cl [0] + ⋯)` to the coefficient of degree 4, so the
coefficients are the five `ch` and then the eight `cl`.  The bounds hold on the piece widened by
`2 ^ -50` at each end, `[lo j, lo j + 8 rr j]`, since the code selects the piece from a rounded
argument.  `sub_bound` turns a kernel check `GammaRel.lgammaRelOk` on sub-piece `k` of radius
`rr j` into the relative bound `2 ^ -63` there, with `π` within `2 ^ -128` (`GammaPi`).  The pieces
4 and 10, which contain the zeros 1 and 2, carry the factors `1 - x` and `x - 2` and are bounded
elsewhere.
-/

namespace Verified.Examples.LgammaPieceBase

open Real LeanExe.ProofKit PolyBound TaylorModel GammaModels GammaFits GammaRel GammaThresholds
  TgammaFactsBase

/-- The left border of piece `j`: `ubrd [j]` as the top bits of a double. -/
def border (j : ℕ) : ℚ := ratOfWord (Lgamma.mainTable[j]! <<< 37)

/-- The offset of piece `j`. -/
def off (j : ℕ) : ℚ := q Lgamma.mainTable (20 + j)

/-- The polynomial of piece `j` in `z = x - off j`. -/
def pieceP (j : ℕ) : List ℚ :=
  ddCoeffs Lgamma.mainTable (191 + 10 * j) 5 ++ coeffs Lgamma.mainTable (39 + 8 * j) 1 8

/-- The left end of piece `j` widened by `2 ^ -50`. -/
def lo (j : ℕ) : ℚ := border j - 1 / 2 ^ 50

/-- The radius of the four sub-pieces of piece `j` widened by `2 ^ -50` at each end. -/
def rr (j : ℕ) : ℚ := (border (j + 1) - border j + 2 / 2 ^ 50) / 8

/-- The Taylor-model parameters for piece `j`: degree 18, 100 bits, at most 60 terms with factor
below `2 ^ -100`, and `π` within `2 ^ -128`. -/
def cfgJ (j : ℕ) : Cfg := ⟨rr j, 18, 100, 60, 1 / 2 ^ 100, GammaPi.piLo128, GammaPi.piHi128⟩

theorem cfgJ_pi (j : ℕ) : ((cfgJ j).piLo : ℝ) ≤ π ∧ π ≤ (cfgJ j).piHi := GammaPi.pi_bounds128

/-- Sub-piece `k` of piece `j` with `n` shifts. -/
def sub (j k n : ℕ) (ly lp : LogData) : LgData :=
  ⟨lo j + rr j * (2 * k + 1), n, log2Lo, log2Hi, ly, lp⟩

/-- The inner and outer relative bounds of the checks. -/
def εin : ℚ := 31 / 32 / 2 ^ 63

def εout : ℚ := 1 / 2 ^ 63

theorem sub_bound (j k n : ℕ) (ly lp : LogData) (σ m0 : ℚ) (depth : ℕ)
    (h : lgammaRelOk (cfgJ j) (sub j k n ly lp)
      (PolyBound.shift (lo j + rr j * (2 * k + 1) - off j) (pieceP j)) σ εin εout m0 depth = true)
    (t : ℝ) (ht : |t| ≤ (rr j : ℝ)) :
    |GammaBasic.lgamma ((lo j : ℝ) + rr j * (2 * k + 1) + t) -
        eval (pieceP j) ((lo j : ℝ) + rr j * (2 * k + 1) + t - off j)| ≤
      εout * |GammaBasic.lgamma ((lo j : ℝ) + rr j * (2 * k + 1) + t)| := by
  have hb := lgammaRelOk_sound (cfgJ j) _ _ σ εin εout m0 depth (cfgJ_pi j) h (t := t) ht
  rw [eval_shift] at hb
  simp only [sub] at hb
  push_cast at hb
  convert hb using 4
  ring

/-- The relative bound on piece `j`, widened by `2 ^ -50` at each end, from the bounds on its four
sub-pieces. -/
theorem piece_of_subs (j : ℕ) (hr : 0 < rr j)
    (h : ∀ k : ℕ, k < 4 → ∀ t : ℝ, |t| ≤ (rr j : ℝ) →
      |GammaBasic.lgamma ((lo j : ℝ) + rr j * (2 * k + 1) + t) -
          eval (pieceP j) ((lo j : ℝ) + rr j * (2 * k + 1) + t - off j)| ≤
        εout * |GammaBasic.lgamma ((lo j : ℝ) + rr j * (2 * k + 1) + t)|) :
    ∀ x : ℝ, (border j : ℝ) - 1 / 2 ^ 50 ≤ x → x ≤ (border (j + 1) : ℝ) + 1 / 2 ^ 50 →
      |GammaBasic.lgamma x - eval (pieceP j) (x - off j)| ≤ εout * |GammaBasic.lgamma x| := by
  intro x hlo hhi
  have hrr : (0 : ℝ) < rr j := by exact_mod_cast hr
  have hl : ((lo j : ℚ) : ℝ) = (border j : ℝ) - 1 / 2 ^ 50 := by
    simp only [lo]
    push_cast
    ring
  have hw : (border (j + 1) : ℝ) + 1 / 2 ^ 50 = (lo j : ℝ) + 2 * rr j * 4 := by
    simp only [lo, rr]
    push_cast
    ring
  exact cover_pieces (K := 4) (by norm_num) hrr
    (fun x => |GammaBasic.lgamma x - eval (pieceP j) (x - off j)| ≤ εout * |GammaBasic.lgamma x|)
    h x (by rw [hl]; exact hlo) (by rw [hw] at hhi; push_cast; linarith)

#print axioms sub_bound
#print axioms piece_of_subs

end Verified.Examples.LgammaPieceBase
