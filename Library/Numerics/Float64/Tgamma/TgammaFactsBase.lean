import LeanExe.ProofKit.GammaFits
import Library.Numerics.Float64.Tgamma.Compiled

/-!
The coefficient lists of CORE-MATH's `tgamma` approximations, read from the port's tables in the
forms of the floating-point proof's statements (`TgammaApprox` on branch `w/poly`): `q tab i` is the
exact rational value of entry `i`, `coeffs tab o s n` lists the entries `o, o + s, …`, and `ddCoeffs
tab o n` the double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]`.  The fact modules
`TgammaPolyMain`, `TgammaPolySmall`, `TgammaPolySmallAcc`, and `TgammaAsymFit` bound these
polynomials against `Γ` and `log Γ`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaFactsBase

open LeanExe.ProofKit PolyBound

/-- The exact rational value of entry `i` of `tab`. -/
def q (tab : Array UInt64) (i : ℕ) : ℚ := ratOfWord tab[i]!

/-- The entries `o + s k` of `tab` for `k < n`. -/
def coeffs (tab : Array UInt64) (o s n : ℕ) : List ℚ :=
  (List.range n).map fun k => q tab (o + s * k)

/-- The double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]` for `k < n`. -/
def ddCoeffs (tab : Array UInt64) (o n : ℕ) : List ℚ :=
  (List.range n).map fun k => q tab (o + 2 * k) + q tab (o + 2 * k + 1)

/-- The polynomial of `tgammaWith` below `1/4`: `Γ x ≈ 1/x + eval smallList x`. -/
def smallList : List ℚ := ddCoeffs Tgamma.smallTable 0 5 ++ coeffs Tgamma.smallTable 10 1 16

/-- The polynomial of `tgammaWith` on `[-3, 4]`: `Γ (7/2 + d) ≈ eval mainList d`. -/
def mainList : List ℚ := ddCoeffs Tgamma.mainTable 0 10 ++ coeffs Tgamma.mainTable 46 1 8

/-- The polynomial of `Tgamma.accurate` below `1/4`: `Γ x ≈ 1/x + eval accSmallList x`. -/
def accSmallList : List ℚ :=
  ddCoeffs Tgamma.accurateTable 0 28 ++ coeffs Tgamma.accurateTable 56 1 8

/-- `C0` and `P` of `asLgammaAsym` above 11.5. -/
def c0Hi : ℚ := q Tgamma.asymTable 0 + q Tgamma.asymTable 1

def stirHiList : List ℚ :=
  (q Tgamma.asymTable 2 + q Tgamma.asymTable 3) :: coeffs Tgamma.asymTable 4 2 6

/-- `C0` and `P` of `asLgammaAsym` at or below 11.5. -/
def c0Lo : ℚ := q Tgamma.asymTable 16 + q Tgamma.asymTable 17

def stirLoList : List ℚ :=
  (q Tgamma.asymTable 18 + q Tgamma.asymTable 19) ::
    (q Tgamma.asymTable 20 + q Tgamma.asymTable 21) :: coeffs Tgamma.asymTable 22 2 10

/-- `1 + x Q x` as a coefficient list. -/
def onePlusX (Q : List ℚ) : List ℚ := addP [1] (0 :: Q)

theorem eval_onePlusX (Q : List ℚ) (x : ℝ) : eval (onePlusX Q) x = 1 + x * eval Q x := by
  rw [onePlusX, eval_addP]
  simp

#print axioms eval_onePlusX

end Library.Numerics.Float64.Tgamma.TgammaFactsBase
