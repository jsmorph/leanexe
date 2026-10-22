import Library.Numerics.Float64.Lgamma.Program
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.GammaBasic

/-!
The approximation statements that the floating-point proof of `Lgamma.lgammaR` takes as
hypotheses.  Each statement compares a real function built from the words of `Lgamma`'s and
`Tgamma`'s tables with `GammaBasic.lgamma` (`log |Γ|`), `Real.log`, `Real.sin`, `Real.cos`, or
`Real.pi`, and involves no floating-point operation, except `CancelFact`, which bounds the
cancellation of the reflection at the doubles from `-21/2` down.  `q tab i` is the exact rational value of entry `i` of
`tab`, `coeffs tab o s n` lists the entries `o, o + s, …, o + s (n - 1)`, and `ddCoeffs tab o n`
lists the double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]`.  A polynomial is a
coefficient list, lowest degree first, evaluated by `PolyBound.eval`.

The functions follow the code with exact arithmetic.  The fast path's are `smallPoly` below
`2^-5`, the 19 pieces `pieceApprox` from 0.5 to 8.29541 (the pieces that contain the zeros 1 and 2
carry the factors `1 - x` and `x - 2`), `stirFast` above, the kernels and tables of `asLogd`
(`LogFact`, the statement of `Library.Numerics.Float64.Tgamma.TgammaApprox.LogFact`), and those of `asSinpipid` (`SinpiFact`).  The
accurate path's are `accSmallPoly` and `accMidPoly` near 1 and 3/2, `asymAcc` for Stirling's series,
the kernels and tables of `asLogdAccurate` and `asSinpipidAccurate`, the 17 polynomials about the
zeros of `log |Γ|` from -10.5 to -2 (`rootRanges`), with an absolute term `2^-120` that covers
the distance between each stored center and the zero, and the smallest `|log |Γ|` at the doubles
of those ranges (`RootMinFact`), and the 19 hard cases (`DbFact`).

The tolerances leave a factor over the errors that a 70-to-90-digit evaluation with Python's
`decimal` module found at dense sample points: about 1.5 for the pieces (measured `7.96 · 10^-20`
relative against `12 · 10^-20`) and 1.6 for `stirFast` (`4.34 · 10^-20` against `7 · 10^-20`), the
two facts that the rounding test of the fast path needs within about twice CORE-MATH's `eps`, and
at least 2 for the others.  From -17 to -21/2 the accurate path's reflection
`-(log Γ (1 - x) + log (sin (π φ)/π))` cancels by up to `2^31.04`, next to the zero at
`-10.99999997494789`, so `asymAcc` on `[15/4, 48]` and the kernels and tables of the accurate
logarithm and sine carry about `2^-87` relative, and `CancelFact` bounds the cancellation by `2^32`.
Elsewhere the accurate path needs about `2^-63` after a cancellation of at most `2^8`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaApprox
open LeanExe.ProofKit PolyBound GammaBasic

/-- The exact rational value of entry `i` of `tab`. -/
def q (tab : Array UInt64) (i : ℕ) : ℚ := ratOfWord tab[i]!

/-- The entries `o + s k` of `tab` for `k < n`. -/
def coeffs (tab : Array UInt64) (o s n : ℕ) : List ℚ := (List.range n).map fun k => q tab (o + s * k)

/-- The double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]` for `k < n`. -/
def ddCoeffs (tab : Array UInt64) (o n : ℕ) : List ℚ :=
  (List.range n).map fun k => q tab (o + 2 * k) + q tab (o + 2 * k + 1)

/-! ### The fast path -/

/-- The polynomial below `2^-5`: `log Γ (1 + x) ≈ x · smallPoly x`. -/
noncomputable def smallPoly : ℝ → ℝ :=
  eval (ddCoeffs Lgamma.mainTable 381 4 ++ coeffs Lgamma.mainTable 389 1 8)

def SmallFact : Prop :=
  ∀ x : ℝ, |x| ≤ 1 / 32 → |GammaBasic.lgamma (1 + x) - x * smallPoly x| ≤ 1 / 2 ^ 70 * |x|

/-- The border `j ≤ 19` of the pieces, the double whose top bits are `ubrd j`. -/
def border (j : ℕ) : ℚ := ratOfWord (Lgamma.mainTable[j]! <<< 37)

/-- The offset of piece `j`. -/
def offs (j : ℕ) : ℚ := q Lgamma.mainTable (20 + j)

/-- The polynomial of piece `j`: five double-double coefficients and eight doubles. -/
noncomputable def piecePoly (j : ℕ) : ℝ → ℝ :=
  eval (ddCoeffs Lgamma.mainTable (191 + 10 * j) 5 ++ coeffs Lgamma.mainTable (39 + 8 * j) 1 8)

/-- The approximation of `log |Γ x|` on piece `j`, with the factor `1 - x` on the piece that
contains 1 and `x - 2` on the piece that contains 2. -/
noncomputable def pieceApprox (j : ℕ) (x : ℝ) : ℝ :=
  (if j = 4 then 1 - x else if j = 10 then x - 2 else 1) * piecePoly j (x - offs j)

def PieceFact : Prop :=
  ∀ j < 19, ∀ x : ℝ, (border j : ℝ) - 1 / 2 ^ 50 ≤ x → x ≤ (border (j + 1) : ℝ) + 1 / 2 ^ 50 →
    |GammaBasic.lgamma x - pieceApprox j x| ≤ 12 / 10 ^ 20 * |GammaBasic.lgamma x|

/-- Stirling's series from 8.29541 on: `(x - 1/2) (log x - 1) + c + S (1/x²)/x`. -/
noncomputable def stirFast (x : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log x - 1) + ((q Lgamma.mainTable 397 + q Lgamma.mainTable 398 : ℚ) : ℝ) +
    1 / x * eval ((q Lgamma.mainTable 399 + q Lgamma.mainTable 400) ::
      coeffs Lgamma.mainTable 401 1 5) (1 / x ^ 2)

def StirlingFact : Prop :=
  ∀ x : ℝ, (border 19 : ℝ) - 1 / 2 ^ 40 ≤ x → |GammaBasic.lgamma x - stirFast x| ≤ 7 / 10 ^ 20 * GammaBasic.lgamma x

/-- The kernel of `asLogd`: `log (1 + z) ≈ z + z² logPoly z`. -/
noncomputable def logPoly : ℝ → ℝ := eval (coeffs Tgamma.logdTable 260 1 4)

/-- `asLogd`'s reciprocals `r1` (33 entries) and `r2` (32 entries). -/
def r1 (i : ℕ) : ℚ := q Tgamma.logdTable (64 + i)
def r2 (i : ℕ) : ℚ := q Tgamma.logdTable (97 + i)

/-- `asLogd`'s logarithms `l1 ≈ -log r1` and `l2 ≈ -log r2`, as double-doubles. -/
def l1 (i : ℕ) : ℚ := q Tgamma.logdTable (130 + 2 * i) + q Tgamma.logdTable (131 + 2 * i)
def l2 (i : ℕ) : ℚ := q Tgamma.logdTable (196 + 2 * i) + q Tgamma.logdTable (197 + 2 * i)

/-- `asLogd`'s `ln 2` as `0x1.62e42fef8p-1 + 0x1.1cf79abc9e3b4p-36`. -/
def ln2 : ℚ := ratOfWord 0x3FE62E42FEF80000 + ratOfWord 0x3DB1CF79ABC9E3B4

/-- The statement of `Library.Numerics.Float64.Tgamma.TgammaApprox.LogFact`, for the same table. -/
def LogFact : Prop :=
  (∀ z : ℝ, |z| ≤ 1 / 2400 → |Real.log (1 + z) - (z + z ^ 2 * logPoly z)| ≤ 1 / 2 ^ 70) ∧
    (∀ i < 33, |(l1 i : ℝ) + Real.log (r1 i)| ≤ 1 / 2 ^ 80) ∧
    (∀ i < 32, |(l2 i : ℝ) + Real.log (r2 i)| ≤ 1 / 2 ^ 80) ∧
    |(ln2 : ℝ) - Real.log 2| ≤ 1 / 2 ^ 80

/-- `as_sinpipid`'s table `stpi k ≈ sin (k π/128)/π` for `k ≤ 64`, as double-doubles. -/
def stpi (k : ℕ) : ℚ := q Lgamma.sinpiTable (2 * k) + q Lgamma.sinpiTable (2 * k + 1)

/-- The kernels of `Tgamma.asSinpid` with `Lgamma.sinpiTable`, in `w = d²`:
`sin (π d/128) ≈ d sinKernel w` and `cos (π d/128) ≈ 1 + w cosKernel w`, with the code's
corrections `s0` and `c0`. -/
noncomputable def sinKernel : ℝ → ℝ :=
  eval ((q Lgamma.sinpiTable 134 + ratOfWord 0x3C31A624B88C9448) :: coeffs Lgamma.sinpiTable 135 1 3)
noncomputable def cosKernel : ℝ → ℝ :=
  eval ((q Lgamma.sinpiTable 130 + ratOfWord 0xBBD692B66E3CF6E8) :: coeffs Lgamma.sinpiTable 131 1 3)

/-- The polynomial of `asSinpipid` within `3/256` of an integer: `sin (π z)/π ≈ z + z³ nearPoly z²`.
`SinpiFact` states it on `|z| ≤ 1/80`, which contains the computed `z = 0.5 - |x - 0.5|` of that
branch.  At `|z| = 1/64` its relative error reaches `2^-71.7`. -/
noncomputable def nearPoly : ℝ → ℝ :=
  eval ((q Lgamma.sinpiTable 138 + q Lgamma.sinpiTable 139) :: coeffs Lgamma.sinpiTable 140 1 3)

def SinpiFact : Prop :=
  (∀ k ≤ 64, |(stpi k : ℝ) - Real.sin (k * Real.pi / 128) / Real.pi| ≤ 1 / 2 ^ 100) ∧
    (∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.sin (Real.pi * d / 128) - d * sinKernel (d ^ 2)| ≤ 1 / 2 ^ 73 * |d|) ∧
    (∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * cosKernel (d ^ 2))| ≤ 1 / 2 ^ 76 * d ^ 2) ∧
    (∀ z : ℝ, |z| ≤ 1 / 80 →
      |Real.sin (Real.pi * z) / Real.pi - (z + z ^ 3 * nearPoly (z ^ 2))| ≤ 1 / 2 ^ 76 * |z|)

/-! ### The accurate path -/

/-- `as_lgamma_accurate`'s `c0`: `log Γ (1 + x) ≈ x · accSmallPoly x` for `|x| ≤ 1/4`. -/
noncomputable def accSmallPoly : ℝ → ℝ := eval (ddCoeffs Lgamma.accurateTable 0 34)

/-- `as_lgamma_accurate`'s `b`: `log Γ (3/2 + d) ≈ accMidPoly d` for `|d| ≤ 1/4`. -/
noncomputable def accMidPoly : ℝ → ℝ := eval (ddCoeffs Lgamma.accurateTable 68 30)

def AccPolyFact : Prop :=
  (∀ x : ℝ, |x| ≤ 1 / 4 → |GammaBasic.lgamma (1 + x) - x * accSmallPoly x| ≤ 1 / 2 ^ 70 * |x|) ∧
    ∀ d : ℝ, |d| ≤ 1 / 4 → |GammaBasic.lgamma (3 / 2 + d) - accMidPoly d| ≤ 1 / 2 ^ 70

/-- `as_lgamma_asym_accurate` with the constant at `o` and `n` coefficients after it. -/
noncomputable def asymAcc (o n : ℕ) (x : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log x - 1) + ((q Lgamma.asymTable o + q Lgamma.asymTable (o + 1) : ℚ) : ℝ) +
    1 / x * eval (ddCoeffs Lgamma.asymTable (o + 2) n) (1 / x ^ 2)

def AsymFact : Prop :=
  (∀ x : ℝ, 48 - 1 / 2 ^ 40 ≤ x → |GammaBasic.lgamma x - asymAcc 0 7 x| ≤ 1 / 2 ^ 63 * GammaBasic.lgamma x) ∧
    (∀ x : ℝ, 29 / 2 - 1 / 2 ^ 40 ≤ x → x ≤ 48 + 1 / 2 ^ 40 →
      |GammaBasic.lgamma x - asymAcc 16 11 x| ≤ 1 / 2 ^ 87 * GammaBasic.lgamma x) ∧
    ∀ x : ℝ, 15 / 4 - 1 / 2 ^ 40 ≤ x → x ≤ 29 / 2 + 1 / 2 ^ 40 →
      |GammaBasic.lgamma x - asymAcc 40 27 x| ≤ 1 / 2 ^ 87 * GammaBasic.lgamma x

/-- The kernel of `asLogdAccurate`: `log (1 + X) ≈ X · logAccPoly X`. -/
noncomputable def logAccPoly : ℝ → ℝ :=
  eval (ddCoeffs Lgamma.logAccurateTable 198 6 ++
    [q Lgamma.logAccurateTable 210, q Lgamma.logAccurateTable 212, q Lgamma.logAccurateTable 214])

/-- `asLogdAccurate`'s logarithms `h1 ≈ -log r1` and `h2 ≈ -log r2`, as triple-doubles. -/
def h1 (i : ℕ) : ℚ :=
  q Lgamma.logAccurateTable (3 * i) + q Lgamma.logAccurateTable (3 * i + 1) +
    q Lgamma.logAccurateTable (3 * i + 2)
def h2 (i : ℕ) : ℚ :=
  q Lgamma.logAccurateTable (99 + 3 * i) + q Lgamma.logAccurateTable (100 + 3 * i) +
    q Lgamma.logAccurateTable (101 + 3 * i)

/-- `asLogdAccurate`'s `ln 2` as `0x1.62e42fefa38p-1 + 0x1.ef35793c76p-45 + 0x1.cc01f97b57a08p-87`. -/
def ln2Acc : ℚ :=
  ratOfWord 0x3FE62E42FEFA3800 + ratOfWord 0x3D2EF35793C76000 + ratOfWord 0x3A8CC01F97B57A08

def LogAccFact : Prop :=
  (∀ X : ℝ, |X| ≤ 1 / 2400 → |Real.log (1 + X) - X * logAccPoly X| ≤ 1 / 2 ^ 80 * |X|) ∧
    (∀ i < 33, |(h1 i : ℝ) + Real.log (r1 i)| ≤ 1 / 2 ^ 96) ∧
    (∀ i < 32, |(h2 i : ℝ) + Real.log (r2 i)| ≤ 1 / 2 ^ 96) ∧
    |(ln2Acc : ℝ) - Real.log 2| ≤ 1 / 2 ^ 100

/-- The kernels of `asSinpipidAccurate` in `w = d²`: `cos (π d/128) ≈ 1 + w sinAccCos w` and
`sin (π d/128) ≈ d sinAccSin w`. -/
noncomputable def sinAccCos : ℝ → ℝ := eval (ddCoeffs Lgamma.sinpiTable 143 5)
noncomputable def sinAccSin : ℝ → ℝ := eval (ddCoeffs Lgamma.sinpiTable 153 6)

def SinpiAccFact : Prop :=
  (∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * sinAccCos (d ^ 2))| ≤ 1 / 2 ^ 95 * d ^ 2) ∧
    ∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.sin (Real.pi * d / 128) - d * sinAccSin (d ^ 2)| ≤ 1 / 2 ^ 95 * |d|

/-- The ranges of `Lgamma.rootRange`, as `(afh, lo, hi, o, n, k, e)`: the bound on `|fh|`, the open
interval of the argument, the offset `o` of the triple `x0`, the `n` coefficients after it, the
`k` of them that the code evaluates in doubles, and the scale `2 ^ e`. -/
def rootRanges : List (UInt64 × ℚ × ℚ × ℕ × ℕ × ℕ × ℕ) :=
  [(0x3FB7400000000000, ratOfWord 0xC004E147AE147AE1, -2, 128, 26, 6, 3),
    (0x3FB1680000000000, -3, ratOfWord 0xC004E147AE147AE1, 183, 27, 6, 4),
    (0x3FB2D40000000000, -7 / 2, -3, 240, 20, 7, 6),
    (0x3FAEF00000000000, -4, -7 / 2, 283, 20, 7, 8),
    (0x3FC0000000000000, -9 / 2, -4, 326, 24, 7, 7),
    (0x3FB0800000000000, -5, -9 / 2, 377, 19, 7, 10),
    (0x3FB1000000000000, -11 / 2, -5, 418, 19, 6, 10),
    (0x3FC1300000000000, -6, -11 / 2, 459, 24, 6, 12),
    (0x3FC1500000000000, -13 / 2, -6, 510, 24, 6, 12),
    (0x3FC3400000000000, -7, -13 / 2, 561, 25, 6, 14),
    (0x3FC1450000000000, -15 / 2, -7, 614, 24, 6, 15),
    (0x3FC76B0000000000, -8, -15 / 2, 665, 27, 6, 17),
    (0x3FC76C0000000000, -17 / 2, -8, 722, 27, 6, 17),
    (0x3FC9900000000000, -9, -17 / 2, 779, 28, 6, 20),
    (0x3FC9900000000000, -19 / 2, -9, 838, 28, 6, 20),
    (0x3FC76B0000000000, -10, -19 / 2, 897, 27, 6, 24),
    (0x3FC76B0000000000, -21 / 2, -10, 954, 27, 6, 24)]

/-- `-x0` of a range, the zero of `log |Γ|` that its polynomial is centered on, as a triple. -/
def rootX0 (o : ℕ) : ℚ :=
  q Lgamma.accurateTable o + q Lgamma.accurateTable (o + 1) + q Lgamma.accurateTable (o + 2)

/-- The polynomial of a range: `n - k` double-double coefficients and `k` doubles. -/
noncomputable def rootPoly (o n k : ℕ) : ℝ → ℝ :=
  eval (ddCoeffs Lgamma.accurateTable (o + 3) (n - k) ++
    coeffs Lgamma.accurateTable (o + 3 + 2 * (n - k)) 2 k)

def RootFact : Prop :=
  ∀ afh lo hi o n k e, (afh, lo, hi, o, n, k, e) ∈ rootRanges →
    ∀ x : ℝ, (lo : ℝ) < x → x < hi → |GammaBasic.lgamma x| ≤ (1 + 1 / 2 ^ 40) * ratOfWord afh →
      |GammaBasic.lgamma x - (x + rootX0 o) * rootPoly o n k (2 ^ e * (x + rootX0 o))| ≤
        1 / 2 ^ 63 * |GammaBasic.lgamma x| + 1 / 2 ^ 120

/-- Every double inside a range of `rootRanges` lies where `|log |Γ|| ≥ 2^-60`; the smallest value
is about `5.6 · 10^-17`, next to the zero at -2.457. -/
def RootMinFact : Prop :=
  ∀ afh lo hi o n k e, (afh, lo, hi, o, n, k, e) ∈ rootRanges →
    ∀ w : UInt64, CodeLib.IEEE64.Finite w → (lo : ℝ) < CodeLib.IEEE64.value w →
      CodeLib.IEEE64.value w < hi → 1 / 2 ^ 60 ≤ |GammaBasic.lgamma (CodeLib.IEEE64.value w)|

/-- The hard cases of `Lgamma.database`: the argument and the double nearest to `log |Γ|`. -/
def dbX (k : ℕ) : ℚ := q Lgamma.dbTable (3 * k)
def dbF (k : ℕ) : ℚ := q Lgamma.dbTable (3 * k + 1)

def DbFact : Prop := ∀ k < 19, |GammaBasic.lgamma (dbX k) - dbF k| ≤ 1 / 2 ^ 60 * |(dbF k : ℝ)|

/-- At every non-integer double `x` from -21/2 down, the reflection
`log |Γ x| = -(log Γ (1 - x) + log (|sin (π x)|/π))` cancels by at most `2^32`. -/
def CancelFact : Prop :=
  ∀ w : UInt64, CodeLib.IEEE64.Finite w → CodeLib.IEEE64.value w ≤ -21 / 2 →
    (∀ n : ℤ, CodeLib.IEEE64.value w ≠ n) →
      |GammaBasic.lgamma (1 - CodeLib.IEEE64.value w)| ≤ 2 ^ 32 * |GammaBasic.lgamma (CodeLib.IEEE64.value w)|

/-- Every approximation statement of the proof. -/
def AllFacts : Prop :=
  SmallFact ∧ PieceFact ∧ StirlingFact ∧ LogFact ∧ SinpiFact ∧ AccPolyFact ∧ AsymFact ∧
    LogAccFact ∧ SinpiAccFact ∧ RootFact ∧ RootMinFact ∧ DbFact ∧ CancelFact

end Library.Numerics.Float64.Lgamma.LgammaApprox
