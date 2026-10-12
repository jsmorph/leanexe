import Verified.Examples.Tgamma
import LeanExe.ProofKit.PolyBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The approximation statements that the floating-point proof of `Tgamma.tgamma` takes as
hypotheses.  Each statement compares a real function built from the words of `Tgamma`'s tables with
`Real.Gamma`, `Real.log`, `Real.exp`, `Real.sin`, `Real.cos`, or `Real.pi`, and involves no
floating-point operation.  `q tab i` is the exact rational value of entry `i` of `tab`,
`coeffs tab o s n` lists the entries `o, o + s, …, o + s (n - 1)`, and `ddCoeffs tab o n` lists the
double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]`.  A polynomial is a coefficient list,
lowest degree first, evaluated by `PolyBound.eval`.

The functions follow the code operation for operation with exact arithmetic.  `smallPoly` is the
polynomial of `tgammaWith` below `1/4`, `mainPoly` that of `[-3, 4]` in `d = x - 7/2` after the
shift, `accSmallPoly` and `accPoly` those of `Tgamma.accurate`, `stirHi` and `stirLo` the two
forms of `asLgammaAsym`, `logPoly`, `expPoly`, `sinPoly`, and `cosPoly` the kernels of `asLogd`,
`asExpd`, and `asSinpid`, and the remaining definitions their tables and constants.  The
tolerances leave a factor of at least 8 over the errors that a 90-digit evaluation found at dense
sample points.  The facts that involve `π` allow for an uncertainty of `10 ^ -20` in `π`, the
precision of Mathlib's bounds `Real.pi_gt_d20` and `Real.pi_lt_d20`.
-/

namespace Verified.Examples.TgammaApprox
open LeanExe.ProofKit PolyBound

/-- The exact rational value of entry `i` of `tab`. -/
def q (tab : Array UInt64) (i : ℕ) : ℚ := ratOfWord tab[i]!

/-- The entries `o + s k` of `tab` for `k < n`. -/
def coeffs (tab : Array UInt64) (o s n : ℕ) : List ℚ := (List.range n).map fun k => q tab (o + s * k)

/-- The double-double coefficients `tab[o + 2k] + tab[o + 2k + 1]` for `k < n`. -/
def ddCoeffs (tab : Array UInt64) (o n : ℕ) : List ℚ :=
  (List.range n).map fun k => q tab (o + 2 * k) + q tab (o + 2 * k + 1)

/-! ### `Γ` below `1/4` and on `[3, 4]` -/

/-- The polynomial of `tgammaWith` below `1/4`: `Γ x ≈ 1/x + smallPoly x`. -/
noncomputable def smallPoly : ℝ → ℝ :=
  eval (ddCoeffs Tgamma.smallTable 0 5 ++ coeffs Tgamma.smallTable 10 1 16)

/-- The polynomial of `tgammaWith` on `[-3, 4]`: `Γ (7/2 + d) ≈ mainPoly d`. -/
noncomputable def mainPoly : ℝ → ℝ :=
  eval (ddCoeffs Tgamma.mainTable 0 10 ++ coeffs Tgamma.mainTable 46 1 8)

/-- The polynomial of `Tgamma.accurate` below `1/4`: `Γ x ≈ 1/x + accSmallPoly x`. -/
noncomputable def accSmallPoly : ℝ → ℝ :=
  eval (ddCoeffs Tgamma.accurateTable 0 28 ++ coeffs Tgamma.accurateTable 56 1 8)

/-- The ranges of `Tgamma.accurate` above `1/4`, as `(oh, imax, ol, jmax, j, eoff)` of
`Tgamma.accurateRange`. -/
def accRanges : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(64, 14, 78, 34, 160, 942), (146, 14, 160, 33, 128, 713), (226, 13, 239, 32, 96, 495),
    (303, 13, 316, 32, 64, 293), (380, 12, 392, 30, 32, 115), (452, 12, 464, 29, 26, 86),
    (522, 11, 533, 29, 16, 42), (591, 10, 601, 28, 8, 14), (657, 9, 666, 26, 4, 3)]

/-- The polynomial of `Tgamma.poly3` with `imax` double coefficients at `oh` and `jmax`
double-double coefficients at `ol`: `Γ (j + (1 + d)/2) ≈ 2 ^ eoff accPoly d`. -/
noncomputable def accPoly (oh imax ol jmax : ℕ) (d : ℝ) : ℝ :=
  eval (coeffs Tgamma.accurateTable oh 1 imax) d + eval (ddCoeffs Tgamma.accurateTable ol jmax) d

/-- `1/2^60` of `Γ (1 + x)` on `[-1/4, 1/4]`, for the fast path below `1/4`. -/
def SmallFact : Prop :=
  ∀ x : ℝ, |x| ≤ 1 / 4 → |Real.Gamma (1 + x) - (1 + x * smallPoly x)| ≤ 1 / 2 ^ 60

/-- `1/2^62` of `Γ (7/2 + d)` for `|d| ≤ 1/2 + 2 ^ -50`.  The code's `d` exceeds `1/2` by up to
`2 ^ -51`, since it rounds `x - 7/2` before choosing the nearest integer. -/
def MainFact : Prop :=
  ∀ d : ℝ, |d| ≤ 1 / 2 + 1 / 2 ^ 50 → |Real.Gamma (7 / 2 + d) - mainPoly d| ≤ 1 / 2 ^ 62

/-- `1/2^62` of `Γ (1 + x)` on `[-1/4, 1/4]`, for the accurate path below `1/4`. -/
def AccSmallFact : Prop :=
  ∀ x : ℝ, |x| ≤ 1 / 4 → |Real.Gamma (1 + x) - (1 + x * accSmallPoly x)| ≤ 1 / 2 ^ 62

/-- The relative error `1/2^62` of each range of the accurate path on `[j, j + 1]`. -/
def AccRangeFact : Prop :=
  ∀ oh imax ol jmax j eoff : ℕ, (oh, imax, ol, jmax, j, eoff) ∈ accRanges →
    ∀ d : ℝ, |d| ≤ 1 →
      |Real.Gamma (j + (1 + d) / 2) - 2 ^ eoff * accPoly oh imax ol jmax d| ≤
        1 / 2 ^ 62 * Real.Gamma (j + (1 + d) / 2)

/-! ### Stirling's series -/

/-- `asLgammaAsym` above `11.5`: `(x - 1/2) (log x - 1) + c + F (1/x²)/x`. -/
noncomputable def stirHi (x : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log x - 1) + ((q Tgamma.asymTable 0 + q Tgamma.asymTable 1 : ℚ) : ℝ) +
    1 / x * eval ((q Tgamma.asymTable 2 + q Tgamma.asymTable 3) :: coeffs Tgamma.asymTable 4 2 6)
      (1 / x ^ 2)

/-- `asLgammaAsym` at or below `11.5`. -/
noncomputable def stirLo (x : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log x - 1) + ((q Tgamma.asymTable 16 + q Tgamma.asymTable 17 : ℚ) : ℝ) +
    1 / x * eval ((q Tgamma.asymTable 18 + q Tgamma.asymTable 19) ::
      (q Tgamma.asymTable 20 + q Tgamma.asymTable 21) :: coeffs Tgamma.asymTable 22 2 10) (1 / x ^ 2)

/-- `1/2^64` of `log Γ x`, each form on a range that overlaps the other's. -/
def StirlingFact : Prop :=
  (∀ x : ℝ, 11 ≤ x → x ≤ 186 → |Real.log (Real.Gamma x) - stirHi x| ≤ 1 / 2 ^ 64) ∧
    ∀ x : ℝ, 4 ≤ x → x ≤ 12 → |Real.log (Real.Gamma x) - stirLo x| ≤ 1 / 2 ^ 64

/-! ### The logarithm, the exponential, and `sin (π x)` -/

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

def LogFact : Prop :=
  (∀ z : ℝ, |z| ≤ 1 / 2400 → |Real.log (1 + z) - (z + z ^ 2 * logPoly z)| ≤ 1 / 2 ^ 70) ∧
    (∀ i < 33, |(l1 i : ℝ) + Real.log (r1 i)| ≤ 1 / 2 ^ 80) ∧
    (∀ i < 32, |(l2 i : ℝ) + Real.log (r2 i)| ≤ 1 / 2 ^ 80) ∧
    |(ln2 : ℝ) - Real.log 2| ≤ 1 / 2 ^ 80

/-- The kernel of `asExpd`: `exp (X ln 2/1024) ≈ 1 + X expPoly X`. -/
noncomputable def expPoly : ℝ → ℝ :=
  eval ((q Tgamma.expdTable 128 + q Tgamma.expdTable 129) :: coeffs Tgamma.expdTable 130 2 4)

/-- `asExpd`'s tables `E0 ≈ 2 ^ (i/32)` and `E1 ≈ 2 ^ (i/1024)`, as double-doubles. -/
def e0 (i : ℕ) : ℚ := q Tgamma.expdTable (2 * i) + q Tgamma.expdTable (2 * i + 1)
def e1 (i : ℕ) : ℚ := q Tgamma.expdTable (64 + 2 * i) + q Tgamma.expdTable (65 + 2 * i)

/-- `asExpd`'s `1024/ln 2` as `0x1.71547652b82fep+10 + 0x1.777d0ffda0d24p-46`. -/
def invLn2 : ℚ := ratOfWord 0x40971547652B82FE + ratOfWord 0x3D1777D0FFDA0D24

/-- The constant, the tables, and the kernel of `asExpd`.  The kernel's interval reaches `5/8`,
beyond the `1/2` of the reduction, because `asLgammaAsym` passes a low part up to about
`2 ^ -14.5`, which the first product of `asExpd` carries into the kernel's argument. -/
def ExpFact : Prop :=
  |(invLn2 : ℝ) - 1024 / Real.log 2| ≤ 1 / 2 ^ 80 ∧
    (∀ i < 32, |(e0 i : ℝ) - Real.exp (i * Real.log 2 / 32)| ≤ 1 / 2 ^ 80) ∧
    (∀ i < 32, |(e1 i : ℝ) - Real.exp (i * Real.log 2 / 1024)| ≤ 1 / 2 ^ 80) ∧
    ∀ X : ℝ, |X| ≤ 5 / 8 →
      |Real.exp (X * Real.log 2 / 1024) - (1 + X * expPoly X)| ≤ 1 / 2 ^ 74

/-- `asSinpid`'s table `st k ≈ sin (k π/128)` for `k ≤ 64`, as double-doubles. -/
def st (k : ℕ) : ℚ := q Tgamma.sinpidTable (2 * k) + q Tgamma.sinpidTable (2 * k + 1)

/-- The kernels of `asSinpid` in `u = d²`: `sin (π d/128) ≈ d sinPoly u` and
`cos (π d/128) ≈ 1 + u cosPoly u`, with the code's corrections `s0` and `c0`. -/
noncomputable def sinPoly : ℝ → ℝ :=
  eval ((q Tgamma.sinpidTable 134 + ratOfWord 0x3C31A624B88C9448) :: coeffs Tgamma.sinpidTable 135 1 3)
noncomputable def cosPoly : ℝ → ℝ :=
  eval ((q Tgamma.sinpidTable 130 + ratOfWord 0xBBD692B66E3CF6E8) :: coeffs Tgamma.sinpidTable 131 1 3)

/-- `tgammaWith`'s `π` as `0x1.921fb54442d18p+1 + 0x1.1a62633145c07p-53`. -/
def piDD : ℚ := ratOfWord 0x400921FB54442D18 + ratOfWord 0x3CA1A62633145C07

def SinFact : Prop :=
  (∀ k ≤ 64, |(st k : ℝ) - Real.sin (k * Real.pi / 128)| ≤ 1 / 2 ^ 66) ∧
    (∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.sin (Real.pi * d / 128) - d * sinPoly (d ^ 2)| ≤ 1 / 2 ^ 71 * |d|) ∧
    (∀ d : ℝ, |d| ≤ 1 / 2 →
      |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * cosPoly (d ^ 2))| ≤ 1 / 2 ^ 76 * d ^ 2) ∧
    |(piDD : ℝ) - Real.pi| ≤ 1 / 2 ^ 66

/-- Every approximation statement of the proof. -/
def AllFacts : Prop :=
  SmallFact ∧ MainFact ∧ AccSmallFact ∧ AccRangeFact ∧ StirlingFact ∧ LogFact ∧ ExpFact ∧ SinFact

end Verified.Examples.TgammaApprox
