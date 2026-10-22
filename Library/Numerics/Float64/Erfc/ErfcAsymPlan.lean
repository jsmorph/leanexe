import Library.Numerics.Float64.Erfc.ErfcAsymCert
import Library.Numerics.Float64.Erfc.Compiled

/-!
The rows of `T` and `Tacc` of `Erfc` as rational polynomials in `u = 1/x²`, the intervals of `x`
that their indices allow, and the accuracy of the certificates: `epsA` for the checks and `rhoA`
for the results of `ErfcAsymCert.cert_sound`.  `gen/trows.py` in the track's scratch directory
generates the file and the row modules.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymPlan

open LeanExe.ProofKit PolyBound

/-- The 13 words of row `i` of `T`. -/
def tq (i : ℕ) : List ℚ := (List.range 13).map fun j => ratOfWord Erfc.asymTable[13 * i + j]!

/-- The polynomial of a row of `T`: `(q0 + q1) + q2 u + ... + q12 u^11`. -/
def fastZ (q : List ℚ) : List ℚ :=
  [q.getD 0 0 + q.getD 1 0, q.getD 2 0, q.getD 3 0, q.getD 4 0, q.getD 5 0, q.getD 6 0,
    q.getD 7 0, q.getD 8 0, q.getD 9 0, q.getD 10 0, q.getD 11 0, q.getD 12 0]

/-- The `21 + i` words of row `i` of `Tacc`. -/
def taq (i : ℕ) : List ℚ := (List.range (21 + i)).map fun j => ratOfWord Erfc.asymAccTable[30 * i + j]!

/-- The polynomial of row `i` of `Tacc`: the double-double coefficients `q (2k) + q (2k+1)` of
degrees 0 to 5, and the coefficients `q 12` to `q (20 + i)` of degrees 6 to `14 + i`. -/
def accZ (q : List ℚ) (i : ℕ) : List ℚ :=
  (List.range 6).map (fun k => q.getD (2 * k) 0 + q.getD (2 * k + 1) 0) ++
    (List.range (9 + i)).map fun j => q.getD (12 + j) 0

/-- The accuracy of the checks. -/
def epsA : ℚ := 1 / 2 ^ 62

/-- The relative accuracy of the rows against `x erfcx x`. -/
def rhoA : ℚ := 1 / 2 ^ 61

/-- The lower ends of the intervals of `x` of the rows of `T`. -/
def loT : List ℚ := [(572357 / 2 ^ 16 : ℚ), (3104617 / 2 ^ 19 : ℚ), (2418337 / 2 ^ 19 : ℚ), (4006499 / 2 ^ 20 : ℚ), (430185 / 2 ^ 17 : ℚ), (189039 / 2 ^ 16 : ℚ)]

/-- The upper ends of the intervals of `x` of the rows of `T`. -/
def hiT : List ℚ := [(6777967 / 2 ^ 18 : ℚ), (9157713 / 2 ^ 20 : ℚ), (6209235 / 2 ^ 20 : ℚ), (4836675 / 2 ^ 20 : ℚ), (1001625 / 2 ^ 18 : ℚ), (3441481 / 2 ^ 20 : ℚ)]

/-- The lower ends of the intervals of `x` of the rows of `Tacc`. -/
def loA : List ℚ := [(13215283 / 2 ^ 20 : ℚ), (1118481 / 2 ^ 17 : ℚ), (6731923 / 2 ^ 20 : ℚ), (1325607 / 2 ^ 18 : ℚ), (2143197 / 2 ^ 19 : ℚ), (220029 / 2 ^ 16 : ℚ), (2909869 / 2 ^ 20 : ℚ), (2418337 / 2 ^ 20 : ℚ), (15709 / 2 ^ 13 : ℚ), (1792511 / 2 ^ 20 : ℚ)]

/-- The upper ends of the intervals of `x` of the rows of `Tacc`. -/
def hiA : List ℚ := [(28548549 / 2 ^ 20 : ℚ), (3303821 / 2 ^ 18 : ℚ), (8947849 / 2 ^ 20 : ℚ), (1682981 / 2 ^ 18 : ℚ), (5302429 / 2 ^ 20 : ℚ), (4286395 / 2 ^ 20 : ℚ), (3520465 / 2 ^ 20 : ℚ), (1454935 / 2 ^ 19 : ℚ), (1209169 / 2 ^ 19 : ℚ), (2010753 / 2 ^ 20 : ℚ)]

/-- The bounds `MU` on `U ≈ 1/x²` of the rows of `T`. -/
def muT : List ℚ := [(1801920821 / 2 ^ 37 : ℚ), (1959763283 / 2 ^ 36 : ℚ), (807469351 / 2 ^ 34 : ℚ), (588382309 / 2 ^ 33 : ℚ), (1594884287 / 2 ^ 34 : ℚ), (1032397385 / 2 ^ 33 : ℚ)]

#print axioms fastZ
#print axioms accZ

end Library.Numerics.Float64.Erfc.ErfcAsymPlan
