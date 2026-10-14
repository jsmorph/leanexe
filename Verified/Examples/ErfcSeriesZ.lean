import Verified.Examples.ErfcSeriesI

/-!
The tail bound of `ErfcSeriesI` in integer arithmetic.  `rowTail` sums the absolute values of the
high coefficients of the series of `n` terms shifted to the center `m`; the kernel computes that
shift over `ℚ` slowly, since each rational operation normalizes its result, and for 131 terms the
check of one row took 21 seconds and 2.8 GB.  `shiftZ` performs the same shift on integer
coefficients, as `LeanExe.ProofKit.BesselRatio.ishift` does for the Bessel track, and
`rowTail_eq` and `rowBoundZ_eq` show that the integer forms give the same rationals.
-/

namespace Verified.Examples.ErfcSeriesZ

open LeanExe.ProofKit PolyBound PolyCalculus ErfcSeries ErfcSeriesI

/-- An integer polynomial as a list of rationals. -/
def toQ (l : List ℤ) : List ℚ := l.map fun a : ℤ => (a : ℚ)

theorem toQ_nil : toQ [] = [] := rfl

theorem toQ_cons (a : ℤ) (l : List ℤ) : toQ (a :: l) = (a : ℚ) :: toQ l := rfl

/-- The sum of two integer polynomials. -/
def addZ : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addZ p q

/-- `(X + c) q`. -/
def mulLinZ (c : ℤ) (q : List ℤ) : List ℤ := addZ (q.map fun a => c * a) (0 :: q)

/-- The coefficients of `p (c + X)`. -/
def shiftZ (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: p => addZ [a] (mulLinZ c (shiftZ c p))

/-- `[a, 0, b, 0, ...]`. -/
def spreadZ : List ℤ → List ℤ
  | [] => []
  | a :: p => a :: 0 :: spreadZ p

/-- `serI` with integer coefficients. -/
def serZ (n D s : ℕ) : List ℤ :=
  0 :: spreadZ ((List.range n).map fun k =>
    (-1) ^ k * ((D / (k.factorial * (2 * k + 1)) : ℕ) : ℤ) * (s : ℤ) ^ (2 * (n - 1 - k)))

/-- `Σ |a_k|`. -/
def absSumN : List ℤ → ℕ
  | [] => 0
  | a :: p => a.natAbs + absSumN p

theorem toQ_addZ (p q : List ℤ) : toQ (addZ p q) = addP (toQ p) (toQ q) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => rw [addZ, toQ_cons, toQ_cons, toQ_cons, addP, ih, Int.cast_add]

theorem toQ_map_mul (c : ℤ) (q : List ℤ) : toQ (q.map fun a => c * a) = scaleP c (toQ q) := by
  induction q with
  | nil => rfl
  | cons a q ih => rw [List.map_cons, toQ_cons, toQ_cons, scaleP, ih, Int.cast_mul]

theorem toQ_mulLinZ (c : ℤ) (q : List ℤ) : toQ (mulLinZ c q) = mulLinear c (toQ q) := by
  rw [mulLinZ, toQ_addZ, toQ_map_mul, mulLinear, toQ_cons, Int.cast_zero]

theorem toQ_shiftZ (c : ℤ) (p : List ℤ) : toQ (shiftZ c p) = shift c (toQ p) := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [shiftZ, toQ_addZ, toQ_mulLinZ, ih, toQ_cons, toQ_cons, toQ_nil, shift]

theorem toQ_spreadZ (p : List ℤ) : toQ (spreadZ p) = spread (toQ p) := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [spreadZ, toQ_cons, toQ_cons, toQ_cons, ih, spread, Int.cast_zero]

theorem toQ_serZ (n D s : ℕ) : toQ (serZ n D s) = serI n D s := by
  rw [serZ, serI, oddP, toQ_cons, toQ_spreadZ, Int.cast_zero, toQ, List.map_map]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]

theorem toQ_drop (l : List ℤ) (k : ℕ) : (toQ l).drop k = toQ (l.drop k) := by
  rw [toQ, toQ, List.map_drop]

theorem absSum_toQ (l : List ℤ) : absSum 1 (toQ l) = (absSumN l : ℚ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [toQ_cons, absSum, absSumN, ih, one_mul, Nat.cast_add]
    congr 1
    unfold qabs
    split
    · rename_i h
      have h' : a < 0 := by exact_mod_cast h
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg h]
    · rename_i h
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (not_lt.mp h)]

/-- `rowTail` with the shift in integers. -/
def rowTailZ (n J m s : ℕ) : ℚ :=
  (absSumN ((shiftZ m (serZ n (serD n) s)).drop (J + 1)) : ℚ) / rowDen n s

theorem rowTail_eq (n J m s : ℕ) : rowTail n J m s = rowTailZ n J m s := by
  unfold rowTail rowTailZ rowB
  rw [← toQ_serZ, show ((m : ℚ)) = ((m : ℤ) : ℚ) by simp, ← toQ_shiftZ, toQ_drop, absSum_toQ]

/-- `rowBoundI` with `rowTailZ`. -/
def rowBoundZ (n J m s : ℕ) (ε : ℚ) : ℚ :=
  ε + (sHi - sLo) / 2 * absSum (1 / s) (rowLo n J m s) +
    sHi * (rowTailZ n J m s + serRem n ((m : ℚ) / s + 1 / s))

theorem rowBoundZ_eq (n J m s : ℕ) (ε : ℚ) : rowBoundZ n J m s ε = rowBoundI n J m s ε := by
  rw [rowBoundZ, rowBoundI, rowTail_eq]

#print axioms rowBoundZ_eq

end Verified.Examples.ErfcSeriesZ
