import Library.Numerics.Float64.Tgamma.TgammaApprox

/-!
The kernel check of the database of hard cases of `Tgamma.accurate`.  For row `k`, `dbOk k` takes
the argument `x`, the double `f`, and the correction `δ`, the floor `n = ⌊x⌋`, the range `rowOf n`
of `Tgamma.accurateRange`, and the rational `E = 2 ^ eoff accPoly d K` (`approxE`) for
`d = 2 (x - n) - 1` and the factor `K` with `Γ x = Γ (x + j - n) K` (`kfac`), and checks
`|δ| < |f|`, `|δ| + |f + δ - E| ≤ (5/4) 2 ^ -53 |E|`, and `2 ^ -990 ≤ |E| ≤ 2 ^ 990`.  Each row has
its own kernel check (`db_ok_0` to `db_ok_56`), since one check of all 57 rows exceeded 4 GB.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccDbCheck
open LeanExe.ProofKit PolyBound Tgamma

set_option exponentiation.threshold 4096

/-- Horner's rule on the rationals. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

/-- `TgammaApprox.accPoly` on the rationals. -/
def accPolyQ (oh imax ol jmax : ℕ) (d : ℚ) : ℚ :=
  evalQ (TgammaApprox.coeffs accurateTable oh 1 imax) d +
    evalQ (TgammaApprox.ddCoeffs accurateTable ol jmax) d

/-- `q (q + 1) ⋯ (q + n - 1)`. -/
def poch (q : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => poch q n * (q + n)

/-- The factor `K` with `Γ q = Γ (q + m) K`. -/
def kfac (q : ℚ) (m : ℤ) : ℚ :=
  if 0 ≤ m then 1 / poch q m.toNat else poch (q + m) (-m).toNat

/-- The range of `Tgamma.accurateRange` for `⌊x⌋ = n`. -/
def rowOf (n : ℤ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  if n > 159 then (64, 14, 78, 34, 160, 942)
  else if n > 127 then (146, 14, 160, 33, 128, 713)
  else if n > 95 then (226, 13, 239, 32, 96, 495)
  else if n > 63 then (303, 13, 316, 32, 64, 293)
  else if n > 31 then (380, 12, 392, 30, 32, 115)
  else if n > 25 then (452, 12, 464, 29, 26, 86)
  else if n > 15 then (522, 11, 533, 29, 16, 42)
  else if n > 7 then (591, 10, 601, 28, 8, 14)
  else (657, 9, 666, 26, 4, 3)

/-- The approximation `E` of `Γ x` for `x = qx`, `n = ⌊x⌋`, and the range `r`. -/
def approxE (qx : ℚ) (n : ℤ) (r : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℚ :=
  2 ^ r.2.2.2.2.2 * accPolyQ r.1 r.2.1 r.2.2.1 r.2.2.2.1 (2 * (qx - n) - 1) *
    kfac qx ((r.2.2.2.2.1 : ℤ) - n)

/-- The check of row `k` of the database. -/
def dbOk (k : ℕ) : Bool :=
  let wx := dbTable[3 * k]!
  let wf := dbTable[3 * k + 1]!
  let wd := dbTable[3 * k + 2]!
  let n := ⌊ratOfWord wx⌋
  let E := approxE (ratOfWord wx) n (rowOf n)
  Wasm.IEEE64.isFinite wx && Wasm.IEEE64.isFinite wf && Wasm.IEEE64.isFinite wd &&
    decide (rowOf n ∈ TgammaApprox.accRanges) && decide ((n : ℚ) < ratOfWord wx) &&
    decide (|ratOfWord wd| < |ratOfWord wf|) &&
    decide (|ratOfWord wd| + |ratOfWord wf + ratOfWord wd - E| ≤ 5 / 4 * |E| / 2 ^ 53) &&
    decide (1 / 2 ^ 990 ≤ |E|) && decide (|E| ≤ 2 ^ 990)

theorem db_ok_0 : dbOk 0 = true := by decide +kernel
theorem db_ok_1 : dbOk 1 = true := by decide +kernel
theorem db_ok_2 : dbOk 2 = true := by decide +kernel
theorem db_ok_3 : dbOk 3 = true := by decide +kernel
theorem db_ok_4 : dbOk 4 = true := by decide +kernel
theorem db_ok_5 : dbOk 5 = true := by decide +kernel
theorem db_ok_6 : dbOk 6 = true := by decide +kernel
theorem db_ok_7 : dbOk 7 = true := by decide +kernel
theorem db_ok_8 : dbOk 8 = true := by decide +kernel
theorem db_ok_9 : dbOk 9 = true := by decide +kernel
theorem db_ok_10 : dbOk 10 = true := by decide +kernel
theorem db_ok_11 : dbOk 11 = true := by decide +kernel
theorem db_ok_12 : dbOk 12 = true := by decide +kernel
theorem db_ok_13 : dbOk 13 = true := by decide +kernel
theorem db_ok_14 : dbOk 14 = true := by decide +kernel
theorem db_ok_15 : dbOk 15 = true := by decide +kernel
theorem db_ok_16 : dbOk 16 = true := by decide +kernel
theorem db_ok_17 : dbOk 17 = true := by decide +kernel
theorem db_ok_18 : dbOk 18 = true := by decide +kernel
theorem db_ok_19 : dbOk 19 = true := by decide +kernel
theorem db_ok_20 : dbOk 20 = true := by decide +kernel
theorem db_ok_21 : dbOk 21 = true := by decide +kernel
theorem db_ok_22 : dbOk 22 = true := by decide +kernel
theorem db_ok_23 : dbOk 23 = true := by decide +kernel
theorem db_ok_24 : dbOk 24 = true := by decide +kernel
theorem db_ok_25 : dbOk 25 = true := by decide +kernel
theorem db_ok_26 : dbOk 26 = true := by decide +kernel
theorem db_ok_27 : dbOk 27 = true := by decide +kernel
theorem db_ok_28 : dbOk 28 = true := by decide +kernel
theorem db_ok_29 : dbOk 29 = true := by decide +kernel
theorem db_ok_30 : dbOk 30 = true := by decide +kernel
theorem db_ok_31 : dbOk 31 = true := by decide +kernel
theorem db_ok_32 : dbOk 32 = true := by decide +kernel
theorem db_ok_33 : dbOk 33 = true := by decide +kernel
theorem db_ok_34 : dbOk 34 = true := by decide +kernel
theorem db_ok_35 : dbOk 35 = true := by decide +kernel
theorem db_ok_36 : dbOk 36 = true := by decide +kernel
theorem db_ok_37 : dbOk 37 = true := by decide +kernel
theorem db_ok_38 : dbOk 38 = true := by decide +kernel
theorem db_ok_39 : dbOk 39 = true := by decide +kernel
theorem db_ok_40 : dbOk 40 = true := by decide +kernel
theorem db_ok_41 : dbOk 41 = true := by decide +kernel
theorem db_ok_42 : dbOk 42 = true := by decide +kernel
theorem db_ok_43 : dbOk 43 = true := by decide +kernel
theorem db_ok_44 : dbOk 44 = true := by decide +kernel
theorem db_ok_45 : dbOk 45 = true := by decide +kernel
theorem db_ok_46 : dbOk 46 = true := by decide +kernel
theorem db_ok_47 : dbOk 47 = true := by decide +kernel
theorem db_ok_48 : dbOk 48 = true := by decide +kernel
theorem db_ok_49 : dbOk 49 = true := by decide +kernel
theorem db_ok_50 : dbOk 50 = true := by decide +kernel
theorem db_ok_51 : dbOk 51 = true := by decide +kernel
theorem db_ok_52 : dbOk 52 = true := by decide +kernel
theorem db_ok_53 : dbOk 53 = true := by decide +kernel
theorem db_ok_54 : dbOk 54 = true := by decide +kernel
theorem db_ok_55 : dbOk 55 = true := by decide +kernel
theorem db_ok_56 : dbOk 56 = true := by decide +kernel

theorem db_ok : ∀ k < 57, dbOk k = true
  | 0, _ => db_ok_0
  | 1, _ => db_ok_1
  | 2, _ => db_ok_2
  | 3, _ => db_ok_3
  | 4, _ => db_ok_4
  | 5, _ => db_ok_5
  | 6, _ => db_ok_6
  | 7, _ => db_ok_7
  | 8, _ => db_ok_8
  | 9, _ => db_ok_9
  | 10, _ => db_ok_10
  | 11, _ => db_ok_11
  | 12, _ => db_ok_12
  | 13, _ => db_ok_13
  | 14, _ => db_ok_14
  | 15, _ => db_ok_15
  | 16, _ => db_ok_16
  | 17, _ => db_ok_17
  | 18, _ => db_ok_18
  | 19, _ => db_ok_19
  | 20, _ => db_ok_20
  | 21, _ => db_ok_21
  | 22, _ => db_ok_22
  | 23, _ => db_ok_23
  | 24, _ => db_ok_24
  | 25, _ => db_ok_25
  | 26, _ => db_ok_26
  | 27, _ => db_ok_27
  | 28, _ => db_ok_28
  | 29, _ => db_ok_29
  | 30, _ => db_ok_30
  | 31, _ => db_ok_31
  | 32, _ => db_ok_32
  | 33, _ => db_ok_33
  | 34, _ => db_ok_34
  | 35, _ => db_ok_35
  | 36, _ => db_ok_36
  | 37, _ => db_ok_37
  | 38, _ => db_ok_38
  | 39, _ => db_ok_39
  | 40, _ => db_ok_40
  | 41, _ => db_ok_41
  | 42, _ => db_ok_42
  | 43, _ => db_ok_43
  | 44, _ => db_ok_44
  | 45, _ => db_ok_45
  | 46, _ => db_ok_46
  | 47, _ => db_ok_47
  | 48, _ => db_ok_48
  | 49, _ => db_ok_49
  | 50, _ => db_ok_50
  | 51, _ => db_ok_51
  | 52, _ => db_ok_52
  | 53, _ => db_ok_53
  | 54, _ => db_ok_54
  | 55, _ => db_ok_55
  | 56, _ => db_ok_56
  | _ + 57, h => absurd h (by omega)

theorem db_index : ∀ k < 57, (3 * UInt64.ofNat k).toNat = 3 * k ∧
    (3 * UInt64.ofNat k + 1).toNat = 3 * k + 1 ∧ (3 * UInt64.ofNat k + 2).toNat = 3 * k + 2 := by
  decide

#print axioms db_ok_0
#print axioms db_ok

end Library.Numerics.Float64.Tgamma.TgammaAccDbCheck
