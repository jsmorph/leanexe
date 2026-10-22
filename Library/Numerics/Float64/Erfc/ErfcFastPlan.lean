import Library.Numerics.Float64.Erfc.ErfcFastRow

/-!
The certificate parameters of the 94 rows of `C`, the table of `cr_erf_fast` from `1/16` on, and the
target of each row.  Row `i` takes `planN` terms of the series of `erf` at 0, cuts the shifted series
after degree `planJ`, checks the difference with `ε = 2 ^ -planE` and at most `planD` bisections,
and must stay within `target i` of `erf x`: `(7/8) u erfcLo` at the row's top, or at
`0x1.713786d9c7c09p+1`, for the rows 1 to 46 that positive arguments reach, and `(7/8) u` for the
rows 47 to 94, which only negative arguments reach.  `cert/cgen.py` in the track's scratch
directory chose the parameters, and `cert/cemit.py` wrote this file and the row modules.
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastPlan

open LeanExe.ProofKit ErfcFastRow ErfcSeries

/-- `0x1.713786d9c7c09p+1`, the top of the positive range of `cr_erf_fast`. -/
def xMax : ℚ := 6495332420320265 / 2 ^ 51

def planN : List ℕ :=
  [8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 25, 26, 27, 28, 29,
    30, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 52,
    54, 55, 56, 57, 59, 60, 61, 63, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80, 82, 83, 85,
    87, 88, 90, 92, 93, 95, 97, 99, 100, 102, 104, 106, 108, 110, 111, 113, 115, 117, 119, 121,
    123, 125, 127, 129]

def planJ : List ℕ :=
  [11, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 10, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 11, 11, 12, 12, 9, 9,
    9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]

def planE : List ℕ :=
  [56, 56, 56, 56, 56, 57, 57, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 59, 60, 60, 60, 61, 61,
    61, 62, 62, 62, 63, 63, 63, 64, 64, 65, 65, 66, 66, 66, 67, 67, 68, 68, 69, 70, 70, 70, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56]

def planD : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The target of row `i`. -/
def target (i : ℕ) : ℚ :=
  if i ≤ 46 then 7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((i + 1 : ℕ) : ℚ) / 16) xMax)
  else 7 / 8 * (1 / 2 ^ 53)

/-- The kernel's conditions for row `i` of `C`. -/
def rowOK (i : ℕ) : Prop :=
  RowOK Erfc.fastTable i (planN.getD (i - 1) 0) (planJ.getD (i - 1) 0)
    (1 / 2 ^ planE.getD (i - 1) 0) (planD.getD (i - 1) 0) (target i)

set_option synthInstance.maxSize 4096 in
instance (i : ℕ) : Decidable (rowOK i) := by unfold rowOK; infer_instance

end Library.Numerics.Float64.Erfc.ErfcFastPlan
