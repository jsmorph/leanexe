import Library.Numerics.Float64.Erfc.ErfcAccRow

/-!
The certificate parameters of the 47 rows of `C2`, the table of `cr_erf_accurate` from `1/8` on,
and the target of each row: `(7/8) u erfcLo` at the row's top, or at `0x1.b59ffb450828cp+0`, for
the rows 1 to 13 that positive arguments reach, and `(7/8) u` for the rows from 14, which only
negative arguments reach.  `cert/c2plan.py` in the track's scratch directory chose the parameters,
and `cert/c2emit.py` wrote this file and the row modules.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAccPlan

open LeanExe.ProofKit ErfcAccRow ErfcSeries

/-- `0x1.b59ffb450828cp+0`, the top of the positive range of `cr_erf_accurate`. -/
def xAcc : ℚ := 7698779147895436 / 2 ^ 52

def planN : List ℕ :=
  [10, 12, 14, 16, 17, 19, 21, 23, 25, 26, 28, 30, 33, 33, 35, 37, 39, 41, 43, 45, 48, 50, 52, 55,
    57, 60, 63, 65, 68, 71, 74, 77, 80, 83, 87, 90, 93, 97, 100, 104, 108, 111, 115, 119, 123,
    127, 131]

def planJ : List ℕ :=
  [12, 12, 13, 13, 13, 13, 12, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 11, 11, 11,
    11, 11, 10, 11, 11, 11, 11, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10]

def planE : List ℕ :=
  [56, 56, 57, 57, 57, 58, 58, 59, 59, 60, 61, 61, 62, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56,
    56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56]

def planD : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The target of row `i`. -/
def target (i : ℕ) : ℚ :=
  if i ≤ 13 then 7 / 8 * (1 / 2 ^ 53) * erfcLo 80 (min (((i + 1 : ℕ) : ℚ) / 8) xAcc)
  else 7 / 8 * (1 / 2 ^ 53)

/-- The kernel's conditions for row `i` of `C2`. -/
def rowOK (i : ℕ) : Prop :=
  AccRowOK Erfc.accTable i (planN.getD (i - 1) 0) (planJ.getD (i - 1) 0)
    (1 / 2 ^ planE.getD (i - 1) 0) (planD.getD (i - 1) 0) (target i)

set_option synthInstance.maxSize 4096 in
instance (i : ℕ) : Decidable (rowOK i) := by unfold rowOK; infer_instance

#print axioms rowOK

end Library.Numerics.Float64.Erfc.ErfcAccPlan
