import Verified.Examples.ErfSmallPieces0

/-!
Intervals 37 to 73 of the first range of `s_erf.c` for `erf`, from `x = 0.421875` to `0.84375`.
For each interval `[xlo, xhi]` with the range `[zlo, zhi]` of the computed `x x`, `decide +kernel` checks
`ErfSmallBase.smallOK` and either the relative criterion `smallRelOK` or, for results in `[1/2, 1)`,
`smallTopOK`, and `small_erf_rel` or `small_erf_top` gives one step.  `gen_small.py` and
`emit_small.py` in the track's scratch directory compute the intervals with the same rational
arithmetic and write the file.
-/

namespace Verified.Examples.ErfSmallPieces1
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner ErfSmallBase RealErf

theorem ok37 : smallOK (27 / 64 : ℚ) (7 / 16 : ℚ)
    (3283124128353091219 / 18446744073709551616 : ℚ)
    (3530822107858469257 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit37 : smallRelOK (27 / 64 : ℚ) (7 / 16 : ℚ)
    (3283124128353091219 / 18446744073709551616 : ℚ)
    (3530822107858469257 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf37 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((27 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((7 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok37 crit37 X hX hx0 hxl hxh

theorem ok38 : smallOK (7 / 16 : ℚ) (29 / 64 : ℚ)
    (3530822107858468471 / 18446744073709551616 : ℚ)
    (3787527286618587557 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit38 : smallRelOK (7 / 16 : ℚ) (29 / 64 : ℚ)
    (3530822107858468471 / 18446744073709551616 : ℚ)
    (3787527286618587557 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf38 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((7 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((29 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok38 crit38 X hX hx0 hxl hxh

theorem ok39 : smallOK (29 / 64 : ℚ) (15 / 32 : ℚ)
    (3787527286618586715 / 18446744073709551616 : ℚ)
    (4053239664633446851 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit39 : smallRelOK (29 / 64 : ℚ) (15 / 32 : ℚ)
    (3787527286618586715 / 18446744073709551616 : ℚ)
    (4053239664633446851 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf39 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((29 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((15 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok39 crit39 X hX hx0 hxl hxh

theorem ok40 : smallOK (15 / 32 : ℚ) (31 / 64 : ℚ)
    (4053239664633445949 / 18446744073709551616 : ℚ)
    (4327959241903047137 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit40 : smallRelOK (15 / 32 : ℚ) (31 / 64 : ℚ)
    (4053239664633445949 / 18446744073709551616 : ℚ)
    (4327959241903047137 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf40 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((15 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((31 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok40 crit40 X hX hx0 hxl hxh

theorem ok41 : smallOK (31 / 64 : ℚ) (1 / 2 : ℚ)
    (4327959241903046175 / 18446744073709551616 : ℚ)
    (4611686018427388417 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit41 : smallRelOK (31 / 64 : ℚ) (1 / 2 : ℚ)
    (4327959241903046175 / 18446744073709551616 : ℚ)
    (4611686018427388417 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf41 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((31 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 2 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok41 crit41 X hX hx0 hxl hxh

theorem ok42 : smallOK (1 / 2 : ℚ) (33 / 64 : ℚ)
    (4611686018427387391 / 18446744073709551616 : ℚ)
    (4904419994206470689 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit42 : smallRelOK (1 / 2 : ℚ) (33 / 64 : ℚ)
    (4611686018427387391 / 18446744073709551616 : ℚ)
    (4904419994206470689 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf42 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 2 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((33 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok42 crit42 X hX hx0 hxl hxh

theorem ok43 : smallOK (33 / 64 : ℚ) (17 / 32 : ℚ)
    (4904419994206469599 / 18446744073709551616 : ℚ)
    (5206161169240293955 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit43 : smallRelOK (33 / 64 : ℚ) (17 / 32 : ℚ)
    (4904419994206469599 / 18446744073709551616 : ℚ)
    (5206161169240293955 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf43 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((33 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((17 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok43 crit43 X hX hx0 hxl hxh

theorem ok44 : smallOK (17 / 32 : ℚ) (35 / 64 : ℚ)
    (5206161169240292797 / 18446744073709551616 : ℚ)
    (5516909543528858213 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit44 : smallRelOK (17 / 32 : ℚ) (35 / 64 : ℚ)
    (5206161169240292797 / 18446744073709551616 : ℚ)
    (5516909543528858213 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf44 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((17 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((35 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok44 crit44 X hX hx0 hxl hxh

theorem ok45 : smallOK (35 / 64 : ℚ) (9 / 16 : ℚ)
    (5516909543528856987 / 18446744073709551616 : ℚ)
    (5836665117072163465 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit45 : smallRelOK (35 / 64 : ℚ) (9 / 16 : ℚ)
    (5516909543528856987 / 18446744073709551616 : ℚ)
    (5836665117072163465 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf45 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((35 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((9 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok45 crit45 X hX hx0 hxl hxh

theorem ok46 : smallOK (9 / 16 : ℚ) (37 / 64 : ℚ)
    (5836665117072162167 / 18446744073709551616 : ℚ)
    (6165427889870209709 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit46 : smallRelOK (9 / 16 : ℚ) (37 / 64 : ℚ)
    (5836665117072162167 / 18446744073709551616 : ℚ)
    (6165427889870209709 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf46 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((9 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((37 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok46 crit46 X hX hx0 hxl hxh

theorem ok47 : smallOK (37 / 64 : ℚ) (19 / 32 : ℚ)
    (6165427889870208339 / 18446744073709551616 : ℚ)
    (6503197861922996947 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit47 : smallRelOK (37 / 64 : ℚ) (19 / 32 : ℚ)
    (6165427889870208339 / 18446744073709551616 : ℚ)
    (6503197861922996947 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf47 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((37 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((19 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok47 crit47 X hX hx0 hxl hxh

theorem ok48 : smallOK (19 / 32 : ℚ) (39 / 64 : ℚ)
    (6503197861922995501 / 18446744073709551616 : ℚ)
    (6849975033230525177 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit48 : smallRelOK (19 / 32 : ℚ) (39 / 64 : ℚ)
    (6503197861922995501 / 18446744073709551616 : ℚ)
    (6849975033230525177 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf48 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((19 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((39 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok48 crit48 X hX hx0 hxl hxh

theorem ok49 : smallOK (39 / 64 : ℚ) (5 / 8 : ℚ)
    (6849975033230523655 / 18446744073709551616 : ℚ)
    (7205759403792794401 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit49 : smallRelOK (39 / 64 : ℚ) (5 / 8 : ℚ)
    (6849975033230523655 / 18446744073709551616 : ℚ)
    (7205759403792794401 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf49 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((39 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((5 / 8 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok49 crit49 X hX hx0 hxl hxh

theorem ok50 : smallOK (5 / 8 : ℚ) (41 / 64 : ℚ)
    (7205759403792792799 / 18446744073709551616 : ℚ)
    (7570550973609804617 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit50 : smallRelOK (5 / 8 : ℚ) (41 / 64 : ℚ)
    (7205759403792792799 / 18446744073709551616 : ℚ)
    (7570550973609804617 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf50 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((5 / 8 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((41 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok50 crit50 X hX hx0 hxl hxh

theorem ok51 : smallOK (41 / 64 : ℚ) (21 / 32 : ℚ)
    (7570550973609802935 / 18446744073709551616 : ℚ)
    (7944349742681555827 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit51 : smallRelOK (41 / 64 : ℚ) (21 / 32 : ℚ)
    (7570550973609802935 / 18446744073709551616 : ℚ)
    (7944349742681555827 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf51 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((41 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((21 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok51 crit51 X hX hx0 hxl hxh

theorem ok52 : smallOK (21 / 32 : ℚ) (43 / 64 : ℚ)
    (7944349742681554061 / 18446744073709551616 : ℚ)
    (8327155711008048029 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit52 : smallRelOK (21 / 32 : ℚ) (43 / 64 : ℚ)
    (7944349742681554061 / 18446744073709551616 : ℚ)
    (8327155711008048029 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf52 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((21 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((43 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok52 crit52 X hX hx0 hxl hxh

theorem ok53 : smallOK (43 / 64 : ℚ) (11 / 16 : ℚ)
    (8327155711008046179 / 18446744073709551616 : ℚ)
    (8718968878589281225 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit53 : smallRelOK (43 / 64 : ℚ) (11 / 16 : ℚ)
    (8327155711008046179 / 18446744073709551616 : ℚ)
    (8718968878589281225 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf53 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((43 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((11 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok53 crit53 X hX hx0 hxl hxh

theorem ok54 : smallOK (11 / 16 : ℚ) (45 / 64 : ℚ)
    (8718968878589279287 / 18446744073709551616 : ℚ)
    (9119789245425255413 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit54 : smallRelOK (11 / 16 : ℚ) (45 / 64 : ℚ)
    (8718968878589279287 / 18446744073709551616 : ℚ)
    (9119789245425255413 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf54 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((11 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((45 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok54 crit54 X hX hx0 hxl hxh

theorem ok55 : smallOK (45 / 64 : ℚ) (23 / 32 : ℚ)
    (9119789245425253387 / 18446744073709551616 : ℚ)
    (9529616811515970595 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit55 : smallRelOK (45 / 64 : ℚ) (23 / 32 : ℚ)
    (9119789245425253387 / 18446744073709551616 : ℚ)
    (9529616811515970595 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf55 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((45 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((23 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok55 crit55 X hX hx0 hxl hxh

theorem ok56 : smallOK (23 / 32 : ℚ) (47 / 64 : ℚ)
    (9529616811515968477 / 18446744073709551616 : ℚ)
    (9948451576861426769 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit56 : smallRelOK (23 / 32 : ℚ) (47 / 64 : ℚ)
    (9529616811515968477 / 18446744073709551616 : ℚ)
    (9948451576861426769 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf56 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((23 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((47 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok56 crit56 X hX hx0 hxl hxh

theorem ok57 : smallOK (47 / 64 : ℚ) (3 / 4 : ℚ)
    (9948451576861424559 / 18446744073709551616 : ℚ)
    (10376293541461623937 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit57 : smallRelOK (47 / 64 : ℚ) (3 / 4 : ℚ)
    (9948451576861424559 / 18446744073709551616 : ℚ)
    (10376293541461623937 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf57 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((47 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((3 / 4 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok57 crit57 X hX hx0 hxl hxh

theorem ok58 : smallOK (3 / 4 : ℚ) (97 / 128 : ℚ)
    (10376293541461621631 / 18446744073709551616 : ℚ)
    (10593592223482250393 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit58 : smallTopOK (3 / 4 : ℚ) (97 / 128 : ℚ)
    (10376293541461621631 / 18446744073709551616 : ℚ)
    (10593592223482250393 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf58 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((3 / 4 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((97 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok58 crit58 X hX hx0 hxl hxh

theorem ok59 : smallOK (97 / 128 : ℚ) (49 / 64 : ℚ)
    (10593592223482248039 / 18446744073709551616 : ℚ)
    (10813142705316562097 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit59 : smallTopOK (97 / 128 : ℚ) (49 / 64 : ℚ)
    (10593592223482248039 / 18446744073709551616 : ℚ)
    (10813142705316562097 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf59 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((97 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((49 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok59 crit59 X hX hx0 hxl hxh

theorem ok60 : smallOK (49 / 64 : ℚ) (99 / 128 : ℚ)
    (10813142705316559695 / 18446744073709551616 : ℚ)
    (5517472493482279525 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem crit60 : smallTopOK (49 / 64 : ℚ) (99 / 128 : ℚ)
    (10813142705316559695 / 18446744073709551616 : ℚ)
    (5517472493482279525 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem erf60 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((49 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((99 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok60 crit60 X hX hx0 hxl hxh

theorem ok61 : smallOK (99 / 128 : ℚ) (25 / 32 : ℚ)
    (5517472493482278299 / 9223372036854775808 : ℚ)
    (11258999068426241251 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit61 : smallTopOK (99 / 128 : ℚ) (25 / 32 : ℚ)
    (5517472493482278299 / 9223372036854775808 : ℚ)
    (11258999068426241251 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf61 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((99 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((25 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok61 crit61 X hX hx0 hxl hxh

theorem ok62 : smallOK (25 / 32 : ℚ) (101 / 128 : ℚ)
    (11258999068426238749 / 18446744073709551616 : ℚ)
    (2871326237425402175 / 4611686018427387904 : ℚ) = true := by
  decide +kernel

theorem crit62 : smallTopOK (25 / 32 : ℚ) (101 / 128 : ℚ)
    (11258999068426238749 / 18446744073709551616 : ℚ)
    (2871326237425402175 / 4611686018427387904 : ℚ) = true := by
  decide +kernel

theorem erf62 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((25 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((101 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok62 crit62 X hX hx0 hxl hxh

theorem ok63 : smallOK (101 / 128 : ℚ) (51 / 64 : ℚ)
    (2871326237425401537 / 4611686018427387904 : ℚ)
    (11713862630790661397 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit63 : smallTopOK (101 / 128 : ℚ) (51 / 64 : ℚ)
    (2871326237425401537 / 4611686018427387904 : ℚ)
    (11713862630790661397 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf63 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((101 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((51 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok63 crit63 X hX hx0 hxl hxh

theorem ok64 : smallOK (51 / 64 : ℚ) (103 / 128 : ℚ)
    (11713862630790658795 / 18446744073709551616 : ℚ)
    (11944672111693399343 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit64 : smallTopOK (51 / 64 : ℚ) (103 / 128 : ℚ)
    (11713862630790658795 / 18446744073709551616 : ℚ)
    (11944672111693399343 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf64 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((51 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((103 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok64 crit64 X hX hx0 hxl hxh

theorem ok65 : smallOK (103 / 128 : ℚ) (13 / 16 : ℚ)
    (11944672111693396689 / 18446744073709551616 : ℚ)
    (12177733392409822537 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit65 : smallTopOK (103 / 128 : ℚ) (13 / 16 : ℚ)
    (11944672111693396689 / 18446744073709551616 : ℚ)
    (12177733392409822537 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf65 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((103 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((13 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok65 crit65 X hX hx0 hxl hxh

theorem ok66 : smallOK (13 / 16 : ℚ) (209 / 256 : ℚ)
    (12177733392409819831 / 18446744073709551616 : ℚ)
    (6147554228849083051 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem crit66 : smallTopOK (13 / 16 : ℚ) (209 / 256 : ℚ)
    (12177733392409819831 / 18446744073709551616 : ℚ)
    (6147554228849083051 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem erf66 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((13 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((209 / 256 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok66 crit66 X hX hx0 hxl hxh

theorem ok67 : smallOK (209 / 256 : ℚ) (105 / 128 : ℚ)
    (6147554228849081685 / 9223372036854775808 : ℚ)
    (12413046472939930979 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit67 : smallTopOK (209 / 256 : ℚ) (105 / 128 : ℚ)
    (6147554228849081685 / 9223372036854775808 : ℚ)
    (12413046472939930979 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf67 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((209 / 256 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((105 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok67 crit67 X hX hx0 hxl hxh

theorem ok68 : smallOK (105 / 128 : ℚ) (211 / 256 : ℚ)
    (12413046472939928221 / 18446744073709551616 : ℚ)
    (783221714883444823 / 1152921504606846976 : ℚ) = true := by
  decide +kernel

theorem crit68 : smallTopOK (105 / 128 : ℚ) (211 / 256 : ℚ)
    (12413046472939928221 / 18446744073709551616 : ℚ)
    (783221714883444823 / 1152921504606846976 : ℚ) = true := by
  decide +kernel

theorem erf68 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((105 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((211 / 256 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok68 crit68 X hX hx0 hxl hxh

theorem ok69 : smallOK (211 / 256 : ℚ) (53 / 64 : ℚ)
    (783221714883444649 / 1152921504606846976 : ℚ)
    (12650611353283724669 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit69 : smallTopOK (211 / 256 : ℚ) (53 / 64 : ℚ)
    (783221714883444649 / 1152921504606846976 : ℚ)
    (12650611353283724669 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf69 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((211 / 256 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((53 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok69 crit69 X hX hx0 hxl hxh

theorem ok70 : smallOK (53 / 64 : ℚ) (213 / 256 : ℚ)
    (12650611353283721859 / 18446744073709551616 : ℚ)
    (6385119109192876741 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem crit70 : smallTopOK (53 / 64 : ℚ) (213 / 256 : ℚ)
    (12650611353283721859 / 18446744073709551616 : ℚ)
    (6385119109192876741 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem erf70 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((53 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((213 / 256 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok70 crit70 X hX hx0 hxl hxh

theorem ok71 : smallOK (213 / 256 : ℚ) (107 / 128 : ℚ)
    (6385119109192875323 / 9223372036854775808 : ℚ)
    (1611303504180150451 / 2305843009213693952 : ℚ) = true := by
  decide +kernel

theorem crit71 : smallTopOK (213 / 256 : ℚ) (107 / 128 : ℚ)
    (6385119109192875323 / 9223372036854775808 : ℚ)
    (1611303504180150451 / 2305843009213693952 : ℚ) = true := by
  decide +kernel

theorem erf71 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((213 / 256 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((107 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok71 crit71 X hX hx0 hxl hxh

theorem ok72 : smallOK (107 / 128 : ℚ) (215 / 256 : ℚ)
    (1611303504180150093 / 2305843009213693952 : ℚ)
    (13011180798450075045 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit72 : smallTopOK (107 / 128 : ℚ) (215 / 256 : ℚ)
    (1611303504180150093 / 2305843009213693952 : ℚ)
    (13011180798450075045 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf72 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((107 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((215 / 256 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok72 crit72 X hX hx0 hxl hxh

theorem ok73 : smallOK (215 / 256 : ℚ) (27 / 32 : ℚ)
    (13011180798450072155 / 18446744073709551616 : ℚ)
    (13132496513412367795 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit73 : smallTopOK (215 / 256 : ℚ) (27 / 32 : ℚ)
    (13011180798450072155 / 18446744073709551616 : ℚ)
    (13132496513412367795 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf73 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((215 / 256 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((27 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_top _ _ _ _ ok73 crit73 X hX hx0 hxl hxh

#print axioms erf37
#print axioms erf38
#print axioms erf39
#print axioms erf40
#print axioms erf41
#print axioms erf42
#print axioms erf43
#print axioms erf44
#print axioms erf45
#print axioms erf46
#print axioms erf47
#print axioms erf48
#print axioms erf49
#print axioms erf50
#print axioms erf51
#print axioms erf52
#print axioms erf53
#print axioms erf54
#print axioms erf55
#print axioms erf56
#print axioms erf57
#print axioms erf58
#print axioms erf59
#print axioms erf60
#print axioms erf61
#print axioms erf62
#print axioms erf63
#print axioms erf64
#print axioms erf65
#print axioms erf66
#print axioms erf67
#print axioms erf68
#print axioms erf69
#print axioms erf70
#print axioms erf71
#print axioms erf72
#print axioms erf73

end Verified.Examples.ErfSmallPieces1
