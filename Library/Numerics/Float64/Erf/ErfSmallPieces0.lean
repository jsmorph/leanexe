import Library.Numerics.Float64.Erf.ErfSmallBase

/-!
Intervals 0 to 36 of the first range of `s_erf.c` for `erf`, from `x = 3.72529e-09` to `0.421875`.
For each interval `[xlo, xhi]` with the range `[zlo, zhi]` of the computed `x x`, `decide +kernel` checks
`ErfSmallBase.smallOK` and either the relative criterion `smallRelOK` or, for results in `[1/2, 1)`,
`smallTopOK`, and `small_erf_rel` or `small_erf_top` gives one step.  `gen_small.py` and
`emit_small.py` in the track's scratch directory compute the intervals with the same rational
arithmetic and write the file.
-/

namespace Library.Numerics.Float64.Erf.ErfSmallPieces0
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner ErfSmallBase RealErf

theorem ok0 : smallOK (1 / 268435456 : ℚ) (1 / 134217728 : ℚ)
    (255 / 18446744073709551616 : ℚ)
    (1025 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit0 : smallRelOK (1 / 268435456 : ℚ) (1 / 134217728 : ℚ)
    (255 / 18446744073709551616 : ℚ)
    (1025 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf0 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 268435456 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 134217728 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok0 crit0 X hX hx0 hxl hxh

theorem ok1 : smallOK (1 / 134217728 : ℚ) (1 / 67108864 : ℚ)
    (1023 / 18446744073709551616 : ℚ)
    (4097 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit1 : smallRelOK (1 / 134217728 : ℚ) (1 / 67108864 : ℚ)
    (1023 / 18446744073709551616 : ℚ)
    (4097 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf1 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 134217728 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 67108864 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok1 crit1 X hX hx0 hxl hxh

theorem ok2 : smallOK (1 / 67108864 : ℚ) (1 / 33554432 : ℚ)
    (4095 / 18446744073709551616 : ℚ)
    (16385 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit2 : smallRelOK (1 / 67108864 : ℚ) (1 / 33554432 : ℚ)
    (4095 / 18446744073709551616 : ℚ)
    (16385 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf2 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 67108864 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 33554432 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok2 crit2 X hX hx0 hxl hxh

theorem ok3 : smallOK (1 / 33554432 : ℚ) (1 / 16777216 : ℚ)
    (16383 / 18446744073709551616 : ℚ)
    (65537 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit3 : smallRelOK (1 / 33554432 : ℚ) (1 / 16777216 : ℚ)
    (16383 / 18446744073709551616 : ℚ)
    (65537 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf3 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 33554432 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 16777216 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok3 crit3 X hX hx0 hxl hxh

theorem ok4 : smallOK (1 / 16777216 : ℚ) (1 / 8388608 : ℚ)
    (65535 / 18446744073709551616 : ℚ)
    (262145 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit4 : smallRelOK (1 / 16777216 : ℚ) (1 / 8388608 : ℚ)
    (65535 / 18446744073709551616 : ℚ)
    (262145 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf4 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 16777216 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 8388608 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok4 crit4 X hX hx0 hxl hxh

theorem ok5 : smallOK (1 / 8388608 : ℚ) (1 / 4194304 : ℚ)
    (262143 / 18446744073709551616 : ℚ)
    (1048577 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit5 : smallRelOK (1 / 8388608 : ℚ) (1 / 4194304 : ℚ)
    (262143 / 18446744073709551616 : ℚ)
    (1048577 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf5 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 8388608 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 4194304 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok5 crit5 X hX hx0 hxl hxh

theorem ok6 : smallOK (1 / 4194304 : ℚ) (1 / 2097152 : ℚ)
    (1048575 / 18446744073709551616 : ℚ)
    (4194305 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit6 : smallRelOK (1 / 4194304 : ℚ) (1 / 2097152 : ℚ)
    (1048575 / 18446744073709551616 : ℚ)
    (4194305 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf6 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 4194304 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 2097152 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok6 crit6 X hX hx0 hxl hxh

theorem ok7 : smallOK (1 / 2097152 : ℚ) (1 / 1048576 : ℚ)
    (4194303 / 18446744073709551616 : ℚ)
    (16777217 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit7 : smallRelOK (1 / 2097152 : ℚ) (1 / 1048576 : ℚ)
    (4194303 / 18446744073709551616 : ℚ)
    (16777217 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf7 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 2097152 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 1048576 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok7 crit7 X hX hx0 hxl hxh

theorem ok8 : smallOK (1 / 1048576 : ℚ) (1 / 524288 : ℚ)
    (16777215 / 18446744073709551616 : ℚ)
    (67108865 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit8 : smallRelOK (1 / 1048576 : ℚ) (1 / 524288 : ℚ)
    (16777215 / 18446744073709551616 : ℚ)
    (67108865 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf8 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 1048576 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 524288 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok8 crit8 X hX hx0 hxl hxh

theorem ok9 : smallOK (1 / 524288 : ℚ) (1 / 262144 : ℚ)
    (67108863 / 18446744073709551616 : ℚ)
    (268435457 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit9 : smallRelOK (1 / 524288 : ℚ) (1 / 262144 : ℚ)
    (67108863 / 18446744073709551616 : ℚ)
    (268435457 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf9 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 524288 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 262144 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok9 crit9 X hX hx0 hxl hxh

theorem ok10 : smallOK (1 / 262144 : ℚ) (1 / 131072 : ℚ)
    (268435455 / 18446744073709551616 : ℚ)
    (1073741825 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit10 : smallRelOK (1 / 262144 : ℚ) (1 / 131072 : ℚ)
    (268435455 / 18446744073709551616 : ℚ)
    (1073741825 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf10 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 262144 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 131072 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok10 crit10 X hX hx0 hxl hxh

theorem ok11 : smallOK (1 / 131072 : ℚ) (1 / 65536 : ℚ)
    (1073741823 / 18446744073709551616 : ℚ)
    (4294967297 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit11 : smallRelOK (1 / 131072 : ℚ) (1 / 65536 : ℚ)
    (1073741823 / 18446744073709551616 : ℚ)
    (4294967297 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf11 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 131072 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 65536 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok11 crit11 X hX hx0 hxl hxh

theorem ok12 : smallOK (1 / 65536 : ℚ) (1 / 32768 : ℚ)
    (4294967295 / 18446744073709551616 : ℚ)
    (17179869185 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit12 : smallRelOK (1 / 65536 : ℚ) (1 / 32768 : ℚ)
    (4294967295 / 18446744073709551616 : ℚ)
    (17179869185 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf12 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 65536 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 32768 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok12 crit12 X hX hx0 hxl hxh

theorem ok13 : smallOK (1 / 32768 : ℚ) (1 / 16384 : ℚ)
    (17179869183 / 18446744073709551616 : ℚ)
    (68719476737 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit13 : smallRelOK (1 / 32768 : ℚ) (1 / 16384 : ℚ)
    (17179869183 / 18446744073709551616 : ℚ)
    (68719476737 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf13 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 32768 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 16384 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok13 crit13 X hX hx0 hxl hxh

theorem ok14 : smallOK (1 / 16384 : ℚ) (1 / 8192 : ℚ)
    (68719476735 / 18446744073709551616 : ℚ)
    (274877906945 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit14 : smallRelOK (1 / 16384 : ℚ) (1 / 8192 : ℚ)
    (68719476735 / 18446744073709551616 : ℚ)
    (274877906945 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf14 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 16384 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 8192 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok14 crit14 X hX hx0 hxl hxh

theorem ok15 : smallOK (1 / 8192 : ℚ) (1 / 4096 : ℚ)
    (274877906943 / 18446744073709551616 : ℚ)
    (1099511627777 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit15 : smallRelOK (1 / 8192 : ℚ) (1 / 4096 : ℚ)
    (274877906943 / 18446744073709551616 : ℚ)
    (1099511627777 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf15 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 8192 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 4096 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok15 crit15 X hX hx0 hxl hxh

theorem ok16 : smallOK (1 / 4096 : ℚ) (1 / 2048 : ℚ)
    (1099511627775 / 18446744073709551616 : ℚ)
    (4398046511105 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit16 : smallRelOK (1 / 4096 : ℚ) (1 / 2048 : ℚ)
    (1099511627775 / 18446744073709551616 : ℚ)
    (4398046511105 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf16 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 4096 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 2048 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok16 crit16 X hX hx0 hxl hxh

theorem ok17 : smallOK (1 / 2048 : ℚ) (1 / 1024 : ℚ)
    (4398046511103 / 18446744073709551616 : ℚ)
    (17592186044417 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit17 : smallRelOK (1 / 2048 : ℚ) (1 / 1024 : ℚ)
    (4398046511103 / 18446744073709551616 : ℚ)
    (17592186044417 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf17 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 2048 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 1024 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok17 crit17 X hX hx0 hxl hxh

theorem ok18 : smallOK (1 / 1024 : ℚ) (1 / 512 : ℚ)
    (17592186044415 / 18446744073709551616 : ℚ)
    (70368744177665 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit18 : smallRelOK (1 / 1024 : ℚ) (1 / 512 : ℚ)
    (17592186044415 / 18446744073709551616 : ℚ)
    (70368744177665 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf18 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 1024 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 512 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok18 crit18 X hX hx0 hxl hxh

theorem ok19 : smallOK (1 / 512 : ℚ) (1 / 256 : ℚ)
    (70368744177663 / 18446744073709551616 : ℚ)
    (281474976710657 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit19 : smallRelOK (1 / 512 : ℚ) (1 / 256 : ℚ)
    (70368744177663 / 18446744073709551616 : ℚ)
    (281474976710657 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf19 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 512 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 256 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok19 crit19 X hX hx0 hxl hxh

theorem ok20 : smallOK (1 / 256 : ℚ) (1 / 128 : ℚ)
    (281474976710655 / 18446744073709551616 : ℚ)
    (1125899906842625 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit20 : smallRelOK (1 / 256 : ℚ) (1 / 128 : ℚ)
    (281474976710655 / 18446744073709551616 : ℚ)
    (1125899906842625 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf20 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 256 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 128 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok20 crit20 X hX hx0 hxl hxh

theorem ok21 : smallOK (1 / 128 : ℚ) (1 / 64 : ℚ)
    (1125899906842623 / 18446744073709551616 : ℚ)
    (4503599627370497 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit21 : smallRelOK (1 / 128 : ℚ) (1 / 64 : ℚ)
    (1125899906842623 / 18446744073709551616 : ℚ)
    (4503599627370497 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf21 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 128 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok21 crit21 X hX hx0 hxl hxh

theorem ok22 : smallOK (1 / 64 : ℚ) (1 / 32 : ℚ)
    (4503599627370495 / 18446744073709551616 : ℚ)
    (18014398509481987 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit22 : smallRelOK (1 / 64 : ℚ) (1 / 32 : ℚ)
    (4503599627370495 / 18446744073709551616 : ℚ)
    (18014398509481987 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf22 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok22 crit22 X hX hx0 hxl hxh

theorem ok23 : smallOK (1 / 32 : ℚ) (1 / 16 : ℚ)
    (18014398509481981 / 18446744073709551616 : ℚ)
    (72057594037927945 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit23 : smallRelOK (1 / 32 : ℚ) (1 / 16 : ℚ)
    (18014398509481981 / 18446744073709551616 : ℚ)
    (72057594037927945 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf23 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok23 crit23 X hX hx0 hxl hxh

theorem ok24 : smallOK (1 / 16 : ℚ) (1 / 8 : ℚ)
    (72057594037927927 / 18446744073709551616 : ℚ)
    (288230376151711777 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit24 : smallRelOK (1 / 16 : ℚ) (1 / 8 : ℚ)
    (72057594037927927 / 18446744073709551616 : ℚ)
    (288230376151711777 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf24 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 8 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok24 crit24 X hX hx0 hxl hxh

theorem ok25 : smallOK (1 / 8 : ℚ) (1 / 4 : ℚ)
    (288230376151711711 / 18446744073709551616 : ℚ)
    (1152921504606847105 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit25 : smallRelOK (1 / 8 : ℚ) (1 / 4 : ℚ)
    (288230376151711711 / 18446744073709551616 : ℚ)
    (1152921504606847105 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf25 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 8 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((1 / 4 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok25 crit25 X hX hx0 hxl hxh

theorem ok26 : smallOK (1 / 4 : ℚ) (17 / 64 : ℚ)
    (1152921504606846847 / 18446744073709551616 : ℚ)
    (1301540292310073489 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit26 : smallRelOK (1 / 4 : ℚ) (17 / 64 : ℚ)
    (1152921504606846847 / 18446744073709551616 : ℚ)
    (1301540292310073489 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf26 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((1 / 4 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((17 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok26 crit26 X hX hx0 hxl hxh

theorem ok27 : smallOK (17 / 64 : ℚ) (9 / 32 : ℚ)
    (1301540292310073199 / 18446744073709551616 : ℚ)
    (1459166279268040867 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit27 : smallRelOK (17 / 64 : ℚ) (9 / 32 : ℚ)
    (1301540292310073199 / 18446744073709551616 : ℚ)
    (1459166279268040867 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf27 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((17 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((9 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok27 crit27 X hX hx0 hxl hxh

theorem ok28 : smallOK (9 / 32 : ℚ) (19 / 64 : ℚ)
    (1459166279268040541 / 18446744073709551616 : ℚ)
    (1625799465480749237 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit28 : smallRelOK (9 / 32 : ℚ) (19 / 64 : ℚ)
    (1459166279268040541 / 18446744073709551616 : ℚ)
    (1625799465480749237 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf28 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((9 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((19 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok28 crit28 X hX hx0 hxl hxh

theorem ok29 : smallOK (19 / 64 : ℚ) (5 / 16 : ℚ)
    (1625799465480748875 / 18446744073709551616 : ℚ)
    (1801439850948198601 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit29 : smallRelOK (19 / 64 : ℚ) (5 / 16 : ℚ)
    (1625799465480748875 / 18446744073709551616 : ℚ)
    (1801439850948198601 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf29 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((19 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((5 / 16 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok29 crit29 X hX hx0 hxl hxh

theorem ok30 : smallOK (5 / 16 : ℚ) (21 / 64 : ℚ)
    (1801439850948198199 / 18446744073709551616 : ℚ)
    (1986087435670388957 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit30 : smallRelOK (5 / 16 : ℚ) (21 / 64 : ℚ)
    (1801439850948198199 / 18446744073709551616 : ℚ)
    (1986087435670388957 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf30 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((5 / 16 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((21 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok30 crit30 X hX hx0 hxl hxh

theorem ok31 : smallOK (21 / 64 : ℚ) (11 / 32 : ℚ)
    (1986087435670388515 / 18446744073709551616 : ℚ)
    (2179742219647320307 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit31 : smallRelOK (21 / 64 : ℚ) (11 / 32 : ℚ)
    (1986087435670388515 / 18446744073709551616 : ℚ)
    (2179742219647320307 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf31 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((21 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((11 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok31 crit31 X hX hx0 hxl hxh

theorem ok32 : smallOK (11 / 32 : ℚ) (23 / 64 : ℚ)
    (2179742219647319821 / 18446744073709551616 : ℚ)
    (2382404202878992649 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit32 : smallRelOK (11 / 32 : ℚ) (23 / 64 : ℚ)
    (2179742219647319821 / 18446744073709551616 : ℚ)
    (2382404202878992649 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf32 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((11 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((23 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok32 crit32 X hX hx0 hxl hxh

theorem ok33 : smallOK (23 / 64 : ℚ) (3 / 8 : ℚ)
    (2382404202878992119 / 18446744073709551616 : ℚ)
    (2594073385365405985 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit33 : smallRelOK (23 / 64 : ℚ) (3 / 8 : ℚ)
    (2382404202878992119 / 18446744073709551616 : ℚ)
    (2594073385365405985 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf33 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((23 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((3 / 8 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok33 crit33 X hX hx0 hxl hxh

theorem ok34 : smallOK (3 / 8 : ℚ) (25 / 64 : ℚ)
    (2594073385365405407 / 18446744073709551616 : ℚ)
    (2814749767106560313 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit34 : smallRelOK (3 / 8 : ℚ) (25 / 64 : ℚ)
    (2594073385365405407 / 18446744073709551616 : ℚ)
    (2814749767106560313 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf34 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((3 / 8 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((25 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok34 crit34 X hX hx0 hxl hxh

theorem ok35 : smallOK (25 / 64 : ℚ) (13 / 32 : ℚ)
    (2814749767106559687 / 18446744073709551616 : ℚ)
    (3044433348102455635 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit35 : smallRelOK (25 / 64 : ℚ) (13 / 32 : ℚ)
    (2814749767106559687 / 18446744073709551616 : ℚ)
    (3044433348102455635 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf35 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((25 / 64 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((13 / 32 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok35 crit35 X hX hx0 hxl hxh

theorem ok36 : smallOK (13 / 32 : ℚ) (27 / 64 : ℚ)
    (3044433348102454957 / 18446744073709551616 : ℚ)
    (3283124128353091949 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem crit36 : smallRelOK (13 / 32 : ℚ) (27 / 64 : ℚ)
    (3044433348102454957 / 18446744073709551616 : ℚ)
    (3283124128353091949 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem erf36 (X : UInt64) (hX : Finite X) (hx0 : 0 < value X)
    (hxl : ((13 / 32 : ℚ) : ℝ) ≤ value X) (hxh : value X ≤ ((27 / 64 : ℚ) : ℝ)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul X (Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul X X))
        (hornerW qqW (Wasm.IEEE64.mul X X))))) :=
  small_erf_rel _ _ _ _ ok36 crit36 X hX hx0 hxl hxh

#print axioms erf0
#print axioms erf1
#print axioms erf2
#print axioms erf3
#print axioms erf4
#print axioms erf5
#print axioms erf6
#print axioms erf7
#print axioms erf8
#print axioms erf9
#print axioms erf10
#print axioms erf11
#print axioms erf12
#print axioms erf13
#print axioms erf14
#print axioms erf15
#print axioms erf16
#print axioms erf17
#print axioms erf18
#print axioms erf19
#print axioms erf20
#print axioms erf21
#print axioms erf22
#print axioms erf23
#print axioms erf24
#print axioms erf25
#print axioms erf26
#print axioms erf27
#print axioms erf28
#print axioms erf29
#print axioms erf30
#print axioms erf31
#print axioms erf32
#print axioms erf33
#print axioms erf34
#print axioms erf35
#print axioms erf36

end Library.Numerics.Float64.Erf.ErfSmallPieces0
