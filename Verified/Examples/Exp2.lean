import Verified.Examples.Exp

/-! The thirty-eighth program of the verified compiler: `exp2` and `exp10`, ported from Arm's
optimized-routines, `math/exp2.c`, `math/exp10.c`, and `math/exp_data.c` at commit
`503fafe311c177de0e571c458c7c337b1ca5f522` (Copyright (c) 2018-2025 and 2023-2025, Arm Limited,
SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception).  The configuration is that of
`Exp.lean`: without rounding intrinsics or fused multiply-add, `EXP_TABLE_BITS` 7, so `N` is 128,
`EXP2_POLY_ORDER` 5, and `EXP10_POLY_WIDE` 0.  Both write their argument as `k/N + r`, `exp2`
with `k` the rounded `x N` and `exp10` with `k` the rounded `x N/log10 2` and `r` reduced by
`log10 2/N` in two parts, and both take `2 ^ (k/N)` as `H j · (1 + T j)` from `__exp_data.tab`,
which is `Exp.expTable` word for word, and a polynomial of degree 5 in `r` for the rest.  Arm
states 0.511 units in the last place for `exp2` without fused multiply-add and about 0.513 for
`exp10`.  Results near overflow and underflow go through `exp2SpecialCase`, which is
`exp2.c`'s `specialcase` and `exp10.c`'s `special_case`, the same code, and which differs from
`exp.c`'s in scaling a positive `k` by 2 rather than `2 ^ 1009`.  `exp2` and `exp10` pass
`Exp.expTable` to `exp2With` and `exp10With`.  Each constant is written as the bit pattern of its
value in Arm's source, the products and quotients by `N` included, and the results of
`__math_oflow` and `__math_uflow` from `math/math_err.c` as the products that compute them.  The
dialect has no floating-point flags, and the expressions that Arm evaluates only for its flags are
left out, as in `Exp.lean`.  `Exp2Accuracy.lean` checks the results against references computed
with Lean's integers. -/

namespace Verified.Examples.Exp2

/-- `exp2.c`'s `specialcase` and `exp10.c`'s `special_case`: `scale · (1 + tmp)` for a result
that may overflow or underflow, with `sbits` the bits of `scale` whose exponent may have wrapped
and the sign bit of the low 32 bits of `ki` the sign of `k`.  A positive `k` doubles the product
of the scale lowered by one binade.  A negative `k` scales by `2 ^ -1022`, and a result below 1
before the scaling is first rounded to the precision that the subnormal range keeps. -/
def exp2SpecialCase (tmp : Float) (sbits ki : UInt64) : Float :=
  if ki &&& 0x80000000 == 0 then
    let scale := Float.ofBits (sbits - ((1 : UInt64) <<< (52 : UInt64)))
    2.0 * (scale + scale * tmp)
  else
    let scale := Float.ofBits (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
    let y := scale + scale * tmp
    let y := if y < 1.0 then
        let lo := scale - y + scale * tmp
        let hi := 1.0 + y
        let lo := 1.0 - hi + y + lo
        let y := hi + lo - 1.0
        if y == 0.0 then 0.0 else y
      else y
    Float.ofBits 0x0010000000000000 * y

/-- The reduction and the polynomial of Arm's `exp2`, through `exp2SpecialCase` when `special`
holds. -/
def exp2Core (tab : Array UInt64) (x : Float) (special : Bool) : Float :=
  let shift := Float.ofBits 0x42C8000000000000  -- 0x1.8p52 / N
  let C1 := Float.ofBits 0x3FE62E42FEFA39EF     -- 0x1.62e42fefa39efp-1
  let C2 := Float.ofBits 0x3FCEBFBDFF82C424     -- 0x1.ebfbdff82c424p-3
  let C3 := Float.ofBits 0x3FAC6B08D70CF4B5     -- 0x1.c6b08d70cf4b5p-5
  let C4 := Float.ofBits 0x3F83B2ABD24650CC     -- 0x1.3b2abd24650ccp-7
  let C5 := Float.ofBits 0x3F55D7E09B4E3A84     -- 0x1.5d7e09b4e3a84p-10
  let kd := x + shift
  let ki := kd.toBits
  let kd := kd - shift
  let r := x - kd
  let idx := 2 * (ki % 128)
  let top := ki <<< (45 : UInt64)
  let tail := Float.ofBits tab[idx.toNat]!
  let sbits := tab[(idx + 1).toNat]! + top
  let r2 := r * r
  let tmp := tail + r * C1 + r2 * (C2 + r * C3) + r2 * r2 * (C4 + r * C5)
  if special then exp2SpecialCase tmp sbits ki
  else
    let scale := Float.ofBits sbits
    scale + scale * tmp

/-- Arm's `exp2` with the table `tab`.  `abstop` is the biased exponent of `x`.  Below `2 ^ -54`
the result is `1 + x`.  From 1024 on in magnitude, `-∞` gives 0, an infinity or NaN `1 + x`, a
positive `x` the overflow product, and an `x` at or below -1075 the underflow product.  Above 928
in magnitude, -1075 to -1024 included, the result goes through `exp2SpecialCase`.  The thresholds
are `top12 (0x1p-54) = 0x3c9`, `top12 (512) = 0x408`, `top12 (1024) = 0x409`, and the bits of
`-1075` and `928`. -/
def exp2With (tab : Array UInt64) (x : Float) : Float :=
  let abstop := (x.toBits >>> 52) &&& 0x7ff
  if abstop - 0x3c9 ≥ 0x408 - 0x3c9 then
    if abstop - 0x3c9 ≥ 0x80000000 then 1.0 + x
    else if abstop ≥ 0x409 && x.toBits == 0xFFF0000000000000 then 0.0
    else if abstop ≥ 0x409 && abstop ≥ 0x7ff then 1.0 + x
    else if abstop ≥ 0x409 && x.toBits >>> 63 == 0 then
      Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
    else if abstop ≥ 0x409 && x.toBits ≥ 0xC090CC0000000000 then
      Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
    else exp2Core tab x (2 * x.toBits > 2 * 0x408D000000000000)
  else exp2Core tab x false

/-- The reduction and the polynomial of Arm's `exp10`, through `exp2SpecialCase` when `special`
holds. -/
def exp10Core (tab : Array UInt64) (x : Float) (special : Bool) : Float :=
  let shift := Float.ofBits 0x4338000000000000          -- 0x1.8p52
  let invlog10_2N := Float.ofBits 0x407A934F0979A371    -- 0x1.a934f0979a371p1 * N
  let neglog10_2hiN := Float.ofBits 0xBF63441350A00000  -- -0x1.3441350ap-2 / N
  let neglog10_2loN := Float.ofBits 0x3D10C0219DC1DA99  -- 0x1.0c0219dc1da99p-39 / N
  let C0 := Float.ofBits 0x40026BB1BBB55516  -- 0x1.26bb1bbb55516p1
  let C1 := Float.ofBits 0x40053524C73CE9FE  -- 0x1.53524c73ce9fep1
  let C2 := Float.ofBits 0x4000470591CE4B26  -- 0x1.0470591ce4b26p1
  let C3 := Float.ofBits 0x3FF2BD76577FE684  -- 0x1.2bd76577fe684p0
  let C4 := Float.ofBits 0x3FE1446EECCD0EFB  -- 0x1.1446eeccd0efbp-1
  let z := invlog10_2N * x
  let kd := z + shift
  let ki := kd.toBits
  let kd := kd - shift
  let r := neglog10_2hiN * kd + x
  let r := neglog10_2loN * kd + r
  let e := ki <<< (45 : UInt64)
  let i := (ki &&& 127) * 2
  let sbits := tab[(i + 1).toNat]! + e
  let tail := Float.ofBits tab[i.toNat]!
  let r2 := r * r
  let p := C0 + r * C1
  let y := C2 + r * C3
  let y := y + r2 * C4
  let y := p + r2 * y
  let y := tail + y * r
  if special then exp2SpecialCase y sbits ki
  else
    let s := Float.ofBits sbits
    s * y + s

/-- Arm's `exp10` with the table `tab`.  `abstop` is the biased exponent of `x`.  Below `2 ^ -57`
the result is `x + 1`.  From 256 on in magnitude, `-∞` gives 0, an infinity or NaN `x + 1`, an
`x` at or above `log10 (DBL_MAX)` the overflow product, one below -350 the underflow product, and
the others go through `exp2SpecialCase`.  The thresholds are `top12 (0x1p-57) = 0x3c6` and
`top12 (0x1p8) - top12 (0x1p-57) = 0x41`. -/
def exp10With (tab : Array UInt64) (x : Float) : Float :=
  let oflowBound := Float.ofBits 0x40734413509F79FF  -- 0x1.34413509f79ffp8
  let uflowBound := Float.ofBits 0xC075E00000000000  -- -0x1.5ep+8
  let ix := x.toBits
  let abstop := (ix >>> 52) &&& 0x7ff
  if abstop - 0x3c6 ≥ 0x41 then
    if abstop - 0x3c6 ≥ 0x80000000 then x + 1.0
    else if abstop == 0x7ff then if ix == 0xFFF0000000000000 then 0.0 else x + 1.0
    else if x ≥ oflowBound then Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
    else if x < uflowBound then Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
    else exp10Core tab x true
  else exp10Core tab x false

/-- `2 ^ x`, with the table `Exp.expTable`. -/
def exp2 (x : Float) : Float := exp2With Exp.expTable x

/-- `10 ^ x`, with the table `Exp.expTable`. -/
def exp10 (x : Float) : Float := exp10With Exp.expTable x

verified_compile compiled := [exp2SpecialCase, exp2Core, exp2With, exp10Core, exp10With, exp2,
  exp10]

end Verified.Examples.Exp2
