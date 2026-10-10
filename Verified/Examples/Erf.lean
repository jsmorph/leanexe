import Verified.Examples.Exp

/-! The forty-third program of the verified compiler: `erf` and `erfc`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`s_erf.c`,
Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this notice).  Below
`0.84375` in magnitude, `erf x = x + x R (x²)` with a rational function `R` of degrees 4 and 5,
within `2 ^ -57.90` of `(erf x - x)/x`, and `erfc` is `1 - erf x`, or `0.5 - (x R + (x - 0.5))` from
`1/4` on.  Up to `1.25`, both use `erf |x| = c + P (s)/Q (s)` with `s = |x| - 1`, `c` the single
precision `0.84506291151`, and a rational function of degrees 6 and 6 within `2 ^ -59.06`.  Up to
28, `erfc |x| = exp (-x² - 0.5625 + R/S)/|x|` with `R/S` a rational function in `1/x²`, one below
`1/0.35` and another above, within `2 ^ -62.57` and `2 ^ -61.52` of `log (x erfc x) + x² + 0.5625`,
and `-x²` is split at the high 32 bits of `x` so that its first part is exact.  `erf` takes
`1 - erfc |x|` with the sign of `x`, and `±1` from 6 on, and `erfc` takes `2 - erfc |x|` for a
negative `x`, 2 from -6 down, and `1.0e-300²` from 28 up.  fdlibm states errors below one unit in
the last place for `erf` on the first range and states none elsewhere.  fdlibm calls its own `exp`
(`e_exp.c`), and the module calls `Exp.expWith` with the table `Exp.expTable`, Arm's `exp`, which
the module lists, so that the reflector compiles it into this module.  Both state errors below one
unit in the last place, and their results may differ in the last bit.  `erf` and `erfc` pass
`Exp.expTable` to `erfWith` and `erfcWith`.  fdlibm computes the rational functions in each
function, and here `erfSmall`, `erfMiddle`, `erfTail`, and `erfExp` compute them, and the two
exponentials, with the same operations.  Each constant is written as the bit pattern that fdlibm's
source gives beside its decimal value, and `1.0e-300` as the bits of that decimal.  The dialect has
no floating-point flags, and the expressions that fdlibm evaluates only for their flags keep their
values: `1 - tiny`, `tiny - 1`, `2 - tiny`, and `tiny · tiny` stay rounded sums and products.
fdlibm's signed high word `hx` is a word, so a signed comparison with a positive bound also tests
its sign bit.  `ErfAccuracy.lean` checks the results against references computed with Lean's
integers. -/

namespace Verified.Examples.Erf

/-- `s_erf.c`'s `r/s` on `[0, 0.84375]`: `R (x²)`, near `(erf x - x)/x`, from `z = x²`. -/
def erfSmall (z : Float) : Float :=
  let pp0 := Float.ofBits 0x3FC06EBA8214DB68  --  1.28379167095512558561e-01
  let pp1 := Float.ofBits 0xBFD4CD7D691CB913  -- -3.25042107247001499370e-01
  let pp2 := Float.ofBits 0xBF9D2A51DBD7194F  -- -2.84817495755985104766e-02
  let pp3 := Float.ofBits 0xBF77A291236668E4  -- -5.77027029648944159157e-03
  let pp4 := Float.ofBits 0xBEF8EAD6120016AC  -- -2.37630166566501626084e-05
  let qq1 := Float.ofBits 0x3FD97779CDDADC09  --  3.97917223959155352819e-01
  let qq2 := Float.ofBits 0x3FB0A54C5536CEBA  --  6.50222499887672944485e-02
  let qq3 := Float.ofBits 0x3F74D022C4D36B0F  --  5.08130628187576562776e-03
  let qq4 := Float.ofBits 0x3F215DC9221C1A10  --  1.32494738004321644526e-04
  let qq5 := Float.ofBits 0xBED09C4342A26120  -- -3.96022827877536812320e-06
  let r := pp0 + z * (pp1 + z * (pp2 + z * (pp3 + z * pp4)))
  let s := 1.0 + z * (qq1 + z * (qq2 + z * (qq3 + z * (qq4 + z * qq5))))
  r / s

/-- `s_erf.c`'s `P` and `Q` on `[0.84375, 1.25]`, from `s = |x| - 1`: `P/Q` is near
`erf |x| - 0.84506291151`. -/
def erfMiddle (s : Float) : Float × Float :=
  let pa0 := Float.ofBits 0xBF6359B8BEF77538  -- -2.36211856075265944077e-03
  let pa1 := Float.ofBits 0x3FDA8D00AD92B34D  --  4.14856118683748331666e-01
  let pa2 := Float.ofBits 0xBFD7D240FBB8C3F1  -- -3.72207876035701323847e-01
  let pa3 := Float.ofBits 0x3FD45FCA805120E4  --  3.18346619901161753674e-01
  let pa4 := Float.ofBits 0xBFBC63983D3E28EC  -- -1.10894694282396677476e-01
  let pa5 := Float.ofBits 0x3FA22A36599795EB  --  3.54783043256182359371e-02
  let pa6 := Float.ofBits 0xBF61BF380A96073F  -- -2.16637559486879084300e-03
  let qa1 := Float.ofBits 0x3FBB3E6618EEE323  --  1.06420880400844228286e-01
  let qa2 := Float.ofBits 0x3FE14AF092EB6F33  --  5.40397917702171048937e-01
  let qa3 := Float.ofBits 0x3FB2635CD99FE9A7  --  7.18286544141962662868e-02
  let qa4 := Float.ofBits 0x3FC02660E763351F  --  1.26171219808761642112e-01
  let qa5 := Float.ofBits 0x3F8BEDC26B51DD1C  --  1.36370839120290507362e-02
  let qa6 := Float.ofBits 0x3F888B545735151D  --  1.19844998467991074170e-02
  (pa0 + s * (pa1 + s * (pa2 + s * (pa3 + s * (pa4 + s * (pa5 + s * pa6))))),
    1.0 + s * (qa1 + s * (qa2 + s * (qa3 + s * (qa4 + s * (qa5 + s * qa6))))))

/-- `s_erf.c`'s `R` and `S` from `s = 1/x²`: those of `[1.25, 1/0.35)` when `near` holds, and those
of `[1/0.35, 28)` otherwise. -/
def erfTail (s : Float) (near : Bool) : Float × Float :=
  if near then
    let ra0 := Float.ofBits 0xBF843412600D6435  -- -9.86494403484714822705e-03
    let ra1 := Float.ofBits 0xBFE63416E4BA7360  -- -6.93858572707181764372e-01
    let ra2 := Float.ofBits 0xC0251E0441B0E726  -- -1.05586262253232909814e+01
    let ra3 := Float.ofBits 0xC04F300AE4CBA38D  -- -6.23753324503260060396e+01
    let ra4 := Float.ofBits 0xC0644CB184282266  -- -1.62396669462573470355e+02
    let ra5 := Float.ofBits 0xC067135CEBCCABB2  -- -1.84605092906711035994e+02
    let ra6 := Float.ofBits 0xC054526557E4D2F2  -- -8.12874355063065934246e+01
    let ra7 := Float.ofBits 0xC023A0EFC69AC25C  -- -9.81432934416914548592e+00
    let sa1 := Float.ofBits 0x4033A6B9BD707687  --  1.96512716674392571292e+01
    let sa2 := Float.ofBits 0x4061350C526AE721  --  1.37657754143519042600e+02
    let sa3 := Float.ofBits 0x407B290DD58A1A71  --  4.34565877475229228821e+02
    let sa4 := Float.ofBits 0x40842B1921EC2868  --  6.45387271733267880336e+02
    let sa5 := Float.ofBits 0x407AD02157700314  --  4.29008140027567833386e+02
    let sa6 := Float.ofBits 0x405B28A3EE48AE2C  --  1.08635005541779435134e+02
    let sa7 := Float.ofBits 0x401A47EF8E484A93  --  6.57024977031928170135e+00
    let sa8 := Float.ofBits 0xBFAEEFF2EE749A62  -- -6.04244152148580987438e-02
    (ra0 + s * (ra1 + s * (ra2 + s * (ra3 + s * (ra4 + s * (ra5 + s * (ra6 + s * ra7)))))),
      1.0 + s * (sa1 + s * (sa2 + s * (sa3 + s * (sa4 + s * (sa5 + s * (sa6 + s * (sa7 +
        s * sa8))))))))
  else
    let rb0 := Float.ofBits 0xBF84341239E86F4A  -- -9.86494292470009928597e-03
    let rb1 := Float.ofBits 0xBFE993BA70C285DE  -- -7.99283237680523006574e-01
    let rb2 := Float.ofBits 0xC031C209555F995A  -- -1.77579549177547519889e+01
    let rb3 := Float.ofBits 0xC064145D43C5ED98  -- -1.60636384855821916062e+02
    let rb4 := Float.ofBits 0xC083EC881375F228  -- -6.37566443368389627722e+02
    let rb5 := Float.ofBits 0xC09004616A2E5992  -- -1.02509513161107724954e+03
    let rb6 := Float.ofBits 0xC07E384E9BDC383F  -- -4.83519191608651397019e+02
    let sb1 := Float.ofBits 0x403E568B261D5190  --  3.03380607434824582924e+01
    let sb2 := Float.ofBits 0x40745CAE221B9F0A  --  3.25792512996573918826e+02
    let sb3 := Float.ofBits 0x409802EB189D5118  --  1.53672958608443695994e+03
    let sb4 := Float.ofBits 0x40A8FFB7688C246A  --  3.19985821950859553908e+03
    let sb5 := Float.ofBits 0x40A3F219CEDF3BE6  --  2.55305040643316442583e+03
    let sb6 := Float.ofBits 0x407DA874E79FE763  --  4.74528541206955367215e+02
    let sb7 := Float.ofBits 0xC03670E242712D62  -- -2.24409524465858183362e+01
    (rb0 + s * (rb1 + s * (rb2 + s * (rb3 + s * (rb4 + s * (rb5 + s * rb6))))),
      1.0 + s * (sb1 + s * (sb2 + s * (sb3 + s * (sb4 + s * (sb5 + s * (sb6 + s * sb7)))))))

/-- `exp (-z² - 0.5625) · exp ((z - x)(z + x) + R/S)` for `x > 0`, with `z` the high 32 bits of
`x`, so that `z²` is exact: `x erfc x` for `x` from 1.25 to 28. -/
def erfExp (tab : Array UInt64) (x R S : Float) : Float :=
  let z := Float.ofBits (x.toBits &&& 0xFFFFFFFF00000000)
  Exp.expWith tab (-z * z - 0.5625) * Exp.expWith tab ((z - x) * (z + x) + R / S)

/-- fdlibm's `erf` with the table `tab` of `Exp.expWith`.  `hx` is the high word of `x` and `ix`
that of `|x|`.  NaN gives NaN and `±∞` gives `±1`, as `±1 + 1/x`.  Below `2 ^ -28` the result is
`x + efx x`, computed as `(8 x + efx8 x)/8` below `2 ^ -1015` so that no product underflows. -/
def erfWith (tab : Array UInt64) (x : Float) : Float :=
  let erx := Float.ofBits 0x3FEB0AC160000000   --  8.45062911510467529297e-01
  let efx := Float.ofBits 0x3FC06EBA8214DB69   --  1.28379167095512586316e-01
  let efx8 := Float.ofBits 0x3FF06EBA8214DB69  --  1.02703333676410069053e+00
  let tiny := Float.ofBits 0x01A56E1FC2F8F359  --  1.0e-300
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let neg := hx >>> 31 == 1
  if ix ≥ 0x7ff00000 then (if neg then -1.0 else 1.0) + 1.0 / x
  else if ix < 0x3feb0000 then
    if ix < 0x3e300000 then
      if ix < 0x00800000 then (8.0 * x + efx8 * x) / 8.0 else x + efx * x
    else x + x * erfSmall (x * x)
  else if ix < 0x3ff40000 then
    let (P, Q) := erfMiddle (x.abs - 1.0)
    if neg then -erx - P / Q else erx + P / Q
  else if ix ≥ 0x40180000 then if neg then tiny - 1.0 else 1.0 - tiny
  else
    let x := x.abs
    let (R, S) := erfTail (1.0 / (x * x)) (ix < 0x4006DB6E)
    let r := erfExp tab x R S
    if neg then r / x - 1.0 else 1.0 - r / x

/-- fdlibm's `erfc` with the table `tab` of `Exp.expWith`.  `hx` is the high word of `x` and `ix`
that of `|x|`.  NaN gives NaN, `+∞` gives 0 and `-∞` gives 2, as `0 + 1/x` and `2 + 1/x`.  Below
`2 ^ -56` the result is `1 - x`. -/
def erfcWith (tab : Array UInt64) (x : Float) : Float :=
  let erx := Float.ofBits 0x3FEB0AC160000000   --  8.45062911510467529297e-01
  let tiny := Float.ofBits 0x01A56E1FC2F8F359  --  1.0e-300
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let neg := hx >>> 31 == 1
  if ix ≥ 0x7ff00000 then (if neg then 2.0 else 0.0) + 1.0 / x
  else if ix < 0x3feb0000 then
    if ix < 0x3c700000 then 1.0 - x
    else
      let y := erfSmall (x * x)
      if neg || hx < 0x3fd00000 then 1.0 - (x + x * y)
      else
        let r := x * y
        let r := r + (x - 0.5)
        0.5 - r
  else if ix < 0x3ff40000 then
    let (P, Q) := erfMiddle (x.abs - 1.0)
    if neg then 1.0 + (erx + P / Q) else (1.0 - erx) - P / Q
  else if ix < 0x403c0000 then
    if neg && ix ≥ 0x4006DB6D && ix ≥ 0x40180000 then 2.0 - tiny
    else
      let x := x.abs
      let (R, S) := erfTail (1.0 / (x * x)) (ix < 0x4006DB6D)
      let r := erfExp tab x R S
      if neg then 2.0 - r / x else r / x
  else if neg then 2.0 - tiny else tiny * tiny

/-- `erf x`, with the table `Exp.expTable`. -/
def erf (x : Float) : Float := erfWith Exp.expTable x

/-- `erfc x`, with the table `Exp.expTable`. -/
def erfc (x : Float) : Float := erfcWith Exp.expTable x

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, erfSmall, erfMiddle,
  erfTail, erfExp, erfWith, erfcWith, erf, erfc]

end Verified.Examples.Erf
