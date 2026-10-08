import Verified.Reflect.Command

/-! The twenty-eighth program of the verified compiler: `exp`, ported from Arm's
optimized-routines, `math/exp.c` and `math/exp_data.c` at commit
`503fafe311c177de0e571c458c7c337b1ca5f522` (Copyright (c) 2018-2025, Arm Limited,
SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception).  The configuration is the one
for a target without rounding intrinsics or fused multiply-add: `EXP_TABLE_BITS` 7, so `N` is
128, `EXP_POLY_ORDER` 5, `EXP_USE_TOINT_NARROW` 0, and the rounding of `x · N/ln 2` by adding
`0x1.8p52`.  The reduction writes `x = k ln 2/N + r`, with `|r|` at most `ln 2/(2 N)` plus the
rounding error of `x · N/ln 2`, and `exp x = 2 ^ (k/N) · exp r`, where a table of 256 words gives
`2 ^ (j/N)` for `j = k mod N` as `H j · (1 + T j)` and a polynomial of degree 5 gives
`exp r - 1`.  Arm states an error of 0.511 units in the last place without fused multiply-add.
The module holds the table in a data segment: `expWith` takes it as a parameter, and `exp` passes
it.  Each constant is written as the bit pattern of its value in Arm's source: `InvLn2N` is the
product `0x1.71547652b82fep0 · N`, which is exact, and the factors `2 ^ -767` and `2 ^ 769` of
the results that underflow and overflow are those of `math/math_err.c`.  `ExpAccuracy.lean`
checks the results against a reference computed with Lean's integers. -/

namespace Verified.Examples.Exp

/-- Arm's `__exp_data.tab` for `N = 128`: for `j` below 128, word `2 j` is the bits of `T j` and
word `2 j + 1` is the bits of `H j` minus `j · 2 ^ 52 / N`, where `2 ^ (j/N) ≈ H j · (1 + T j)`. -/
def expTable : Array UInt64 :=
  #[
    0x0000000000000000, 0x3FF0000000000000, 0x3C9B3B4F1A88BF6E, 0x3FEFF63DA9FB3335,
    0xBC7160139CD8DC5D, 0x3FEFEC9A3E778061, 0xBC905E7A108766D1, 0x3FEFE315E86E7F85,
    0x3C8CD2523567F613, 0x3FEFD9B0D3158574, 0xBC8BCE8023F98EFA, 0x3FEFD06B29DDF6DE,
    0x3C60F74E61E6C861, 0x3FEFC74518759BC8, 0x3C90A3E45B33D399, 0x3FEFBE3ECAC6F383,
    0x3C979AA65D837B6D, 0x3FEFB5586CF9890F, 0x3C8EB51A92FDEFFC, 0x3FEFAC922B7247F7,
    0x3C3EBE3D702F9CD1, 0x3FEFA3EC32D3D1A2, 0xBC6A033489906E0B, 0x3FEF9B66AFFED31B,
    0xBC9556522A2FBD0E, 0x3FEF9301D0125B51, 0xBC5080EF8C4EEA55, 0x3FEF8ABDC06C31CC,
    0xBC91C923B9D5F416, 0x3FEF829AAEA92DE0, 0x3C80D3E3E95C55AF, 0x3FEF7A98C8A58E51,
    0xBC801B15EAA59348, 0x3FEF72B83C7D517B, 0xBC8F1FF055DE323D, 0x3FEF6AF9388C8DEA,
    0x3C8B898C3F1353BF, 0x3FEF635BEB6FCB75, 0xBC96D99C7611EB26, 0x3FEF5BE084045CD4,
    0x3C9AECF73E3A2F60, 0x3FEF54873168B9AA, 0xBC8FE782CB86389D, 0x3FEF4D5022FCD91D,
    0x3C8A6F4144A6C38D, 0x3FEF463B88628CD6, 0x3C807A05B0E4047D, 0x3FEF3F49917DDC96,
    0x3C968EFDE3A8A894, 0x3FEF387A6E756238, 0x3C875E18F274487D, 0x3FEF31CE4FB2A63F,
    0x3C80472B981FE7F2, 0x3FEF2B4565E27CDD, 0xBC96B87B3F71085E, 0x3FEF24DFE1F56381,
    0x3C82F7E16D09AB31, 0x3FEF1E9DF51FDEE1, 0xBC3D219B1A6FBFFA, 0x3FEF187FD0DAD990,
    0x3C8B3782720C0AB4, 0x3FEF1285A6E4030B, 0x3C6E149289CECB8F, 0x3FEF0CAFA93E2F56,
    0x3C834D754DB0ABB6, 0x3FEF06FE0A31B715, 0x3C864201E2AC744C, 0x3FEF0170FC4CD831,
    0x3C8FDD395DD3F84A, 0x3FEEFC08B26416FF, 0xBC86A3803B8E5B04, 0x3FEEF6C55F929FF1,
    0xBC924AEDCC4B5068, 0x3FEEF1A7373AA9CB, 0xBC9907F81B512D8E, 0x3FEEECAE6D05D866,
    0xBC71D1E83E9436D2, 0x3FEEE7DB34E59FF7, 0xBC991919B3CE1B15, 0x3FEEE32DC313A8E5,
    0x3C859F48A72A4C6D, 0x3FEEDEA64C123422, 0xBC9312607A28698A, 0x3FEEDA4504AC801C,
    0xBC58A78F4817895B, 0x3FEED60A21F72E2A, 0xBC7C2C9B67499A1B, 0x3FEED1F5D950A897,
    0x3C4363ED60C2AC11, 0x3FEECE086061892D, 0x3C9666093B0664EF, 0x3FEECA41ED1D0057,
    0x3C6ECCE1DAA10379, 0x3FEEC6A2B5C13CD0, 0x3C93FF8E3F0F1230, 0x3FEEC32AF0D7D3DE,
    0x3C7690CEBB7AAFB0, 0x3FEEBFDAD5362A27, 0x3C931DBDEB54E077, 0x3FEEBCB299FDDD0D,
    0xBC8F94340071A38E, 0x3FEEB9B2769D2CA7, 0xBC87DECCDC93A349, 0x3FEEB6DAA2CF6642,
    0xBC78DEC6BD0F385F, 0x3FEEB42B569D4F82, 0xBC861246EC7B5CF6, 0x3FEEB1A4CA5D920F,
    0x3C93350518FDD78E, 0x3FEEAF4736B527DA, 0x3C7B98B72F8A9B05, 0x3FEEAD12D497C7FD,
    0x3C9063E1E21C5409, 0x3FEEAB07DD485429, 0x3C34C7855019C6EA, 0x3FEEA9268A5946B7,
    0x3C9432E62B64C035, 0x3FEEA76F15AD2148, 0xBC8CE44A6199769F, 0x3FEEA5E1B976DC09,
    0xBC8C33C53BEF4DA8, 0x3FEEA47EB03A5585, 0xBC845378892BE9AE, 0x3FEEA34634CCC320,
    0xBC93CEDD78565858, 0x3FEEA23882552225, 0x3C5710AA807E1964, 0x3FEEA155D44CA973,
    0xBC93B3EFBF5E2228, 0x3FEEA09E667F3BCD, 0xBC6A12AD8734B982, 0x3FEEA012750BDABF,
    0xBC6367EFB86DA9EE, 0x3FEE9FB23C651A2F, 0xBC80DC3D54E08851, 0x3FEE9F7DF9519484,
    0xBC781F647E5A3ECF, 0x3FEE9F75E8EC5F74, 0xBC86EE4AC08B7DB0, 0x3FEE9F9A48A58174,
    0xBC8619321E55E68A, 0x3FEE9FEB564267C9, 0x3C909CCB5E09D4D3, 0x3FEEA0694FDE5D3F,
    0xBC7B32DCB94DA51D, 0x3FEEA11473EB0187, 0x3C94ECFD5467C06B, 0x3FEEA1ED0130C132,
    0x3C65EBE1ABD66C55, 0x3FEEA2F336CF4E62, 0xBC88A1C52FB3CF42, 0x3FEEA427543E1A12,
    0xBC9369B6F13B3734, 0x3FEEA589994CCE13, 0xBC805E843A19FF1E, 0x3FEEA71A4623C7AD,
    0xBC94D450D872576E, 0x3FEEA8D99B4492ED, 0x3C90AD675B0E8A00, 0x3FEEAAC7D98A6699,
    0x3C8DB72FC1F0EAB4, 0x3FEEACE5422AA0DB, 0xBC65B6609CC5E7FF, 0x3FEEAF3216B5448C,
    0x3C7BF68359F35F44, 0x3FEEB1AE99157736, 0xBC93091FA71E3D83, 0x3FEEB45B0B91FFC6,
    0xBC5DA9B88B6C1E29, 0x3FEEB737B0CDC5E5, 0xBC6C23F97C90B959, 0x3FEEBA44CBC8520F,
    0xBC92434322F4F9AA, 0x3FEEBD829FDE4E50, 0xBC85CA6CD7668E4B, 0x3FEEC0F170CA07BA,
    0x3C71AFFC2B91CE27, 0x3FEEC49182A3F090, 0x3C6DD235E10A73BB, 0x3FEEC86319E32323,
    0xBC87C50422622263, 0x3FEECC667B5DE565, 0x3C8B1C86E3E231D5, 0x3FEED09BEC4A2D33,
    0xBC91BBD1D3BCBB15, 0x3FEED503B23E255D, 0x3C90CC319CEE31D2, 0x3FEED99E1330B358,
    0x3C8469846E735AB3, 0x3FEEDE6B5579FDBF, 0xBC82DFCD978E9DB4, 0x3FEEE36BBFD3F37A,
    0x3C8C1A7792CB3387, 0x3FEEE89F995AD3AD, 0xBC907B8F4AD1D9FA, 0x3FEEEE07298DB666,
    0xBC55C3D956DCAEBA, 0x3FEEF3A2B84F15FB, 0xBC90A40E3DA6F640, 0x3FEEF9728DE5593A,
    0xBC68D6F438AD9334, 0x3FEEFF76F2FB5E47, 0xBC91EEE26B588A35, 0x3FEF05B030A1064A,
    0x3C74FFD70A5FDDCD, 0x3FEF0C1E904BC1D2, 0xBC91BDFBFA9298AC, 0x3FEF12C25BD71E09,
    0x3C736EAE30AF0CB3, 0x3FEF199BDD85529C, 0x3C8EE3325C9FFD94, 0x3FEF20AB5FFFD07A,
    0x3C84E08FD10959AC, 0x3FEF27F12E57D14B, 0x3C63CDAF384E1A67, 0x3FEF2F6D9406E7B5,
    0x3C676B2C6C921968, 0x3FEF3720DCEF9069, 0xBC808A1883CCB5D2, 0x3FEF3F0B555DC3FA,
    0xBC8FAD5D3FFFFA6F, 0x3FEF472D4A07897C, 0xBC900DAE3875A949, 0x3FEF4F87080D89F2,
    0x3C74A385A63D07A7, 0x3FEF5818DCFBA487, 0xBC82919E2040220F, 0x3FEF60E316C98398,
    0x3C8E5A50D5C192AC, 0x3FEF69E603DB3285, 0x3C843A59AC016B4B, 0x3FEF7321F301B460,
    0xBC82D52107B43E1F, 0x3FEF7C97337B9B5F, 0xBC892AB93B470DC9, 0x3FEF864614F5A129,
    0x3C74B604603A88D3, 0x3FEF902EE78B3FF6, 0x3C83C5EC519D7271, 0x3FEF9A51FBC74C83,
    0xBC8FF7128FD391F0, 0x3FEFA4AFA2A490DA, 0xBC8DAE98E223747D, 0x3FEFAF482D8E67F1,
    0x3C8EC3BC41AA2008, 0x3FEFBA1BEE615A27, 0x3C842B94C3A9EB32, 0x3FEFC52B376BBA97,
    0x3C8A64A931D185EE, 0x3FEFD0765B6E4540, 0xBC8E37BAE43BE3ED, 0x3FEFDBFDAD9CBE14,
    0x3C77893B4D91CD9D, 0x3FEFE7C1819E90D8, 0x3C5305C14160CC89, 0x3FEFF3C22B8F71F1]

/-- Arm's `specialcase`: `scale · (1 + tmp)` for a result that may overflow or underflow, where
`sbits` holds the bits of `scale` with an exponent that may have wrapped, and the sign bit of the
low 32 bits of `ki` is the sign of `k`.  A positive `k` scales by `2 ^ 1009` after the product.  A
negative `k` scales by `2 ^ -1022`, and a result below 1 before the scaling is first rounded to
the precision that the subnormal range keeps, by adding and subtracting 1. -/
def specialCase (tmp : Float) (sbits ki : UInt64) : Float :=
  if ki &&& 0x80000000 == 0 then
    let scale := Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64)))
    Float.ofBits 0x7F00000000000000 * (scale + scale * tmp)
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

/-- The reduction and the polynomial of Arm's `exp_inline` with `xtail` 0, for `x` with
`2 ^ -54 ≤ |x| < 1024`, through `specialCase` when `special` holds, as for `512 ≤ |x|`. -/
def expCore (tab : Array UInt64) (x : Float) (special : Bool) : Float :=
  let z := Float.ofBits 0x40671547652B82FE * x
  let kd := z + Float.ofBits 0x4338000000000000
  let ki := kd.toBits
  let kd := kd - Float.ofBits 0x4338000000000000
  let r := x + kd * Float.ofBits 0xBF762E42FEFA0000 + kd * Float.ofBits 0xBD0CF79ABC9E3B3A
  let idx := 2 * (ki % 128)
  let top := ki <<< (45 : UInt64)
  let tail := Float.ofBits tab[idx.toNat]!
  let sbits := tab[(idx + 1).toNat]! + top
  let r2 := r * r
  let tmp := tail + r +
    r2 * (Float.ofBits 0x3FDFFFFFFFFFFDBD + r * Float.ofBits 0x3FC555555555543C) +
    r2 * r2 * (Float.ofBits 0x3FA55555CF172B91 + r * Float.ofBits 0x3F81111167A4D017)
  if special then specialCase tmp sbits ki
  else
    let scale := Float.ofBits sbits
    scale + scale * tmp

/-- Arm's `exp` with the table `tab`.  `abstop` is the biased exponent of `x`.  Below `2 ^ -54`
the result is `1 + x`; from 512 on, the reduction runs through `specialCase`; from 1024 on, `-∞`
gives 0, an infinity or NaN gives `1 + x`, and other values give the products by which Arm's
`__math_uflow` and `__math_oflow` produce 0 and `∞`.  Arm compares 32-bit words, where
`abstop - 0x3c9` wraps for `abstop < 0x3c9`; the comparisons on 64-bit words give the same
results, since the wrapped difference is at least `2 ^ 32 - 0x3c9` either way. -/
def expWith (tab : Array UInt64) (x : Float) : Float :=
  let abstop := (x.toBits >>> 52) &&& 0x7ff
  if abstop - 0x3c9 ≥ 0x408 - 0x3c9 then
    if abstop - 0x3c9 ≥ 0x80000000 then 1.0 + x
    else if abstop ≥ 0x409 then
      if x.toBits == 0xFFF0000000000000 then 0.0
      else if abstop ≥ 0x7ff then 1.0 + x
      else if x.toBits >>> 63 == 1 then
        Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
      else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
    else expCore tab x true
  else expCore tab x false

/-- `exp x`, from the table `expTable`. -/
def exp (x : Float) : Float := expWith expTable x

verified_compile compiled := [specialCase, expCore, expWith, exp]

end Verified.Examples.Exp
