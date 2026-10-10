import Verified.Examples.Exp

/-! The forty-first program of the verified compiler: `pow`, ported from Arm's optimized-routines,
`math/pow.c`, `math/pow_common.h`, and `math/pow_log_data.c` at commit
`503fafe311c177de0e571c458c7c337b1ca5f522` (Copyright (c) 2018-2026, Arm Limited,
SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception).  The configuration is the one for
a target without fused multiply-add or rounding intrinsics: `POW_LOG_TABLE_BITS` 7,
`POW_LOG_POLY_ORDER` 8, `EXP_TABLE_BITS` 7, and `EXP_POLY_ORDER` 5.  `pow x y` is
`exp (y log |x|)` with the sign of `x` for an odd integer `y`.  `powLog` computes `log |x|` as
`hi + lo`, about 15 bits more precise than a double, from a table of 128 subintervals whose
entries `1/c` have few bits, so that `z/c - 1` is exact, and whose `log c` is split in two.
`powMain` multiplies by `y` with both factors split at bit 27, and `powExp` is Arm's `exp_inline`
with the tail `elo` and the sign: the reduction, polynomial, and table of `Exp.lean`, whose table
`__exp_data.tab` is `Exp.expTable` word for word.  `powSpecialCase` scales results near overflow
and underflow and differs from `exp.c`'s `specialcase`: it keeps the sign of a negative result and
rounds `scale + scale · tmp` by its magnitude.  Arm states a worst-case error of 0.54 units in the
last place.  `powWith` handles the special cases of C99's Annex F: a zero, infinite, or NaN `y`; a
zero, infinite, or NaN `x`, with the sign for an odd integer `y`; a negative finite `x`, which needs
an integer `y` and takes the sign of an odd one; `|y|` below `2 ^ -65`, which gives `1 ± y`; and
`|y|` from `2 ^ 63` on, which overflows or underflows.  `pow` passes the tables `powLogTable` and
`Exp.expTable`.  Each constant is written as the bit pattern of its value in Arm's source, the
products of the polynomial coefficients with their scale factors included, and the results of
`__math_oflow`, `__math_uflow`, and `__math_invalid` as the expressions that compute them.  The
dialect has no floating-point flags, and the expressions that Arm evaluates only for its flags or
its rounding mode keep their values: the test `1 + 2 ^ -60 != 1` of `specialcase` stays, false in
rounding to nearest.  `WANT_ERRNO` is 0, so the division by zero of `__math_divzero` does not
occur.  `PowAccuracy.lean` checks the results against a reference computed with Lean's integers. -/

namespace Verified.Examples.Pow

/-- Arm's `__pow_log_data.tab` for `N = 128`: words `4 i` to `4 i + 3` are the bits of `invc`, the
unused `pad`, `logc`, and `logctail` of subinterval `i`, where `1/c` is `invc` and
`logc + logctail` is `log c`. -/
def powLogTable : Array UInt64 :=
  #[
    0x3FF6A00000000000, 0x0000000000000000, 0xBFD62C82F2B9C800, 0x3CFAB42428375680,
    0x3FF6800000000000, 0x0000000000000000, 0xBFD5D1BDBF580800, 0xBD1CA508D8E0F720,
    0x3FF6600000000000, 0x0000000000000000, 0xBFD5767717455800, 0xBD2362A4D5B6506D,
    0x3FF6400000000000, 0x0000000000000000, 0xBFD51AAD872DF800, 0xBCE684E49EB067D5,
    0x3FF6200000000000, 0x0000000000000000, 0xBFD4BE5F95777800, 0xBD041B6993293EE0,
    0x3FF6000000000000, 0x0000000000000000, 0xBFD4618BC21C6000, 0x3D13D82F484C84CC,
    0x3FF5E00000000000, 0x0000000000000000, 0xBFD404308686A800, 0x3CDC42F3ED820B3A,
    0x3FF5C00000000000, 0x0000000000000000, 0xBFD3A64C55694800, 0x3D20B1C686519460,
    0x3FF5A00000000000, 0x0000000000000000, 0xBFD347DD9A988000, 0x3D25594DD4C58092,
    0x3FF5800000000000, 0x0000000000000000, 0xBFD2E8E2BAE12000, 0x3D267B1E99B72BD8,
    0x3FF5600000000000, 0x0000000000000000, 0xBFD2895A13DE8800, 0x3D15CA14B6CFB03F,
    0x3FF5600000000000, 0x0000000000000000, 0xBFD2895A13DE8800, 0x3D15CA14B6CFB03F,
    0x3FF5400000000000, 0x0000000000000000, 0xBFD22941FBCF7800, 0xBD165A242853DA76,
    0x3FF5200000000000, 0x0000000000000000, 0xBFD1C898C1699800, 0xBD1FAFBC68E75404,
    0x3FF5000000000000, 0x0000000000000000, 0xBFD1675CABABA800, 0x3D1F1FC63382A8F0,
    0x3FF4E00000000000, 0x0000000000000000, 0xBFD1058BF9AE4800, 0xBD26A8C4FD055A66,
    0x3FF4C00000000000, 0x0000000000000000, 0xBFD0A324E2739000, 0xBD0C6BEE7EF4030E,
    0x3FF4A00000000000, 0x0000000000000000, 0xBFD0402594B4D000, 0xBCF036B89EF42D7F,
    0x3FF4A00000000000, 0x0000000000000000, 0xBFD0402594B4D000, 0xBCF036B89EF42D7F,
    0x3FF4800000000000, 0x0000000000000000, 0xBFCFB9186D5E4000, 0x3D0D572AAB993C87,
    0x3FF4600000000000, 0x0000000000000000, 0xBFCEF0ADCBDC6000, 0x3D2B26B79C86AF24,
    0x3FF4400000000000, 0x0000000000000000, 0xBFCE27076E2AF000, 0xBD172F4F543FFF10,
    0x3FF4200000000000, 0x0000000000000000, 0xBFCD5C216B4FC000, 0x3D21BA91BBCA681B,
    0x3FF4000000000000, 0x0000000000000000, 0xBFCC8FF7C79AA000, 0x3D27794F689F8434,
    0x3FF4000000000000, 0x0000000000000000, 0xBFCC8FF7C79AA000, 0x3D27794F689F8434,
    0x3FF3E00000000000, 0x0000000000000000, 0xBFCBC286742D9000, 0x3D194EB0318BB78F,
    0x3FF3C00000000000, 0x0000000000000000, 0xBFCAF3C94E80C000, 0x3CBA4E633FCD9066,
    0x3FF3A00000000000, 0x0000000000000000, 0xBFCA23BC1FE2B000, 0xBD258C64DC46C1EA,
    0x3FF3A00000000000, 0x0000000000000000, 0xBFCA23BC1FE2B000, 0xBD258C64DC46C1EA,
    0x3FF3800000000000, 0x0000000000000000, 0xBFC9525A9CF45000, 0xBD2AD1D904C1D4E3,
    0x3FF3600000000000, 0x0000000000000000, 0xBFC87FA06520D000, 0x3D2BBDBF7FDBFA09,
    0x3FF3400000000000, 0x0000000000000000, 0xBFC7AB890210E000, 0x3D2BDB9072534A58,
    0x3FF3400000000000, 0x0000000000000000, 0xBFC7AB890210E000, 0x3D2BDB9072534A58,
    0x3FF3200000000000, 0x0000000000000000, 0xBFC6D60FE719D000, 0xBD10E46AA3B2E266,
    0x3FF3000000000000, 0x0000000000000000, 0xBFC5FF3070A79000, 0xBD1E9E439F105039,
    0x3FF3000000000000, 0x0000000000000000, 0xBFC5FF3070A79000, 0xBD1E9E439F105039,
    0x3FF2E00000000000, 0x0000000000000000, 0xBFC526E5E3A1B000, 0xBD20DE8B90075B8F,
    0x3FF2C00000000000, 0x0000000000000000, 0xBFC44D2B6CCB8000, 0x3D170CC16135783C,
    0x3FF2C00000000000, 0x0000000000000000, 0xBFC44D2B6CCB8000, 0x3D170CC16135783C,
    0x3FF2A00000000000, 0x0000000000000000, 0xBFC371FC201E9000, 0x3CF178864D27543A,
    0x3FF2800000000000, 0x0000000000000000, 0xBFC29552F81FF000, 0xBD248D301771C408,
    0x3FF2600000000000, 0x0000000000000000, 0xBFC1B72AD52F6000, 0xBD2E80A41811A396,
    0x3FF2600000000000, 0x0000000000000000, 0xBFC1B72AD52F6000, 0xBD2E80A41811A396,
    0x3FF2400000000000, 0x0000000000000000, 0xBFC0D77E7CD09000, 0x3D0A699688E85BF4,
    0x3FF2400000000000, 0x0000000000000000, 0xBFC0D77E7CD09000, 0x3D0A699688E85BF4,
    0x3FF2200000000000, 0x0000000000000000, 0xBFBFEC9131DBE000, 0xBD2575545CA333F2,
    0x3FF2000000000000, 0x0000000000000000, 0xBFBE27076E2B0000, 0x3D2A342C2AF0003C,
    0x3FF2000000000000, 0x0000000000000000, 0xBFBE27076E2B0000, 0x3D2A342C2AF0003C,
    0x3FF1E00000000000, 0x0000000000000000, 0xBFBC5E548F5BC000, 0xBD1D0C57585FBE06,
    0x3FF1C00000000000, 0x0000000000000000, 0xBFBA926D3A4AE000, 0x3D253935E85BAAC8,
    0x3FF1C00000000000, 0x0000000000000000, 0xBFBA926D3A4AE000, 0x3D253935E85BAAC8,
    0x3FF1A00000000000, 0x0000000000000000, 0xBFB8C345D631A000, 0x3D137C294D2F5668,
    0x3FF1A00000000000, 0x0000000000000000, 0xBFB8C345D631A000, 0x3D137C294D2F5668,
    0x3FF1800000000000, 0x0000000000000000, 0xBFB6F0D28AE56000, 0xBD269737C93373DA,
    0x3FF1600000000000, 0x0000000000000000, 0xBFB51B073F062000, 0x3D1F025B61C65E57,
    0x3FF1600000000000, 0x0000000000000000, 0xBFB51B073F062000, 0x3D1F025B61C65E57,
    0x3FF1400000000000, 0x0000000000000000, 0xBFB341D7961BE000, 0x3D2C5EDACCF913DF,
    0x3FF1400000000000, 0x0000000000000000, 0xBFB341D7961BE000, 0x3D2C5EDACCF913DF,
    0x3FF1200000000000, 0x0000000000000000, 0xBFB16536EEA38000, 0x3D147C5E768FA309,
    0x3FF1000000000000, 0x0000000000000000, 0xBFAF0A30C0118000, 0x3D2D599E83368E91,
    0x3FF1000000000000, 0x0000000000000000, 0xBFAF0A30C0118000, 0x3D2D599E83368E91,
    0x3FF0E00000000000, 0x0000000000000000, 0xBFAB42DD71198000, 0x3D1C827AE5D6704C,
    0x3FF0E00000000000, 0x0000000000000000, 0xBFAB42DD71198000, 0x3D1C827AE5D6704C,
    0x3FF0C00000000000, 0x0000000000000000, 0xBFA77458F632C000, 0xBD2CFC4634F2A1EE,
    0x3FF0C00000000000, 0x0000000000000000, 0xBFA77458F632C000, 0xBD2CFC4634F2A1EE,
    0x3FF0A00000000000, 0x0000000000000000, 0xBFA39E87B9FEC000, 0x3CF502B7F526FEAA,
    0x3FF0A00000000000, 0x0000000000000000, 0xBFA39E87B9FEC000, 0x3CF502B7F526FEAA,
    0x3FF0800000000000, 0x0000000000000000, 0xBF9F829B0E780000, 0xBD2980267C7E09E4,
    0x3FF0800000000000, 0x0000000000000000, 0xBF9F829B0E780000, 0xBD2980267C7E09E4,
    0x3FF0600000000000, 0x0000000000000000, 0xBF97B91B07D58000, 0xBD288D5493FAA639,
    0x3FF0400000000000, 0x0000000000000000, 0xBF8FC0A8B0FC0000, 0xBCDF1E7CF6D3A69C,
    0x3FF0400000000000, 0x0000000000000000, 0xBF8FC0A8B0FC0000, 0xBCDF1E7CF6D3A69C,
    0x3FF0200000000000, 0x0000000000000000, 0xBF7FE02A6B100000, 0xBD19E23F0DDA40E4,
    0x3FF0200000000000, 0x0000000000000000, 0xBF7FE02A6B100000, 0xBD19E23F0DDA40E4,
    0x3FF0000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
    0x3FF0000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
    0x3FEFC00000000000, 0x0000000000000000, 0x3F80101575890000, 0xBD10C76B999D2BE8,
    0x3FEF800000000000, 0x0000000000000000, 0x3F90205658938000, 0xBD23DC5B06E2F7D2,
    0x3FEF400000000000, 0x0000000000000000, 0x3F98492528C90000, 0xBD2AA0BA325A0C34,
    0x3FEF000000000000, 0x0000000000000000, 0x3FA0415D89E74000, 0x3D0111C05CF1D753,
    0x3FEEC00000000000, 0x0000000000000000, 0x3FA466AED42E0000, 0xBD2C167375BDFD28,
    0x3FEE800000000000, 0x0000000000000000, 0x3FA894AA149FC000, 0xBD197995D05A267D,
    0x3FEE400000000000, 0x0000000000000000, 0x3FACCB73CDDDC000, 0xBD1A68F247D82807,
    0x3FEE200000000000, 0x0000000000000000, 0x3FAEEA31C006C000, 0xBD0E113E4FC93B7B,
    0x3FEDE00000000000, 0x0000000000000000, 0x3FB1973BD1466000, 0xBD25325D560D9E9B,
    0x3FEDA00000000000, 0x0000000000000000, 0x3FB3BDF5A7D1E000, 0x3D2CC85EA5DB4ED7,
    0x3FED600000000000, 0x0000000000000000, 0x3FB5E95A4D97A000, 0xBD2C69063C5D1D1E,
    0x3FED400000000000, 0x0000000000000000, 0x3FB700D30AEAC000, 0x3CEC1E8DA99DED32,
    0x3FED000000000000, 0x0000000000000000, 0x3FB9335E5D594000, 0x3D23115C3ABD47DA,
    0x3FECC00000000000, 0x0000000000000000, 0x3FBB6AC88DAD6000, 0xBD1390802BF768E5,
    0x3FECA00000000000, 0x0000000000000000, 0x3FBC885801BC4000, 0x3D2646D1C65AACD3,
    0x3FEC600000000000, 0x0000000000000000, 0x3FBEC739830A2000, 0xBD2DC068AFE645E0,
    0x3FEC400000000000, 0x0000000000000000, 0x3FBFE89139DBE000, 0xBD2534D64FA10AFD,
    0x3FEC000000000000, 0x0000000000000000, 0x3FC1178E8227E000, 0x3D21EF78CE2D07F2,
    0x3FEBE00000000000, 0x0000000000000000, 0x3FC1AA2B7E23F000, 0x3D2CA78E44389934,
    0x3FEBA00000000000, 0x0000000000000000, 0x3FC2D1610C868000, 0x3D039D6CCB81B4A1,
    0x3FEB800000000000, 0x0000000000000000, 0x3FC365FCB0159000, 0x3CC62FA8234B7289,
    0x3FEB400000000000, 0x0000000000000000, 0x3FC4913D8333B000, 0x3D25837954FDB678,
    0x3FEB200000000000, 0x0000000000000000, 0x3FC527E5E4A1B000, 0x3D2633E8E5697DC7,
    0x3FEAE00000000000, 0x0000000000000000, 0x3FC6574EBE8C1000, 0x3D19CF8B2C3C2E78,
    0x3FEAC00000000000, 0x0000000000000000, 0x3FC6F0128B757000, 0xBD25118DE59C21E1,
    0x3FEAA00000000000, 0x0000000000000000, 0x3FC7898D85445000, 0xBD1C661070914305,
    0x3FEA600000000000, 0x0000000000000000, 0x3FC8BEAFEB390000, 0xBD073D54AAE92CD1,
    0x3FEA400000000000, 0x0000000000000000, 0x3FC95A5ADCF70000, 0x3D07F22858A0FF6F,
    0x3FEA000000000000, 0x0000000000000000, 0x3FCA93ED3C8AE000, 0xBD28724350562169,
    0x3FE9E00000000000, 0x0000000000000000, 0x3FCB31D8575BD000, 0xBD0C358D4EACE1AA,
    0x3FE9C00000000000, 0x0000000000000000, 0x3FCBD087383BE000, 0xBD2D4BC4595412B6,
    0x3FE9A00000000000, 0x0000000000000000, 0x3FCC6FFBC6F01000, 0xBCF1EC72C5962BD2,
    0x3FE9600000000000, 0x0000000000000000, 0x3FCDB13DB0D49000, 0xBD2AFF2AF715B035,
    0x3FE9400000000000, 0x0000000000000000, 0x3FCE530EFFE71000, 0x3CC212276041F430,
    0x3FE9200000000000, 0x0000000000000000, 0x3FCEF5ADE4DD0000, 0xBCCA211565BB8E11,
    0x3FE9000000000000, 0x0000000000000000, 0x3FCF991C6CB3B000, 0x3D1BCBECCA0CDF30,
    0x3FE8C00000000000, 0x0000000000000000, 0x3FD07138604D5800, 0x3CF89CDB16ED4E91,
    0x3FE8A00000000000, 0x0000000000000000, 0x3FD0C42D67616000, 0x3D27188B163CEAE9,
    0x3FE8800000000000, 0x0000000000000000, 0x3FD1178E8227E800, 0xBD2C210E63A5F01C,
    0x3FE8600000000000, 0x0000000000000000, 0x3FD16B5CCBACF800, 0x3D2B9ACDF7A51681,
    0x3FE8400000000000, 0x0000000000000000, 0x3FD1BF99635A6800, 0x3D2CA6ED5147BDB7,
    0x3FE8200000000000, 0x0000000000000000, 0x3FD214456D0EB800, 0x3D0A87DEBA46BAEA,
    0x3FE7E00000000000, 0x0000000000000000, 0x3FD2BEF07CDC9000, 0x3D2A9CFA4A5004F4,
    0x3FE7C00000000000, 0x0000000000000000, 0x3FD314F1E1D36000, 0xBD28E27AD3213CB8,
    0x3FE7A00000000000, 0x0000000000000000, 0x3FD36B6776BE1000, 0x3D116ECDB0F177C8,
    0x3FE7800000000000, 0x0000000000000000, 0x3FD3C25277333000, 0x3D183B54B606BD5C,
    0x3FE7600000000000, 0x0000000000000000, 0x3FD419B423D5E800, 0x3D08E436EC90E09D,
    0x3FE7400000000000, 0x0000000000000000, 0x3FD4718DC271C800, 0xBD2F27CE0967D675,
    0x3FE7200000000000, 0x0000000000000000, 0x3FD4C9E09E173000, 0xBD2E20891B0AD8A4,
    0x3FE7000000000000, 0x0000000000000000, 0x3FD522AE0738A000, 0x3D2EBE708164C759,
    0x3FE6E00000000000, 0x0000000000000000, 0x3FD57BF753C8D000, 0x3D1FADEDEE5D40EF,
    0x3FE6C00000000000, 0x0000000000000000, 0x3FD5D5BDDF596000, 0xBD0A0B2A08A465DC
  ]

/-- `pow_common.h`'s `checkint` for the bits `iy` of a nonzero finite `y`: 0 if `y` is not an
integer, 1 if it is an odd integer, and 2 if it is an even one. -/
def checkint (iy : UInt64) : UInt64 :=
  let e := (iy >>> 52) &&& 0x7ff
  if e < 0x3ff then 0
  else if e > 0x3ff + 52 then 2
  else if iy &&& (((1 : UInt64) <<< (0x3ff + 52 - e)) - 1) != 0 then 0
  else if iy &&& ((1 : UInt64) <<< (0x3ff + 52 - e)) != 0 then 1
  else 2

/-- `pow_common.h`'s `zeroinfnan`: whether the bits `i` are those of a zero, an infinity, or a
NaN. -/
def zeroinfnan (i : UInt64) : Bool :=
  2 * i - 1 ≥ 2 * 0x7FF0000000000000 - 1

/-- `math_config.h`'s `issignaling_inline` with `IEEE_754_2008_SNAN` 1: whether `x` is a
signaling NaN. -/
def issignaling (x : Float) : Bool :=
  2 * (x.toBits ^^^ 0x0008000000000000) > 2 * 0x7ff8000000000000

/-- Arm's `log_inline` for the bits `ix` of a positive `x`, normalized as `powWith` does for a
subnormal: `log x` as the rounded `y` and the tail `hi - y + lo`.  `tmp >>> 52`, extended by the
sign of `tmp`, is C's arithmetic shift of `(int64_t) tmp`.  `z` is split at bit 32 of its bits,
rounded, so that `zhi · invc - 1` and the square of `rhi` are exact. -/
def powLog (tab : Array UInt64) (ix : UInt64) : Float × Float :=
  let ln2hi := Float.ofBits 0x3FE62E42FEFA3800  --  0x1.62e42fefa3800p-1
  let ln2lo := Float.ofBits 0x3D2EF35793C76730  --  0x1.ef35793c76730p-45
  let A0 := Float.ofBits 0xBFE0000000000000     -- -0x1p-1
  let A1 := Float.ofBits 0xBFE5555555555560     --  0x1.555555555556p-2 * -2
  let A2 := Float.ofBits 0x3FE0000000000006     -- -0x1.0000000000006p-2 * -2
  let A3 := Float.ofBits 0x3FE999999959554E     --  0x1.999999959554ep-3 * 4
  let A4 := Float.ofBits 0xBFE555555529A47A     -- -0x1.555555529a47ap-3 * 4
  let A5 := Float.ofBits 0xBFF2495B9B4845E9     --  0x1.2495b9b4845e9p-3 * -8
  let A6 := Float.ofBits 0x3FF0002B8B263FC3     -- -0x1.0002b8b263fc3p-3 * -8
  let tmp := ix - 0x3fe6955500000000
  let i := (tmp >>> 45) % 128
  let k := (tmp >>> 52) ||| (if tmp >>> 63 == 1 then 0xFFFFFFFFFFFFF000 else 0)
  let iz := ix - (tmp &&& ((0xfff : UInt64) <<< 52))
  let z := Float.ofBits iz
  let kd := if k >>> 63 == 1 then -(0 - k).toFloat else k.toFloat
  let invc := Float.ofBits tab[(4 * i).toNat]!
  let logc := Float.ofBits tab[(4 * i + 2).toNat]!
  let logctail := Float.ofBits tab[(4 * i + 3).toNat]!
  let zhi := Float.ofBits ((iz + ((1 : UInt64) <<< 31)) &&& 0xFFFFFFFF00000000)
  let zlo := z - zhi
  let rhi := zhi * invc - 1.0
  let rlo := zlo * invc
  let r := rhi + rlo
  let t1 := kd * ln2hi + logc
  let t2 := t1 + r
  let lo1 := kd * ln2lo + logctail
  let lo2 := t1 - t2 + r
  let ar := A0 * r
  let ar2 := r * ar
  let ar3 := r * ar2
  let arhi := A0 * rhi
  let arhi2 := rhi * arhi
  let hi := t2 + arhi2
  let lo3 := rlo * (ar + arhi)
  let lo4 := t2 - hi + arhi2
  let p := ar3 * (A1 + r * A2 + ar2 * (A3 + r * A4 + ar2 * (A5 + r * A6)))
  let lo := lo1 + lo2 + lo3 + lo4 + p
  let y := hi + lo
  (y, hi - y + lo)

/-- `pow.c`'s `specialcase`: `scale · (1 + tmp)` for a result that may overflow or underflow, with
`sbits` the bits of `scale`, its sign included, whose exponent may have wrapped, and the sign bit
of the low 32 bits of `ki` the sign of `k`.  A positive `k` scales by `2 ^ 1009` after the sum; the
test that returns `DBL_MAX` is true only when rounding upward.  A negative `k` scales by
`2 ^ -1022`, and a result below 1 in magnitude before the scaling is first rounded to the
precision that the subnormal range keeps, with a zero taking the sign of `scale`. -/
def powSpecialCase (tmp : Float) (sbits ki : UInt64) : Float :=
  if ki &&& 0x80000000 == 0 then
    let scale := Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64)))
    let y := scale + scale * tmp
    if y == Float.ofBits 0x40E0000000000000 &&
        1.0 + Float.ofBits 0x3C30000000000000 != 1.0 then Float.ofBits 0x7FEFFFFFFFFFFFFF
    else y * Float.ofBits 0x7F00000000000000
  else
    let sbits := sbits + ((1022 : UInt64) <<< (52 : UInt64))
    let scale := Float.ofBits sbits
    let y := scale + scale * tmp
    let y := if y.abs < 1.0 then
        let one := if y < 0.0 then -1.0 else 1.0
        let lo := scale - y + scale * tmp
        let hi := one + y
        let lo := one - hi + y + lo
        let y := hi + lo - one
        if y == 0.0 then Float.ofBits (sbits &&& 0x8000000000000000) else y
      else y
    Float.ofBits 0x0010000000000000 * y

/-- The reduction and the polynomial of Arm's `exp_inline` for `x + xtail`, with `signBias`
`0x800 << 7` or 0 added to `k` so that the scale's sign bit is set for a negative result, through
`powSpecialCase` when `special` holds.  The constants are those of `Exp.expCore`. -/
def powExpCore (tab : Array UInt64) (x xtail : Float) (signBias : UInt64) (special : Bool) :
    Float :=
  let z := Float.ofBits 0x40671547652B82FE * x
  let kd := z + Float.ofBits 0x4338000000000000
  let ki := kd.toBits
  let kd := kd - Float.ofBits 0x4338000000000000
  let r := x + kd * Float.ofBits 0xBF762E42FEFA0000 + kd * Float.ofBits 0xBD0CF79ABC9E3B3A
  let r := r + xtail
  let idx := 2 * (ki % 128)
  let top := (ki + signBias) <<< (45 : UInt64)
  let tail := Float.ofBits tab[idx.toNat]!
  let sbits := tab[(idx + 1).toNat]! + top
  let r2 := r * r
  let tmp := tail + r +
    r2 * (Float.ofBits 0x3FDFFFFFFFFFFDBD + r * Float.ofBits 0x3FC555555555543C) +
    r2 * r2 * (Float.ofBits 0x3FA55555CF172B91 + r * Float.ofBits 0x3F81111167A4D017)
  if special then powSpecialCase tmp sbits ki
  else
    let scale := Float.ofBits sbits
    scale + scale * tmp

/-- Arm's `exp_inline`: `± exp (x + xtail)`, with the sign of `signBias`.  Below `2 ^ -54` in
magnitude the result is `±(1 + x)`, from 1024 on it is the signed underflow or overflow product of
`__math_uflow` or `__math_oflow`, and from 512 on it goes through `powSpecialCase`. -/
def powExp (tab : Array UInt64) (x xtail : Float) (signBias : UInt64) : Float :=
  let abstop := (x.toBits >>> 52) &&& 0x7ff
  if abstop - 0x3c9 ≥ 0x408 - 0x3c9 then
    if abstop - 0x3c9 ≥ 0x80000000 then
      let one := 1.0 + x
      if signBias != 0 then -one else one
    else if abstop ≥ 0x409 then
      if x.toBits >>> 63 == 1 then
        (if signBias != 0 then Float.ofBits 0x9000000000000000
          else Float.ofBits 0x1000000000000000) * Float.ofBits 0x1000000000000000
      else
        (if signBias != 0 then Float.ofBits 0xF000000000000000
          else Float.ofBits 0x7000000000000000) * Float.ofBits 0x7000000000000000
    else powExpCore tab x xtail signBias true
  else powExpCore tab x xtail signBias false

/-- The end of Arm's `pow` for the bits `ix` of a positive `x`, normalized for a subnormal, and `y`
with bits `iy`: `log x = hi + lo`, the product with `y` as `ehi + elo` from `y` and `hi` split at
bit 27, and its exponential. -/
def powMain (logTab expTab : Array UInt64) (ix : UInt64) (y : Float) (iy signBias : UInt64) :
    Float :=
  let (hi, lo) := powLog logTab ix
  let yhi := Float.ofBits (iy &&& 0xFFFFFFFFF8000000)
  let ylo := y - yhi
  let lhi := Float.ofBits (hi.toBits &&& 0xFFFFFFFFF8000000)
  let llo := hi - lhi + lo
  let ehi := yhi * lhi
  let elo := ylo * lhi + y * llo
  powExp expTab ehi elo signBias

/-- Arm's `pow` with the tables `logTab` and `expTab`.  `topx` and `topy` are the top 12 bits of
`x` and `y`.  The special cases run when `x` is below `2 ^ -1022` in magnitude, negative,
infinite, or NaN, or `|y|` is below `2 ^ -65`, from `2 ^ 63` on, or NaN.  `checkint` is evaluated
once in C for a negative `x` and here in each of the two tests that use it.  The comparisons of
two Booleans with `==` in C are nested tests here, since the dialect compares no Booleans. -/
def powWith (logTab expTab : Array UInt64) (x y : Float) : Float :=
  let ix := x.toBits
  let iy := y.toBits
  let topx := ix >>> 52
  let topy := iy >>> 52
  if topx - 0x001 ≥ 0x7ff - 0x001 || (topy &&& 0x7ff) - 0x3be ≥ 0x43e - 0x3be then
    if zeroinfnan iy then
      if 2 * iy == 0 then if issignaling x then x + y else 1.0
      else if ix == 0x3FF0000000000000 then if issignaling y then x + y else 1.0
      else if 2 * ix > 2 * 0x7FF0000000000000 || 2 * iy > 2 * 0x7FF0000000000000 then x + y
      else if 2 * ix == 2 * 0x3FF0000000000000 then 1.0
      else if 2 * ix < 2 * 0x3FF0000000000000 then if iy >>> 63 == 0 then 0.0 else y * y
      else if iy >>> 63 == 0 then y * y else 0.0
    else if zeroinfnan ix then
      let x2 := x * x
      let x2 := if ix >>> 63 == 1 && checkint iy == 1 then -x2 else x2
      if iy >>> 63 == 1 then 1.0 / x2 else x2
    else if ix >>> 63 == 1 && checkint iy == 0 then (x - x) / (x - x)
    else
      let signBias : UInt64 :=
        if ix >>> 63 == 1 && checkint iy == 1 then (0x800 : UInt64) <<< 7 else 0
      let neg := ix >>> 63 == 1
      let ix := if neg then ix &&& (0x7fffffffffffffff : UInt64) else ix
      let topx := if neg then topx &&& 0x7ff else topx
      if (topy &&& 0x7ff) - 0x3be ≥ 0x43e - 0x3be then
        if ix == 0x3FF0000000000000 then 1.0
        else if (topy &&& 0x7ff) < 0x3be then
          if ix > 0x3FF0000000000000 then 1.0 + y else 1.0 - y
        else if ix > 0x3FF0000000000000 then
          if topy < 0x800 then Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
          else Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
        else if topy < 0x800 then
          Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
        else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
      else
        let ix := if topx == 0 then
            ((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
              ((52 : UInt64) <<< 52)
          else ix
        powMain logTab expTab ix y iy signBias
  else powMain logTab expTab ix y iy 0

/-- `x ^ y`, from the tables `powLogTable` and `Exp.expTable`. -/
def pow (x y : Float) : Float := powWith powLogTable Exp.expTable x y

verified_compile compiled := [checkint, zeroinfnan, issignaling, powLog, powSpecialCase,
  powExpCore, powExp, powMain, powWith, pow]

end Verified.Examples.Pow
