import Verified.Examples.Trig
import Verified.Examples.Log

/-! The forty-eighth program of the verified compiler: the Bessel functions `j0`, `j1`, `y0`, `y1`,
`jn`, and `yn`, ported from fdlibm as FreeBSD's `lib/msun/src` has it at commit
`20381bce4b63975494a2f4bc84257f6932e6d379` (`e_j0.c`, `e_j1.c`, and `e_jn.c`, Copyright (C) 1993 by
Sun Microsystems, Inc., freely distributable with this notice).  Below 2, `j0` and `j1` are rational
approximations in `x²`, and `y0` and `y1` add `(2/π) j0 x ln x` and `(2/π) (j1 x ln x - 1/x)` to
rational approximations.  From 2 up, all four are `(P cos θ ∓ Q sin θ)/√(π x)` with `θ = x - π/4` or
`x - 3π/4`, where rational approximations in `1/x²` on four ranges give `P` and `Q`, and `cos θ` and
`sin θ` come from `sin x` and `cos x`, the one that cancels from `-cos (2 x)` divided by the other.
`jn` uses the forward recurrence from `J 0` and `J 1` for `x ≥ n`, the leading term of the series
below `2 ^ -30`, where fdlibm's comment says `2 ^ -29`, and otherwise a continued fraction and the
backward recurrence, normalized by `J 0` or `J 1`, and `yn` the forward recurrence from `Y 0` and
`Y 1`.  Above `2 ^ 302` both use the leading term of the asymptotic expansion.

The port calls the earlier ports where fdlibm calls the C library: `Trig.sinWith` and `Trig.cosWith`
with the tables `Trig.invPi` and `Trig.halfPi` for `sincos` and `cos`, `Log.logWith` with
`Log.logTable` and `Log.logTable2` for `log`, and `Float.sqrt` for `sqrt`.  FreeBSD's `sincos`
evaluates the formulas of its `sin` and `cos`, of which `Trig` is a port, so the first two
substitutions keep fdlibm's values, and the square root is correctly rounded in both.  `Log.logWith`
is Arm's `log`, whose results may differ from fdlibm's in the last bit.  The order of `jn` and `yn`
is C's `int` in the low 32 bits of the word, two's complement, with `J (-n) = (-1) ^ n J n` and
`Y (-n) = (-1) ^ n Y n`, so that `|n| = 2 ^ 31` for `n = -2 ^ 31`, where C's `-n` overflows.  The
special values are those of POSIX.1-2017: `j0 (±∞) = j1 (±∞) = 0`, `y0`, `y1`, and `yn` of `±0` are
`-∞` and of a negative `x` NaN, and NaN gives NaN.  The `while` loop of `jn` is a
`LeanExe.repeatWhile` with `2 ^ 32 - 1` steps of fuel, more than it can take, and the constants are
the bit patterns that fdlibm's comments give, which match its decimal literals.  The
`verified_compile` call at the end of the module checks the encoding one function at a time and
needs about 1.0 GB.  The journal records the measurements.  `BesselAccuracy.lean` checks the results
against references computed with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`e_j0.c`, `e_j1.c`, and `e_jn.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunSoft, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Verified.Examples.Bessel

/-- The coefficients of `pzero` and `qzero` in `e_j0.c`: for each of the ranges from 8 up, from
4.5454, from 2.8571, and from 2, `pR` (6) and `pS` (5) at `11 r`, and `qR` (6) and `qS` (6) at
`44 + 12 r`. -/
def j0Table : Array UInt64 :=
  #[
    0x0000000000000000,  -- 0, pR8: 0.00000000000000000000e+00
    0xBFB1FFFFFFFFFD32,  -- 1, pR8: -7.03124999999900357484e-02
    0xC02029D0B44FA779,  -- 2, pR8: -8.08167041275349795626e+00
    0xC07011027B19E863,  -- 3, pR8: -2.57063105679704847262e+02
    0xC0A36A6ECD4DCAFC,  -- 4, pR8: -2.48521641009428822144e+03
    0xC0B4850B36CC643D,  -- 5, pR8: -5.25304380490729545272e+03
    0x405D223307A96751,  -- 6, pS8: 1.16534364619668181717e+02
    0x40ADF37D50596938,  -- 7, pS8: 3.83374475364121826715e+03
    0x40E3D2BB6EB6B05F,  -- 8, pS8: 4.05978572648472545552e+04
    0x40FC810F8F9FA9BD,  -- 9, pS8: 1.16752972564375915681e+05
    0x40E741774F2C49DC,  -- 10, pS8: 4.76277284146730962675e+04
    0xBDA918B147E495CC,  -- 11, pR5: -1.14125464691894502584e-11
    0xBFB1FFFFE69AFBC6,  -- 12, pR5: -7.03124940873599280078e-02
    0xC010A370F90C6BBF,  -- 13, pR5: -4.15961064470587782438e+00
    0xC050EB2F5A7D1783,  -- 14, pR5: -6.76747652265167261021e+01
    0xC074B3B36742CC63,  -- 15, pR5: -3.31231299649172967747e+02
    0xC075A6EF28A38BD7,  -- 16, pR5: -3.46433388365604912451e+02
    0x404E60810C98C5DE,  -- 17, pS5: 6.07539382692300335975e+01
    0x40906D025C7E2864,  -- 18, pS5: 1.05125230595704579173e+03
    0x40B75AF88FBE1D60,  -- 19, pS5: 5.97897094333855784498e+03
    0x40C2CCB8FA76FA38,  -- 20, pS5: 9.62544514357774460223e+03
    0x40A2CC1DC70BE864,  -- 21, pS5: 2.40605815922939109441e+03
    0xBE25E1036FE1AA86,  -- 22, pR3: -2.54704601771951915620e-09
    0xBFB1FFF6F7C0E24B,  -- 23, pR3: -7.03119616381481654654e-02
    0xC00345B2AEA48074,  -- 24, pR3: -2.40903221549529611423e+00
    0xC035F74A4CB94E14,  -- 25, pR3: -2.19659774734883086467e+01
    0xC04D0A22420A1A45,  -- 26, pR3: -5.80791704701737572236e+01
    0xC03F72ACA892D80F,  -- 27, pR3: -3.14479470594888503854e+01
    0x4041ED9284077DD3,  -- 28, pS3: 3.58560338055209726349e+01
    0x40769839464A7C0E,  -- 29, pS3: 3.61513983050303863820e+02
    0x4092A66E6D1061D6,  -- 30, pS3: 1.19360783792111533330e+03
    0x40919FFCB8C39B7E,  -- 31, pS3: 1.12799679856907414432e+03
    0x4065B296FC379081,  -- 32, pS3: 1.73580930813335754692e+02
    0xBE77D316E927026D,  -- 33, pR2: -8.87534333032526411254e-08
    0xBFB1FF62495E1E42,  -- 34, pR2: -7.03030995483624743247e-02
    0xBFF736398A24A843,  -- 35, pR2: -1.45073846780952986357e+00
    0xC01E8AF3EDAFA7F3,  -- 36, pR2: -7.63569613823527770791e+00
    0xC02662E6C5246303,  -- 37, pR2: -1.11931668860356747786e+01
    0xC009DE81AF8FE70F,  -- 38, pR2: -3.23364579351335335033e+00
    0x40363865908B5959,  -- 39, pS2: 2.22202997532088808441e+01
    0x4061069E0EE8878F,  -- 40, pS2: 1.36206794218215208048e+02
    0x4070E78642EA079B,  -- 41, pS2: 2.70470278658083486789e+02
    0x40633C033AB6FAFF,  -- 42, pS2: 1.53875394208320329881e+02
    0x402D50B344391809,  -- 43, pS2: 1.46576176948256193810e+01
    0x0000000000000000,  -- 44, qR8: 0.00000000000000000000e+00
    0x3FB2BFFFFFFFFE2C,  -- 45, qR8: 7.32421874999935051953e-02
    0x402789525BB334D6,  -- 46, qR8: 1.17682064682252693899e+01
    0x40816D6315301825,  -- 47, qR8: 5.57673380256401856059e+02
    0x40C14D993E18F46D,  -- 48, qR8: 8.85919720756468632317e+03
    0x40E212D40E901566,  -- 49, qR8: 3.70146267776887834771e+04
    0x406478D5365B39BC,  -- 50, qS8: 1.63776026895689824414e+02
    0x40BFA2584E6B0563,  -- 51, qS8: 8.09834494656449805916e+03
    0x4101665254D38C3F,  -- 52, qS8: 1.42538291419120476348e+05
    0x412883DA83A52B43,  -- 53, qS8: 8.03309257119514397345e+05
    0x4129A66B28DE0B3D,  -- 54, qS8: 8.40501579819060512818e+05
    0xC114FD6D2C9530C5,  -- 55, qS8: -3.43899293537866615225e+05
    0x3DB43D8F29CC8CD9,  -- 56, qR5: 1.84085963594515531381e-11
    0x3FB2BFFFD172B04C,  -- 57, qR5: 7.32421766612684765896e-02
    0x401757B0B9953DD3,  -- 58, qR5: 5.83563508962056953777e+00
    0x4060E3920A8788E9,  -- 59, qR5: 1.35111577286449829671e+02
    0x40900CF99DC8C481,  -- 60, qR5: 1.02724376596164097464e+03
    0x409F17E953C6E3A6,  -- 61, qR5: 1.98997785864605384631e+03
    0x4054B1B3FB5E1543,  -- 62, qS5: 8.27766102236537761883e+01
    0x40A03BA0DA21C0CE,  -- 63, qS5: 2.07781416421392987104e+03
    0x40D267D27B591E6D,  -- 64, qS5: 1.88472887785718085070e+04
    0x40EBB5E397E02372,  -- 65, qS5: 5.67511122894947329769e+04
    0x40E191181F7A54A0,  -- 66, qS5: 3.59767538425114471465e+04
    0xC0B4EA57BEDBC609,  -- 67, qS5: -5.35434275601944773371e+03
    0x3E32CD036ADECB82,  -- 68, qR3: 4.37741014089738620906e-09
    0x3FB2BFEE0E8D0842,  -- 69, qR3: 7.32411180042911447163e-02
    0x400AC0FC61149CF5,  -- 70, qR3: 3.34423137516170720929e+00
    0x40454F98962DAEDD,  -- 71, qR3: 4.26218440745412650017e+01
    0x406559DBE25EFD1F,  -- 72, qR3: 1.70808091340565596283e+02
    0x4064D77C81FA21E0,  -- 73, qR3: 1.66733948696651168575e+02
    0x40486122BFE343A6,  -- 74, qS3: 4.87588729724587182091e+01
    0x40862D8386544EB3,  -- 75, qS3: 7.09689221056606015736e+02
    0x40ACF04BE44DFC63,  -- 76, qS3: 3.70414822620111362994e+03
    0x40B93C6CD7C76A28,  -- 77, qS3: 6.46042516752568917582e+03
    0x40A3A8AAD94FB1C0,  -- 78, qS3: 2.51633368920368957333e+03
    0xC062A7EB201CF40F,  -- 79, qS3: -1.49247451836156386662e+02
    0x3E84313B54F76BDB,  -- 80, qR2: 1.50444444886983272379e-07
    0x3FB2BEC53E883E34,  -- 81, qR2: 7.32234265963079278272e-02
    0x3FFFF897E727779C,  -- 82, qR2: 1.99819174093815998816e+00
    0x402CFDBFAAF96FE5,  -- 83, qR2: 1.44956029347885735348e+01
    0x403FAA8E29FBDC4A,  -- 84, qR2: 3.16662317504781540833e+01
    0x403040B171814BB4,  -- 85, qR2: 1.62527075710929267416e+01
    0x403E5D96F7C07AED,  -- 86, qS2: 3.03655848355219184498e+01
    0x4070D591E4D14B40,  -- 87, qS2: 2.69348118608049844624e+02
    0x408A664522B3BF22,  -- 88, qS2: 8.44783757595320139444e+02
    0x408B977C9C5CC214,  -- 89, qS2: 8.82935845112488550512e+02
    0x406A95530E001365,  -- 90, qS2: 2.12666388511798828631e+02
    0xC0153E6AF8B32931  -- 91, qS2: -5.31095493882666946917e+00
  ]

/-- The coefficients of `pone` and `qone` in `e_j1.c`, in the layout of `j0Table`, and `U0` and `V0`
of `y1` at 92 and 97. -/
def j1Table : Array UInt64 :=
  #[
    0x0000000000000000,  -- 0, pr8: 0.00000000000000000000e+00
    0x3FBDFFFFFFFFFCCE,  -- 1, pr8: 1.17187499999988647970e-01
    0x402A7A9D357F7FCE,  -- 2, pr8: 1.32394806593073575129e+01
    0x4079C0D4652EA590,  -- 3, pr8: 4.12051854307378562225e+02
    0x40AE457DA3A532CC,  -- 4, pr8: 3.87474538913960532227e+03
    0x40BEEA7AC32782DD,  -- 5, pr8: 7.91447954031891731574e+03
    0x405C8D458E656CAC,  -- 6, ps8: 1.14207370375678408436e+02
    0x40AC85DC964D274F,  -- 7, ps8: 3.65093083420853463394e+03
    0x40E20B8697C5BB7F,  -- 8, ps8: 3.69562060269033463555e+04
    0x40F7D42CB28F17BB,  -- 9, ps8: 9.76027935934950801311e+04
    0x40DE1511697A0B2D,  -- 10, ps8: 3.08042720627888811578e+04
    0x3DAD0667DAE1CA7D,  -- 11, pr5: 1.31990519556243522749e-11
    0x3FBDFFFFE2C10043,  -- 12, pr5: 1.17187493190614097638e-01
    0x401B36046E6315E3,  -- 13, pr5: 6.80275127868432871736e+00
    0x405B13B9452602ED,  -- 14, pr5: 1.08308182990189109773e+02
    0x40802D16D052D649,  -- 15, pr5: 5.17636139533199752805e+02
    0x408085B8BB7E0CB7,  -- 16, pr5: 5.28715201363337541807e+02
    0x404DA3EAA8AF633D,  -- 17, ps5: 5.92805987221131331921e+01
    0x408EFB361B066701,  -- 18, ps5: 9.91401418733614377743e+02
    0x40B4E9445706B6FB,  -- 19, ps5: 5.35326695291487976647e+03
    0x40BEA4B0B8A5BB15,  -- 20, ps5: 7.84469031749551231769e+03
    0x40978030036F5E51,  -- 21, ps5: 1.50404688810361062679e+03
    0x3E29FC21A7AD9EDD,  -- 22, pr3: 3.02503916137373618024e-09
    0x3FBDFFF55B21D17B,  -- 23, pr3: 1.17186865567253592491e-01
    0x400F76BCE85EAD8A,  -- 24, pr3: 3.93297750033315640650e+00
    0x40418F489DA6D129,  -- 25, pr3: 3.51194035591636932736e+01
    0x4056C3854D2C1837,  -- 26, pr3: 9.10550110750781271918e+01
    0x4048478F8EA83EE5,  -- 27, pr3: 4.85590685197364919645e+01
    0x40416549A134069C,  -- 28, ps3: 3.47913095001251519989e+01
    0x40750C3307F1A75F,  -- 29, ps3: 3.36762458747825746741e+02
    0x40905B7C5037D523,  -- 30, ps3: 1.04687139975775130551e+03
    0x408BD67DA32E31E9,  -- 31, ps3: 8.90811346398256432622e+02
    0x4059F26D7C2EED53,  -- 32, ps3: 1.03787932439639277504e+02
    0x3E7CE9D4F65544F4,  -- 33, pr2: 1.07710830106873743082e-07
    0x3FBDFF42BE760D83,  -- 34, pr2: 1.17176219462683348094e-01
    0x4002F2B7F98FAEC0,  -- 35, pr2: 2.36851496667608785174e+00
    0x40287C377F71A964,  -- 36, pr2: 1.22426109148261232917e+01
    0x4031B1A8177F8EE2,  -- 37, pr2: 1.76939711271687727390e+01
    0x40144B49A574C1FE,  -- 38, pr2: 5.07352312588818499250e+00
    0x40356FBD8AD5ECDC,  -- 39, ps2: 2.14364859363821409488e+01
    0x405F529314F92CD5,  -- 40, ps2: 1.25290227168402751090e+02
    0x406D08D8D5A2DBD9,  -- 41, ps2: 2.32276469057162813669e+02
    0x405D6B7ADA1884A9,  -- 42, ps2: 1.17679373287147100768e+02
    0x4020BAB1F44E5192,  -- 43, ps2: 8.36463893371618283368e+00
    0x0000000000000000,  -- 44, qr8: 0.00000000000000000000e+00
    0xBFBA3FFFFFFFFDF3,  -- 45, qr8: -1.02539062499992714161e-01
    0xC0304591A26779F7,  -- 46, qr8: -1.62717534544589987888e+01
    0xC087BCD053E4B576,  -- 47, qr8: -7.59601722513950107896e+02
    0xC0C724E740F87415,  -- 48, qr8: -1.18498066702429587167e+04
    0xC0E7A6D065D09C6A,  -- 49, qr8: -4.84385124285750353010e+04
    0x40642CA6DE5BCDE5,  -- 50, qs8: 1.61395369700722909556e+02
    0x40BE9162D0D88419,  -- 51, qs8: 7.82538599923348465381e+03
    0x4100579AB0B75E98,  -- 52, qs8: 1.33875336287249578163e+05
    0x4125F65372869C19,  -- 53, qs8: 7.19657723683240939863e+05
    0x412457D27719AD5C,  -- 54, qs8: 6.66601232617776375264e+05
    0xC111F9690EA5AA18,  -- 55, qs8: -2.94490264303834643215e+05
    0xBDB6FA431AA1A098,  -- 56, qr5: -2.08979931141764104297e-11
    0xBFBA3FFFCB597FEF,  -- 57, qr5: -1.02539050241375426231e-01
    0xC0201CE6CA03AD4B,  -- 58, qr5: -8.05644828123936029840e+00
    0xC066F56D6CA7B9B0,  -- 59, qr5: -1.83669607474888380239e+02
    0xC09574C66931734F,  -- 60, qr5: -1.37319376065508163265e+03
    0xC0A468E388FDA79D,  -- 61, qr5: -2.61244440453215656817e+03
    0x405451B2FF5A11B2,  -- 62, qs5: 8.12765501384335777857e+01
    0x409F1F31E77BF839,  -- 63, qs5: 1.99179873460485964642e+03
    0x40D10F1F0D64CE29,  -- 64, qs5: 1.74684851924908907677e+04
    0x40E8576DAABAD197,  -- 65, qs5: 4.98514270910352279316e+04
    0x40DB4B04CF7C364B,  -- 66, qs5: 2.79480751638918118260e+04
    0xC0B26F2EFCFFA004,  -- 67, qs5: -4.71918354795128470869e+03
    0xBE35CFA9D38FC84F,  -- 68, qr3: -5.07831226461766561369e-09
    0xBFBA3FEB51AEED54,  -- 69, qr3: -1.02537829820837089745e-01
    0xC01270C23302D9FF,  -- 70, qr3: -4.61011581139473403113e+00
    0xC04CEC71C25D16DA,  -- 71, qr3: -5.78472216562783643212e+01
    0xC06C87D34718D55F,  -- 72, qr3: -2.28244540737631695038e+02
    0xC06B66B95F5C1BF6,  -- 73, qr3: -2.19210128478909325622e+02
    0x4047D523CCD367E4,  -- 74, qs3: 4.76651550323729509273e+01
    0x40850EEBC031EE3E,  -- 75, qs3: 6.73865112676699709482e+02
    0x40AA684E448E7C9A,  -- 76, qs3: 3.38015286679526343505e+03
    0x40B5ABBAA61D54A6,  -- 77, qs3: 5.54772909720722782367e+03
    0x409DBC7A0DD4DF4B,  -- 78, qs3: 1.90311919338810798763e+03
    0xC060E670290A311F,  -- 79, qs3: -1.35201191444307340817e+02
    0xBE87F12644C626D2,  -- 80, qr2: -1.78381727510958865572e-07
    0xBFBA3E8E9148B010,  -- 81, qr2: -1.02517042607985553460e-01
    0xC006048469BB4EDA,  -- 82, qr2: -2.75220568278187460720e+00
    0xC033A9E2C168907F,  -- 83, qr2: -1.96636162643703720221e+01
    0xC04529A3DE104AAA,  -- 84, qr2: -4.23253133372830490089e+01
    0xC0355F3639CF6E52,  -- 85, qr2: -2.13719211703704061733e+01
    0x403D888A78AE64FF,  -- 86, qs2: 2.95333629060523854548e+01
    0x406F9F68DB821CBA,  -- 87, qs2: 2.52981549982190529136e+02
    0x4087AC05CE49A0F7,  -- 88, qs2: 7.57502834868645436472e+02
    0x40871B2548D4C029,  -- 89, qs2: 7.39393205320467245656e+02
    0x40637E5E3C3ED8D4,  -- 90, qs2: 1.55949003336666123687e+02
    0xC013D686E71BE86B,  -- 91, qs2: -4.95949898822628210127e+00
    0xBFC91866143CBC8A,  -- 92, U0: -1.96057090646238940668e-01
    0x3FA9D3C776292CD1,  -- 93, U0: 5.04438716639811282616e-02
    0xBF5F55E54844F50F,  -- 94, U0: -1.91256895875763547298e-03
    0x3EF8AB038FA6B88E,  -- 95, U0: 2.35252600561610495928e-05
    0xBE78AC00569105B8,  -- 96, U0: -9.19099158039878874504e-08
    0x3F94650D3F4DA9F0,  -- 97, V0: 1.99167318236649903973e-02
    0x3F2A8C896C257764,  -- 98, V0: 2.02552581025135171496e-04
    0x3EB6C05A894E8CA6,  -- 99, V0: 1.35608801097516229404e-06
    0x3E3ABF1D5BA69A86,  -- 100, V0: 6.22741452364621501295e-09
    0x3DB25039DACA772A  -- 101, V0: 1.66559246207992079114e-11
  ]

/-- The double whose bits are entry `i` of `tab`. -/
def entry (tab : Array UInt64) (i : UInt64) : Float := Float.ofBits tab[i.toNat]!

/-- The range of `pzero`, `qzero`, `pone`, and `qone` for the high word `ix` of `x ≥ 2`: 0 from 8
up, 1 from 4.5454, 2 from 2.8571, and 3 below. -/
def rangeOf (ix : UInt64) : UInt64 :=
  if ix ≥ 0x40200000 then 0 else if ix ≥ 0x40122E8B then 1 else if ix ≥ 0x4006DB6D then 2 else 3

/-- `pzero` and `pone`: `1 + R/S` in `z = 1/x²`, with the coefficients of `R` and `S` at `11 r` in
`tab`. -/
def pAsym (tab : Array UInt64) (x : Float) : Float :=
  let o := (11 : UInt64) * rangeOf ((x.toBits >>> 32) &&& 0x7fffffff)
  let z := 1.0 / (x * x)
  let r := entry tab o + z * (entry tab (o + 1) + z * (entry tab (o + 2) + z * (entry tab (o + 3) +
    z * (entry tab (o + 4) + z * entry tab (o + 5)))))
  let s := 1.0 + z * (entry tab (o + 6) + z * (entry tab (o + 7) + z * (entry tab (o + 8) +
    z * (entry tab (o + 9) + z * entry tab (o + 10)))))
  1.0 + r / s

/-- `R/S` of `qzero` and `qone`, with the coefficients at `44 + 12 r` in `tab`. -/
def qRatio (tab : Array UInt64) (x : Float) : Float :=
  let o := (44 : UInt64) + (12 : UInt64) * rangeOf ((x.toBits >>> 32) &&& 0x7fffffff)
  let z := 1.0 / (x * x)
  let r := entry tab o + z * (entry tab (o + 1) + z * (entry tab (o + 2) + z * (entry tab (o + 3) +
    z * (entry tab (o + 4) + z * entry tab (o + 5)))))
  let s := 1.0 + z * (entry tab (o + 6) + z * (entry tab (o + 7) + z * (entry tab (o + 8) +
    z * (entry tab (o + 9) + z * (entry tab (o + 10) + z * entry tab (o + 11))))))
  r / s

def invsqrtpi : Float := Float.ofBits 0x3FE20DD750429B6D  -- 5.64189583547756279280e-01
def tpi : Float := Float.ofBits 0x3FE45F306DC9C883  -- 6.36619772367581382433e-01

/-- The common part of `j0` and `y0` from 2 up: `(cc, ss)`, `√2` times `cos (x - π/4)` and
`sin (x - π/4)`, with the one of the two that cancels taken from `-cos (2 x)` divided by the other.
-/
def asym0 (inv half : Array UInt64) (ix : UInt64) (x : Float) : Float × Float :=
  let s := Trig.sinWith inv half x
  let c := Trig.cosWith inv half x
  let ss := s - c
  let cc := s + c
  if ix < 0x7fe00000 then
    let z := -(Trig.cosWith inv half (x + x))
    if s * c < 0.0 then (z / ss, ss) else (cc, z / cc)
  else (cc, ss)

/-- fdlibm's `j0` with the tables of `Trig.sinWith` and `j0Table`. -/
def j0With (inv half tab : Array UInt64) (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then 1.0 / (x * x)
  else
    let x := x.abs
    if ix ≥ 0x40000000 then
      let (cc, ss) := asym0 inv half ix x
      if ix > 0x48000000 then (invsqrtpi * cc) / Float.sqrt x
      else invsqrtpi * (pAsym tab x * cc - (qRatio tab x - 0.125) / x * ss) / Float.sqrt x
    else if ix < 0x3f200000 && Float.ofBits 0x7E37E43C8800759C + x > 1.0 then  -- 1e300
      if ix < 0x3e400000 then 1.0 else 1.0 - x * x / 4.0
    else
      let z := x * x
      let r := z * (Float.ofBits 0x3F8FFFFFFFFFFFFD + z * (Float.ofBits 0xBF28E6A5B61AC6E9 +
        z * (Float.ofBits 0x3EBEB1D10C503919 + z * Float.ofBits 0xBE33D5E773D63FCE)))  -- R02 to R05
      let s := 1.0 + z * (Float.ofBits 0x3F8FFCE882C8C2A4 + z * (Float.ofBits 0x3F1EA6D2DD57DBF4 +
        z * (Float.ofBits 0x3EA13B54CE84D5A9 + z * Float.ofBits 0x3E1408BCF4745D8F)))  -- S01 to S04
      if ix < 0x3FF00000 then 1.0 + z * ((r / s) - 0.25)
      else
        let u := x / 2.0
        (1.0 + u) * (1.0 - u) + z * (r / s)

/-- fdlibm's `y0` with the tables of `Trig.sinWith`, `Log.logWith`, and `j0Table`. -/
def y0With (inv half logTab logTab2 tab : Array UInt64) (x : Float) : Float :=
  let u := x.toBits
  let ix := (u >>> 32) &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then 1.0 / (x + x * x)
  else if u <<< 1 == 0 then -1.0 / 0.0
  else if u >>> 63 == 1 then 0.0 / 0.0
  else if ix ≥ 0x40000000 then
    let (cc, ss) := asym0 inv half ix x
    if ix > 0x48000000 then (invsqrtpi * ss) / Float.sqrt x
    else invsqrtpi * (pAsym tab x * ss + (qRatio tab x - 0.125) / x * cc) / Float.sqrt x
  else if ix ≤ 0x3e400000 then
    Float.ofBits 0xBFB2E4D699CBD01F + tpi * Log.logWith logTab logTab2 x  -- u00
  else
    let z := x * x
    let u := Float.ofBits 0xBFB2E4D699CBD01F + z * (Float.ofBits 0x3FC69D019DE9E3FC +
      z * (Float.ofBits 0xBF8C4CE8B16CFA97 + z * (Float.ofBits 0x3F36C54D20B29B6B +
      z * (Float.ofBits 0xBECFFEA773D25CAD + z * (Float.ofBits 0x3E5500573B4EABD4 +
      z * Float.ofBits 0xBDC5E43D693FB3C8)))))  -- u00 to u06
    let v := 1.0 + z * (Float.ofBits 0x3F8A127091C9C71A + z * (Float.ofBits 0x3F13ECBBF578C6C1 +
      z * (Float.ofBits 0x3E91642D7FF202FD + z * Float.ofBits 0x3DFE50183BD6D9EF)))  -- v01 to v04
    u / v + tpi * (j0With inv half tab x * Log.logWith logTab logTab2 x)

/-- The common part of `j1` and `y1` from 2 up, as `asym0` with `x - 3π/4`. -/
def asym1 (inv half : Array UInt64) (ix : UInt64) (x : Float) : Float × Float :=
  let s := Trig.sinWith inv half x
  let c := Trig.cosWith inv half x
  let ss := -s - c
  let cc := s - c
  if ix < 0x7fe00000 then
    let z := Trig.cosWith inv half (x + x)
    if s * c > 0.0 then (z / ss, ss) else (cc, z / cc)
  else (cc, ss)

/-- fdlibm's `j1` with the tables of `Trig.sinWith` and `j1Table`. -/
def j1With (inv half tab : Array UInt64) (x : Float) : Float :=
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then 1.0 / x
  else
    let y := x.abs
    if ix ≥ 0x40000000 then
      let (cc, ss) := asym1 inv half ix y
      let z :=
        if ix > 0x48000000 then (invsqrtpi * cc) / Float.sqrt y
        else invsqrtpi * (pAsym tab y * cc - (0.375 + qRatio tab y) / y * ss) / Float.sqrt y
      if hx >>> 31 == 1 then -z else z
    else if ix < 0x3e400000 && Float.ofBits 0x7E37E43C8800759C + x > 1.0 then 0.5 * x  -- 1e300
    else
      let z := x * x
      let r := z * (Float.ofBits 0xBFB0000000000000 + z * (Float.ofBits 0x3F570D9F98472C61 +
        z * (Float.ofBits 0xBEF0C5C6BA169668 + z * Float.ofBits 0x3E6AAAFA46CA0BD9)))  -- r00 to r03
      let s := 1.0 + z * (Float.ofBits 0x3F939D0B12637E53 + z * (Float.ofBits 0x3F285F56B9CDF664 +
        z * (Float.ofBits 0x3EB3BFF8333F8498 + z * (Float.ofBits 0x3E35AC88C97DFF2C +
        z * Float.ofBits 0x3DAB2ACFCFB97ED8))))  -- s01 to s05
      x * 0.5 + (r * x) / s

/-- fdlibm's `y1` with the tables of `Trig.sinWith`, `Log.logWith`, and `j1Table`. -/
def y1With (inv half logTab logTab2 tab : Array UInt64) (x : Float) : Float :=
  let u := x.toBits
  let ix := (u >>> 32) &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then 1.0 / (x + x * x)
  else if u <<< 1 == 0 then -1.0 / 0.0
  else if u >>> 63 == 1 then 0.0 / 0.0
  else if ix ≥ 0x40000000 then
    let (cc, ss) := asym1 inv half ix x
    if ix > 0x48000000 then (invsqrtpi * ss) / Float.sqrt x
    else invsqrtpi * (pAsym tab x * ss + (0.375 + qRatio tab x) / x * cc) / Float.sqrt x
  else if ix ≤ 0x3c900000 then -tpi / x
  else
    let z := x * x
    let u := entry tab 92 + z * (entry tab 93 + z * (entry tab 94 + z * (entry tab 95 +
      z * entry tab 96)))
    let v := 1.0 + z * (entry tab 97 + z * (entry tab 98 + z * (entry tab 99 + z * (entry tab 100 +
      z * entry tab 101))))
    x * (u / v) + tpi * (j1With inv half tab x * Log.logWith logTab logTab2 x - 1.0 / x)

/-- The order `n` as C's `int` in the low 32 bits of the word, as `(|n|, n < 0)`.  For
`n = -2 ^ 31`, where C's `-n` overflows, `|n|` is `2 ^ 31`. -/
def order (n : UInt64) : UInt64 × Bool :=
  let n32 := n &&& 0xFFFFFFFF
  if n32 ≥ 0x80000000 then (0x100000000 - n32, true) else (n32, false)

/-- `√2 · cos (x - (2 n + 1) π/4)` from `s = sin x` and `c = cos x`, by `n mod 4`. -/
def phaseCos (k : UInt64) (s c : Float) : Float :=
  if k == 0 then c + s else if k == 1 then -c + s else if k == 2 then -c - s else c - s

/-- `√2 · sin (x - (2 n + 1) π/4)` from `s = sin x` and `c = cos x`, by `n mod 4`. -/
def phaseSin (k : UInt64) (s c : Float) : Float :=
  if k == 0 then s - c else if k == 1 then -s - c else if k == 2 then -s + c else s + c

/-- The backward recurrence of `jn` for `2 ^ -30 ≤ x < n`: the continued fraction for
`J n/J (n - 1)`, with its depth `k` from the recurrence `Q`, the recurrence down to `J 0` and `J 1`,
scaled by `1/b` when `b` exceeds `1e100` if `n ln (2 n/x)` reaches the overflow threshold, and the
normalization by the larger of `j0 x` and `j1 x`. -/
def jnBackward (inv half logTab logTab2 tab0 tab1 : Array UInt64) (n : UInt64) (x : Float) :
    Float :=
  let w := (n + n).toFloat / x
  let h := 2.0 / x
  let (_, _, _, k) := LeanExe.repeatWhile 0xFFFFFFFF (w, w * (w + h) - 1.0, w + h, (1 : UInt64))
    (fun s => s.2.1 < Float.ofBits 0x41CDCD6500000000) fun s =>  -- 1.0e9
      let (q0, q1, z, k) := s
      let z := z + h
      (q1, z * q1 - q0, z, k + 1)
  let t := LeanExe.loop (k + 1) (0.0 : Float) fun j t =>
    1.0 / ((2 * (n + k) - 2 * j).toFloat / x - t)
  let tmp := n.toFloat * Log.logWith logTab logTab2 ((2.0 / x) * n.toFloat).abs
  let scale := !(tmp < Float.ofBits 0x40862E42FEFA39EF)  -- 7.09782712893383973096e+02
  let (a, b, t, _) := LeanExe.loop (n - 1) (t, (1.0 : Float), t, (2 * (n - 1)).toFloat) fun _ s =>
    let (a, b, t, di) := s
    let b' := b * di / x - a
    if scale && b' > Float.ofBits 0x54B249AD2594C37D then (b / b', 1.0, t / b', di - 2.0)  -- 1e100
    else (b, b', t, di - 2.0)
  let z := j0With inv half tab0 x
  let w := j1With inv half tab1 x
  if z.abs ≥ w.abs then t * z / b else t * w / a

/-- fdlibm's `jn` with the order as C's `int` in the low 32 bits of `n`. -/
def jnWith (inv half logTab logTab2 tab0 tab1 : Array UInt64) (n : UInt64) (x : Float) : Float :=
  let u := x.toBits
  let ix := (u >>> 32) &&& 0x7fffffff
  if u <<< 1 > 0xFFE0000000000000 then x + x
  else
    let (n, neg) := order n
    let x := if neg then -x else x
    let hx := if neg then (u >>> 32) ^^^ 0x80000000 else u >>> 32
    if n == 0 then j0With inv half tab0 x
    else if n == 1 then j1With inv half tab1 x
    else
      let negative := n &&& 1 == 1 && hx >>> 31 == 1
      let x := x.abs
      let b :=
        if u <<< 1 == 0 || ix ≥ 0x7ff00000 then 0.0
        else if n.toFloat ≤ x then
          if ix ≥ 0x52D00000 then
            invsqrtpi * phaseCos (n &&& 3) (Trig.sinWith inv half x) (Trig.cosWith inv half x) /
              Float.sqrt x
          else
            (LeanExe.loop (n - 1) (j0With inv half tab0 x, j1With inv half tab1 x) fun k s =>
              (s.2, s.2 * ((2 * (k + 1)).toFloat / x) - s.1)).2
        else if ix < 0x3e100000 then
          if n > 33 then 0.0
          else
            let temp := x * 0.5
            let (a, b) := LeanExe.loop (n - 1) ((1.0 : Float), temp) fun k s =>
              (s.1 * (k + 2).toFloat, s.2 * temp)
            b / a
        else jnBackward inv half logTab logTab2 tab0 tab1 n x
      if negative then -b else b

/-- fdlibm's `yn` with the order as C's `int` in the low 32 bits of `n`. -/
def ynWith (inv half logTab logTab2 tab0 tab1 : Array UInt64) (n : UInt64) (x : Float) : Float :=
  let u := x.toBits
  let ix := (u >>> 32) &&& 0x7fffffff
  if u <<< 1 > 0xFFE0000000000000 then x + x
  else if u <<< 1 == 0 then -1.0 / 0.0
  else if u >>> 63 == 1 then 0.0 / 0.0
  else
    let (n, neg) := order n
    let negative := neg && n &&& 1 == 1
    if n == 0 then y0With inv half logTab logTab2 tab0 x
    else if n == 1 then (if negative then -1.0 else 1.0) * y1With inv half logTab logTab2 tab1 x
    else if ix == 0x7ff00000 then 0.0
    else
      let b :=
        if ix ≥ 0x52D00000 then
          invsqrtpi * phaseSin (n &&& 3) (Trig.sinWith inv half x) (Trig.cosWith inv half x) /
            Float.sqrt x
        else
          let (_, _, b) := LeanExe.repeatWhile 0xFFFFFFFF
            ((1 : UInt64), y0With inv half logTab logTab2 tab0 x,
              y1With inv half logTab logTab2 tab1 x)
            (fun s => s.1 < n && s.2.2.toBits >>> 32 != 0xFFF00000) fun s =>
              let (i, a, b) := s
              (i + 1, b, ((2 * i).toFloat / x) * b - a)
          b
      if negative then -b else b

/-- `J 0 x`. -/
def j0 (x : Float) : Float := j0With Trig.invPi Trig.halfPi j0Table x

/-- `J 1 x`. -/
def j1 (x : Float) : Float := j1With Trig.invPi Trig.halfPi j1Table x

/-- `Y 0 x`. -/
def y0 (x : Float) : Float := y0With Trig.invPi Trig.halfPi Log.logTable Log.logTable2 j0Table x

/-- `Y 1 x`. -/
def y1 (x : Float) : Float := y1With Trig.invPi Trig.halfPi Log.logTable Log.logTable2 j1Table x

/-- `J n x` for the order `n` as C's `int` in the low 32 bits. -/
def jn (n : UInt64) (x : Float) : Float :=
  jnWith Trig.invPi Trig.halfPi Log.logTable Log.logTable2 j0Table j1Table n x

/-- `Y n x` for the order `n` as C's `int` in the low 32 bits. -/
def yn (n : UInt64) (x : Float) : Float :=
  ynWith Trig.invPi Trig.halfPi Log.logTable Log.logTable2 j0Table j1Table n x

verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Trig.remSmall, Trig.remMedium,
 Trig.mul64, Trig.clz64, Trig.window, Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2,
 Trig.sinWith, Trig.cosWith, Log.logNear1, Log.logCore, Log.logWith, entry, rangeOf, pAsym,
 qRatio, invsqrtpi, tpi, asym0, j0With, y0With, asym1, j1With, y1With, order, phaseCos,
 phaseSin, jnBackward, jnWith, ynWith, j0, j1, y0, y1, jn, yn]

end Verified.Examples.Bessel
