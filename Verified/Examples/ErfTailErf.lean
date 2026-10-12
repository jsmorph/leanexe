import Verified.Examples.ErfTailErfBase

/-!
One step for `erf` on the tail `[1.25, 6]` of `s_erf.c` for positive arguments.  `R_a/S_a` serves
`[1.25, tailB2]` and `R_b/S_b` serves `[tailB2, 6]`.  For each interval `decide +kernel` checks
`ErfTailEval.tailOK` and the criterion of `ErfTailErfBase.tail_erf_word`, and `tail_kernel_a` or
`tail_kernel_b` bounds `tailF`.  `gen_tail_erf.py` and `emit_tail_erf.py` in the track's scratch
directory compute the intervals and write the file.
-/

namespace Verified.Examples.ErfTailErf
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner RealErf ErfTailBase ErfTailCoeffs ErfTailSplit
  ErfTailEval ErfTailCompose ErfTailErfBase ErfTailKernel

theorem tok0 : tailOK tailRA tailSA (5 / 4 : ℚ) (678327 / 524288 : ℚ)
    (5509996894681858877 / 9223372036854775808 : ℚ)
    (1475739525896764457 / 2305843009213693952 : ℚ) = true := by
  decide +kernel

theorem tcrit0 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (5 / 4 : ℚ) (678327 / 524288 : ℚ)
    (5509996894681858877 / 9223372036854775808 : ℚ)
    (1475739525896764457 / 2305843009213693952 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok1 : tailOK tailRA tailSA (678327 / 524288 : ℚ) (702099 / 524288 : ℚ)
    (642899171562633379 / 1152921504606846976 : ℚ)
    (11019993789363722649 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit1 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (678327 / 524288 : ℚ) (702099 / 524288 : ℚ)
    (642899171562633379 / 1152921504606846976 : ℚ)
    (11019993789363722649 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok2 : tailOK tailRA tailSA (702099 / 524288 : ℚ) (45419 / 32768 : ℚ)
    (2400404681072621071 / 4611686018427387904 : ℚ)
    (10286386745002138633 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit2 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (702099 / 524288 : ℚ) (45419 / 32768 : ℚ)
    (2400404681072621071 / 4611686018427387904 : ℚ)
    (10286386745002138633 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok3 : tailOK tailRA tailSA (45419 / 32768 : ℚ) (1504343 / 1048576 : ℚ)
    (8962430687998183881 / 18446744073709551616 : ℚ)
    (9601618724290488549 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit3 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (45419 / 32768 : ℚ) (1504343 / 1048576 : ℚ)
    (8962430687998183881 / 18446744073709551616 : ℚ)
    (9601618724290488549 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok4 : tailOK tailRA tailSA (1504343 / 1048576 : ℚ) (778531 / 524288 : ℚ)
    (8365804998683726645 / 18446744073709551616 : ℚ)
    (4481215343999093931 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem tcrit4 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1504343 / 1048576 : ℚ) (778531 / 524288 : ℚ)
    (8365804998683726645 / 18446744073709551616 : ℚ)
    (4481215343999093931 / 9223372036854775808 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok5 : tailOK tailRA tailSA (778531 / 524288 : ℚ) (805815 / 524288 : ℚ)
    (3904441024249296237 / 9223372036854775808 : ℚ)
    (8365804998683730361 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit5 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (778531 / 524288 : ℚ) (805815 / 524288 : ℚ)
    (3904441024249296237 / 9223372036854775808 : ℚ)
    (8365804998683730361 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok6 : tailOK tailRA tailSA (805815 / 524288 : ℚ) (1668109 / 1048576 : ℚ)
    (7289046117402881469 / 18446744073709551616 : ℚ)
    (3904441024249297971 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem tcrit6 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (805815 / 524288 : ℚ) (1668109 / 1048576 : ℚ)
    (7289046117402881469 / 18446744073709551616 : ℚ)
    (3904441024249297971 / 9223372036854775808 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok7 : tailOK tailRA tailSA (1668109 / 1048576 : ℚ) (215821 / 131072 : ℚ)
    (3401904975480866449 / 9223372036854775808 : ℚ)
    (7289046117402884707 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit7 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1668109 / 1048576 : ℚ) (215821 / 131072 : ℚ)
    (3401904975480866449 / 9223372036854775808 : ℚ)
    (7289046117402884707 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok8 : tailOK tailRA tailSA (215821 / 131072 : ℚ) (446769 / 262144 : ℚ)
    (3175437056779031165 / 9223372036854775808 : ℚ)
    (6803809950961735921 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit8 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (215821 / 131072 : ℚ) (446769 / 262144 : ℚ)
    (3175437056779031165 / 9223372036854775808 : ℚ)
    (6803809950961735921 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok9 : tailOK tailRA tailSA (446769 / 262144 : ℚ) (231213 / 131072 : ℚ)
    (5928093946748360989 / 18446744073709551616 : ℚ)
    (6350874113558065151 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit9 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (446769 / 262144 : ℚ) (231213 / 131072 : ℚ)
    (5928093946748360989 / 18446744073709551616 : ℚ)
    (6350874113558065151 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok10 : tailOK tailRA tailSA (231213 / 131072 : ℚ) (1914527 / 1048576 : ℚ)
    (5533457238499275149 / 18446744073709551616 : ℚ)
    (5928093946748363623 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit10 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (231213 / 131072 : ℚ) (1914527 / 1048576 : ℚ)
    (5533457238499275149 / 18446744073709551616 : ℚ)
    (5928093946748363623 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok11 : tailOK tailRA tailSA (1914527 / 1048576 : ℚ) (990811 / 524288 : ℚ)
    (5165090302029756755 / 18446744073709551616 : ℚ)
    (5533457238499277607 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit11 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1914527 / 1048576 : ℚ) (990811 / 524288 : ℚ)
    (5165090302029756755 / 18446744073709551616 : ℚ)
    (5533457238499277607 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok12 : tailOK tailRA tailSA (990811 / 524288 : ℚ) (512767 / 262144 : ℚ)
    (4821247549233175275 / 18446744073709551616 : ℚ)
    (2582545151014879525 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem tcrit12 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (990811 / 524288 : ℚ) (512767 / 262144 : ℚ)
    (4821247549233175275 / 18446744073709551616 : ℚ)
    (2582545151014879525 / 9223372036854775808 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok13 : tailOK tailRA tailSA (512767 / 262144 : ℚ) (530737 / 262144 : ℚ)
    (140634171028548217 / 576460752303423488 : ℚ)
    (4821247549233177417 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit13 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (512767 / 262144 : ℚ) (530737 / 262144 : ℚ)
    (140634171028548217 / 576460752303423488 : ℚ)
    (4821247549233177417 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok14 : tailOK tailRA tailSA (530737 / 262144 : ℚ) (2197347 / 1048576 : ℚ)
    (2100352863166457099 / 9223372036854775808 : ℚ)
    (4500293472913544943 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit14 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (530737 / 262144 : ℚ) (2197347 / 1048576 : ℚ)
    (2100352863166457099 / 9223372036854775808 : ℚ)
    (4500293472913544943 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok15 : tailOK tailRA tailSA (2197347 / 1048576 : ℚ) (2274353 / 1048576 : ℚ)
    (980265715887952115 / 4611686018427387904 : ℚ)
    (4200705726332916065 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit15 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (2197347 / 1048576 : ℚ) (2274353 / 1048576 : ℚ)
    (980265715887952115 / 4611686018427387904 : ℚ)
    (4200705726332916065 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok16 : tailOK tailRA tailSA (2274353 / 1048576 : ℚ) (1177029 / 524288 : ℚ)
    (457504367364150253 / 2305843009213693952 : ℚ)
    (1960531431775905101 / 9223372036854775808 : ℚ) = true := by
  decide +kernel

theorem tcrit16 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (2274353 / 1048576 : ℚ) (1177029 / 524288 : ℚ)
    (457504367364150253 / 2305843009213693952 : ℚ)
    (1960531431775905101 / 9223372036854775808 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok17 : tailOK tailRA tailSA (1177029 / 524288 : ℚ) (609139 / 262144 : ℚ)
    (1708192295475159643 / 9223372036854775808 : ℚ)
    (3660034938913203651 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit17 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1177029 / 524288 : ℚ) (609139 / 262144 : ℚ)
    (1708192295475159643 / 9223372036854775808 : ℚ)
    (3660034938913203651 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok18 : tailOK tailRA tailSA (609139 / 262144 : ℚ) (2521945 / 1048576 : ℚ)
    (797238632852907997 / 4611686018427387904 : ℚ)
    (854096147737580201 / 4611686018427387904 : ℚ) = true := by
  decide +kernel

theorem tcrit18 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (609139 / 262144 : ℚ) (2521945 / 1048576 : ℚ)
    (797238632852907997 / 4611686018427387904 : ℚ)
    (854096147737580201 / 4611686018427387904 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok19 : tailOK tailRA tailSA (2521945 / 1048576 : ℚ) (2610327 / 1048576 : ℚ)
    (1488331667154634135 / 9223372036854775808 : ℚ)
    (3188954531411633405 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit19 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (2521945 / 1048576 : ℚ) (2610327 / 1048576 : ℚ)
    (1488331667154634135 / 9223372036854775808 : ℚ)
    (3188954531411633405 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok20 : tailOK tailRA tailSA (2610327 / 1048576 : ℚ) (1350903 / 524288 : ℚ)
    (1389252636923605693 / 9223372036854775808 : ℚ)
    (2976663334309269593 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit20 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (2610327 / 1048576 : ℚ) (1350903 / 524288 : ℚ)
    (1389252636923605693 / 9223372036854775808 : ℚ)
    (2976663334309269593 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok21 : tailOK tailRA tailSA (1350903 / 524288 : ℚ) (2796491 / 1048576 : ℚ)
    (1296769243487669603 / 9223372036854775808 : ℚ)
    (2778505273847212621 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit21 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1350903 / 524288 : ℚ) (2796491 / 1048576 : ℚ)
    (1296769243487669603 / 9223372036854775808 : ℚ)
    (2778505273847212621 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok22 : tailOK tailRA tailSA (2796491 / 1048576 : ℚ) (1447247 / 524288 : ℚ)
    (2420885458375396497 / 18446744073709551616 : ℚ)
    (2593538486975340359 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit22 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (2796491 / 1048576 : ℚ) (1447247 / 524288 : ℚ)
    (2420885458375396497 / 18446744073709551616 : ℚ)
    (2593538486975340359 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok23 : tailOK tailRA tailSA (1447247 / 524288 : ℚ) (748983 / 262144 : ℚ)
    (2259725287012550019 / 18446744073709551616 : ℚ)
    (2420885458375397573 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit23 : tailEps (1405 / 1000 * uQ) (tailDelta tailRA tailSA (1447247 / 524288 : ℚ) (748983 / 262144 : ℚ)
    (2259725287012550019 / 18446744073709551616 : ℚ)
    (2420885458375397573 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok24 : tailOK tailRB tailSB (748983 / 262144 : ℚ) (847569 / 262144 : ℚ)
    (1764612854438115241 / 18446744073709551616 : ℚ)
    (141232830438284439 / 1152921504606846976 : ℚ) = true := by
  decide +kernel

theorem tcrit24 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (748983 / 262144 : ℚ) (847569 / 262144 : ℚ)
    (1764612854438115241 / 18446744073709551616 : ℚ)
    (141232830438284439 / 1152921504606846976 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok25 : tailOK tailRB tailSB (847569 / 262144 : ℚ) (3836527 / 1048576 : ℚ)
    (688990185451457543 / 9223372036854775808 : ℚ)
    (1764612854438116025 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit25 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (847569 / 262144 : ℚ) (3836527 / 1048576 : ℚ)
    (688990185451457543 / 9223372036854775808 : ℚ)
    (1764612854438116025 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok26 : tailOK tailRB tailSB (3836527 / 1048576 : ℚ) (4341517 / 1048576 : ℚ)
    (1076060122380030185 / 18446744073709551616 : ℚ)
    (1377980370902915699 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit26 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (3836527 / 1048576 : ℚ) (4341517 / 1048576 : ℚ)
    (1076060122380030185 / 18446744073709551616 : ℚ)
    (1377980370902915699 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok27 : tailOK tailRB tailSB (4341517 / 1048576 : ℚ) (4912977 / 1048576 : ℚ)
    (840291725627239425 / 18446744073709551616 : ℚ)
    (134507515297503833 / 2305843009213693952 : ℚ) = true := by
  decide +kernel

theorem tcrit27 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (4341517 / 1048576 : ℚ) (4912977 / 1048576 : ℚ)
    (840291725627239425 / 18446744073709551616 : ℚ)
    (134507515297503833 / 2305843009213693952 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok28 : tailOK tailRB tailSB (4912977 / 1048576 : ℚ) (694957 / 131072 : ℚ)
    (656181085424676333 / 18446744073709551616 : ℚ)
    (840291725627239799 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit28 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (4912977 / 1048576 : ℚ) (694957 / 131072 : ℚ)
    (656181085424676333 / 18446744073709551616 : ℚ)
    (840291725627239799 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

theorem tok29 : tailOK tailRB tailSB (694957 / 131072 : ℚ) (6 : ℚ)
    (256204778801521493 / 9223372036854775808 : ℚ)
    (656181085424676625 / 18446744073709551616 : ℚ) = true := by
  decide +kernel

theorem tcrit29 : tailEps (1405 / 1000 * uQ) (tailDelta tailRB tailSB (694957 / 131072 : ℚ) (6 : ℚ)
    (256204778801521493 / 9223372036854775808 : ℚ)
    (656181085424676625 / 18446744073709551616 : ℚ) + epsT) *
    (772 / 10000) < 1 / 2 ^ 53 := by
  decide +kernel

/-- One step for `erf x` on `[5 / 4, (tailB2 : ℝ)]` with `tailRA/tailSA`. -/
theorem tail_erf_a (X : UInt64) (hX : Finite X) (hlo : 5 / 4 ≤ value X) (hhi : value X ≤ (tailB2 : ℝ))
    (E1 E2 : UInt64)
    (hE1 : Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000) →
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000)| < 512 →
      Finite E1 ∧ |value E1 - Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000)))
    (hE2 : Finite (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW raW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW saW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))) →
      |value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW raW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW saW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))))| < 512 →
      Finite E2 ∧ |value E2 - Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW raW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW saW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW raW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW saW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.sub 0x3FF0000000000000 (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X)) := by
  rcases le_or_gt (value X) ((678327 / 524288 : ℚ) : ℝ) with h0 | h0
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok0 tcrit0
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((678327 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (by rw [show ((5 / 4 : ℚ) : ℝ) = 5 / 4 by norm_num]; exact hlo) h0 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((702099 / 524288 : ℚ) : ℝ) with h1 | h1
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok1 tcrit1
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((702099 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h0) h1 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((45419 / 32768 : ℚ) : ℝ) with h2 | h2
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok2 tcrit2
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((45419 / 32768 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h1) h2 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1504343 / 1048576 : ℚ) : ℝ) with h3 | h3
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok3 tcrit3
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1504343 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h2) h3 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((778531 / 524288 : ℚ) : ℝ) with h4 | h4
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok4 tcrit4
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((778531 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h3) h4 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((805815 / 524288 : ℚ) : ℝ) with h5 | h5
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok5 tcrit5
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((805815 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h4) h5 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1668109 / 1048576 : ℚ) : ℝ) with h6 | h6
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok6 tcrit6
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1668109 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h5) h6 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((215821 / 131072 : ℚ) : ℝ) with h7 | h7
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok7 tcrit7
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((215821 / 131072 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h6) h7 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((446769 / 262144 : ℚ) : ℝ) with h8 | h8
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok8 tcrit8
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((446769 / 262144 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h7) h8 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((231213 / 131072 : ℚ) : ℝ) with h9 | h9
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok9 tcrit9
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((231213 / 131072 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h8) h9 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1914527 / 1048576 : ℚ) : ℝ) with h10 | h10
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok10 tcrit10
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1914527 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h9) h10 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((990811 / 524288 : ℚ) : ℝ) with h11 | h11
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok11 tcrit11
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((990811 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h10) h11 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((512767 / 262144 : ℚ) : ℝ) with h12 | h12
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok12 tcrit12
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((512767 / 262144 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h11) h12 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((530737 / 262144 : ℚ) : ℝ) with h13 | h13
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok13 tcrit13
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((530737 / 262144 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h12) h13 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((2197347 / 1048576 : ℚ) : ℝ) with h14 | h14
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok14 tcrit14
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((2197347 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h13) h14 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((2274353 / 1048576 : ℚ) : ℝ) with h15 | h15
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok15 tcrit15
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((2274353 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h14) h15 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1177029 / 524288 : ℚ) : ℝ) with h16 | h16
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok16 tcrit16
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1177029 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h15) h16 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((609139 / 262144 : ℚ) : ℝ) with h17 | h17
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok17 tcrit17
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((609139 / 262144 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h16) h17 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((2521945 / 1048576 : ℚ) : ℝ) with h18 | h18
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok18 tcrit18
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((2521945 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h17) h18 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((2610327 / 1048576 : ℚ) : ℝ) with h19 | h19
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok19 tcrit19
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((2610327 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h18) h19 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1350903 / 524288 : ℚ) : ℝ) with h20 | h20
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok20 tcrit20
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1350903 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h19) h20 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((2796491 / 1048576 : ℚ) : ℝ) with h21 | h21
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok21 tcrit21
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((2796491 / 1048576 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h20) h21 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((1447247 / 524288 : ℚ) : ℝ) with h22 | h22
  · exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok22 tcrit22
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((1447247 / 524288 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h21) h22 E1 E2 hE1 hE2
  exact tail_erf_word tailRA tailSA raW saW ra_rel sa_rel (by simp [tailRA]) (by simp [tailSA]) _ _ _ _ tok23 tcrit23
      (fun x hx => tail_kernel_a x ⟨by have := hx.1; push_cast at this ⊢; linarith, by have := hx.2; have h2 : ((748983 / 262144 : ℚ) : ℝ) ≤ (tailB2 : ℝ) := (by rw [tailB2]; norm_num); linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h22) (by rw [show ((748983 / 262144 : ℚ) : ℝ) = (tailB2 : ℝ) by rw [tailB2]; norm_num]; exact hhi) E1 E2 hE1 hE2

/-- One step for `erf x` on `[(tailB2 : ℝ), 6]` with `tailRB/tailSB`. -/
theorem tail_erf_b (X : UInt64) (hX : Finite X) (hlo : (tailB2 : ℝ) ≤ value X) (hhi : value X ≤ 6)
    (E1 E2 : UInt64)
    (hE1 : Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000) →
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000)| < 512 →
      Finite E1 ∧ |value E1 - Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000)))
    (hE2 : Finite (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW rbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW sbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))) →
      |value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW rbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW sbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))))| < 512 →
      Finite E2 ∧ |value E2 - Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW rbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW sbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW rbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW sbW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.sub 0x3FF0000000000000 (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X)) := by
  rcases le_or_gt (value X) ((847569 / 262144 : ℚ) : ℝ) with h24 | h24
  · exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok24 tcrit24
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((748983 / 262144 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (by rw [show ((748983 / 262144 : ℚ) : ℝ) = (tailB2 : ℝ) by rw [tailB2]; norm_num]; exact hlo) h24 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((3836527 / 1048576 : ℚ) : ℝ) with h25 | h25
  · exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok25 tcrit25
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((847569 / 262144 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h24) h25 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((4341517 / 1048576 : ℚ) : ℝ) with h26 | h26
  · exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok26 tcrit26
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((3836527 / 1048576 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h25) h26 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((4912977 / 1048576 : ℚ) : ℝ) with h27 | h27
  · exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok27 tcrit27
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((4341517 / 1048576 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h26) h27 E1 E2 hE1 hE2
  rcases le_or_gt (value X) ((694957 / 131072 : ℚ) : ℝ) with h28 | h28
  · exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok28 tcrit28
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((4912977 / 1048576 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h27) h28 E1 E2 hE1 hE2
  exact tail_erf_word tailRB tailSB rbW sbW rb_rel sb_rel (by simp [tailRB]) (by simp [tailSB]) _ _ _ _ tok29 tcrit29
      (fun x hx => tail_kernel_b x ⟨by have := hx.1; have h2 : (tailB1 : ℝ) ≤ ((694957 / 131072 : ℚ) : ℝ) := (by rw [tailB1]; norm_num); linarith, by have := hx.2; push_cast at this ⊢; linarith⟩)
      (by norm_num) (by norm_num) X hX (le_of_lt h28) (by rw [show ((6 : ℚ) : ℝ) = 6 by norm_num]; exact hhi) E1 E2 hE1 hE2

#print axioms tail_erf_a
#print axioms tail_erf_b

end Verified.Examples.ErfTailErf
