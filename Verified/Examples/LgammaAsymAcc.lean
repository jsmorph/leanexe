import Verified.Examples.LgammaAsymKern
import Verified.Examples.LgammaAsymLog
import Verified.Examples.LgammaAsymProd
import Verified.Examples.LgammaFastWalk

/-!
`Lgamma.asLgammaAsymAccurate` below `2^120`, against CORE-MATH's Stirling sum
`LgammaApprox.asymAcc` (`asym_gen`).  The code computes the logarithm of `x = xh + xl`
(`LgammaAsymLog.log_dd`), the product of its parts with `x - 1/2`
(`LgammaAsymProd.prod_spec`), the constant of the range, the series term
(`LgammaAsymSeries.series_gen`), and two `fastTwoSum`.  The logarithm's `2^-88` times `x - 1/2`
dominates the error.  `x - 1/2` is `wh + wl` with `wh = xh - 1/2` exact below `2^52`, and with
`wh = xh` and `wl = xl - 1/2` rounded from `2^52` on (`big_test`).  The first `fastTwoSum` is
exact since the product's high part exceeds the rest, and the second is bounded by
`TgammaAcc2.fts_approx`.
-/

namespace Verified.Examples.LgammaAsymAcc
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul LgammaLogAccKern

set_option exponentiation.threshold 4096

/-- The code below `2^120` after its logarithm `T`, for `x - 1/2 = w1 + w2`, with the series at
offset `on.1 + 2` with `on.2` pairs. -/
def asymW (tab : Array UInt64) (T : Float × Float × Float) (xh xl w1 w2 : Float)
    (on : UInt64 × UInt64) : Float × Float × Float :=
  let zh := 1.0 / xh
  let zl := (Fma.fma zh (-xh) 1.0 - xl * zh) * zh
  let L := LgammaAsymLog.corr T.2.1 T.2.2 xh xl
  let P := LgammaAsymProd.prodCode T.1 L.1 L.2 w1 w2
  let S1 := sumDD P.2.1 P.2.2 (entry tab on.1) (entry tab (on.1 + 1))
  let W := mulDD zh zl zh zl
  let F := Lgamma.polyDD tab (on.1 + 2) on.2 W.1 W.2 0.0
  let G := mulDD zh zl F.1 F.2
  let S2 := sumDD S1.1 S1.2 G.1 G.2
  let A := fastTwoSum P.1 S2.1
  let B := fastTwoSum A.2 S2.2
  (A.1, B.1, B.2)

/-- The code below `2^120` after its logarithm `T`. -/
def asymSmall (tab : Array UInt64) (T : Float × Float × Float) (xh xl : Float)
    (on : UInt64 × UInt64) : Float × Float × Float :=
  let w : Float × Float := if xh.toBits >>> 52 > 0x3ff + 51 then (xh, xl - 0.5) else (xh - 0.5, xl)
  asymW tab T xh xl w.1 w.2 on

/-- The code from `2^120` on after its logarithm `T`. -/
def asymBig (T : Float × Float × Float) (xh xl : Float) : Float × Float × Float :=
  LgammaAsymProd.prodCode T.1 T.2.1 T.2.2 xh (xl - 0.5)

set_option maxHeartbeats 2000000 in
/-- The code of `asLgammaAsymAccurate` in the two branches. -/
theorem asym_eq (logTab hTab tab : Array UInt64) (xh xl : Float) :
    Lgamma.asLgammaAsymAccurate logTab hTab tab xh xl =
      if xh < Float.ofBits 0x4770000000000000 then
        asymSmall tab (Lgamma.asLogdAccurate logTab hTab xh) xh xl
          (if xh ≥ 48.0 then (0, 7) else if xh ≥ 14.5 then (16, 11) else (40, 27))
      else asymBig (Lgamma.asLogdAccurate logTab hTab xh) xh xl := by
  unfold Lgamma.asLgammaAsymAccurate asymSmall asymW asymBig LgammaAsymLog.corr LgammaAsymProd.prodCode
  dsimp only

/-- The test of the code for `xh ≥ 2^52` on a positive double. -/
theorem big_test (xh : Float) (hf : Finite xh.toBits) (hpos : 0 < value xh.toBits) :
    (xh.toBits >>> 52 > 0x3ff + 51) ↔ 2 ^ 52 ≤ value xh.toBits := by
  have hp := (F64Order.positiveBits_iff xh.toBits).mpr ⟨hf, hpos⟩
  simp only [F64Order.positiveBits, Bool.and_eq_true, decide_eq_true_eq] at hp
  have h63 : xh.toBits.toNat < 9223372036854775808 := by
    have := hp.2
    rw [UInt64.lt_iff_toNat_lt] at this
    simp only [UInt64.reduceToNat] at this
    omega
  have hmod : xh.toBits.toNat % 9223372036854775808 = xh.toBits.toNat := Nat.mod_eq_of_lt h63
  have hc : value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x4330000000000000 = 2 ^ 52 by
      decide +kernel]
    norm_num
  have hsh : (xh.toBits >>> 52 > 0x3ff + 51) ↔ 0x4330000000000000 ≤ xh.toBits.toNat := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, UInt64.reduceAdd, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      Nat.reducePow]
    omega
  rw [hsh]
  constructor
  · intro h
    have := LgammaFastWalk.word_le_abs xh.toBits 0x4330000000000000 (2 ^ 52) hc (by decide)
      (by rw [hmod]; exact h)
    rwa [abs_of_pos hpos] at this
  · intro h
    rcases lt_or_ge xh.toBits.toNat 0x4330000000000000 with hlt | hge
    · have := LgammaFastWalk.abs_lt_word xh.toBits 0x4330000000000000 (2 ^ 52) hc (by decide)
        (by rw [hmod]; exact hlt)
      rw [abs_of_pos hpos] at this
      linarith
    · exact hge


set_option maxHeartbeats 4000000 in
/-- **The last four operations** of the code below `2^120`: the constant and the series term added
to the product's middle and low parts with `sumDD`, and the two `fastTwoSum`. -/
theorem tail_spec (P1 P2 P3 ch cl G1 G2 : Float) (hp1 : Finite P1.toBits) (hp2 : Finite P2.toBits)
    (hp3 : Finite P3.toBits) (hcf : Finite ch.toBits) (hclf : Finite cl.toBits)
    (hg1 : Finite G1.toBits) (hg2 : Finite G2.toBits) (U : ℝ) (hU3 : 3 ≤ U) (hU : U ≤ 2 ^ 801)
    (hP1 : 3 / 10 * U ≤ value P1.toBits) (hP1u : value P1.toBits ≤ 561 * U)
    (hP2 : |value P2.toBits| ≤ U / 2 ^ 37) (hP3 : |value P3.toBits| ≤ U / 2 ^ 84)
    (hch : |value ch.toBits| ≤ 1 / 2) (hcl : |value cl.toBits| ≤ 1 / 2 ^ 50)
    (hG1 : |value G1.toBits| ≤ 1 / 2 ^ 4) (hG2 : |value G2.toBits| ≤ 1 / 2 ^ 50) :
    let S1 := sumDD P2 P3 ch cl
    let S2 := sumDD S1.1 S1.2 G1 G2
    let A := fastTwoSum P1 S2.1
    let B := fastTwoSum A.2 S2.2
    Finite A.1.toBits ∧ Finite B.1.toBits ∧ Finite B.2.toBits ∧
      |value A.1.toBits + value B.1.toBits + value B.2.toBits -
          (value P1.toBits + value P2.toBits + value P3.toBits + (value ch.toBits + value cl.toBits) +
            (value G1.toBits + value G2.toBits))| ≤ U / 2 ^ 120 + 1 / 2 ^ 98 ∧
      0 < value A.1.toBits ∧
      |value B.1.toBits| ≤ value A.1.toBits / 2 ^ 45 ∧
      |value B.2.toBits| ≤ value A.1.toBits / 2 ^ 96 := by
  intro S1 S2 A B
  have hU0 : 0 < U := by linarith
  -- `S1`
  have hl2 : |value P2.toBits| < 2 ^ 898 := by
    have : U / 2 ^ 37 ≤ 2 ^ 801 / 2 ^ 37 := div_le_div_of_nonneg_right hU (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 37 < 2 ^ 898)]
  have hlc : |value ch.toBits| < 2 ^ 898 := by linarith [(by norm_num : (1 : ℝ) / 2 < 2 ^ 898)]
  obtain ⟨s1f, s2f, s1e, s1l, s1h⟩ := sumDD_spec P2 P3 ch cl hp2 hp3 hcf hclf hl2 hlc
    (U / 2 ^ 84 + 1 / 2 ^ 50) (by linarith) (by
      have : U / 2 ^ 84 ≤ 2 ^ 801 / 2 ^ 84 := div_le_div_of_nonneg_right hU (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 84 + 1 / 2 ^ 50 ≤ 2 ^ 800)])
  rw [show sumDD P2 P3 ch cl = S1 from rfl] at s1f s2f s1e s1l s1h
  have hS1h : |value S1.1.toBits| ≤ U / 2 ^ 36 + 6 / 10 := by
    have h1 := abs_add_le (value P2.toBits) (value ch.toBits)
    have h2 := mul_le_mul_of_nonneg_right (show |value P2.toBits + value ch.toBits| ≤ U / 2 ^ 37 + 1 / 2
      by linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have : (U / 2 ^ 37 + 1 / 2) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ U / 2 ^ 36 + 6 / 10 := by
      have : (U / 2 ^ 37 + 1 / 2) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 =
          U * ((1 + 1 / 2 ^ 51) / 2 ^ 37) + (1 / 2 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 37 ≤ 1 / 2 ^ 36)
        hU0.le
      linarith [(by norm_num : (1 : ℝ) / 2 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 6 / 10),
        (by ring : U * (1 / 2 ^ 36) = U / 2 ^ 36)]
    linarith
  have hS1l : |value S1.2.toBits| ≤ U / 2 ^ 83 + 1 / 2 ^ 49 := by
    have h1 : |value S1.1.toBits| / 2 ^ 51 ≤ (U / 2 ^ 36 + 6 / 10) / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS1h (by norm_num)
    have : (U / 2 ^ 84 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + (U / 2 ^ 36 + 6 / 10) / 2 ^ 51 +
        1 / 2 ^ 1073 ≤ U / 2 ^ 83 + 1 / 2 ^ 49 := by
      have : (U / 2 ^ 84 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + (U / 2 ^ 36 + 6 / 10) / 2 ^ 51 +
          1 / 2 ^ 1073 = U * ((1 + 1 / 2 ^ 51) / 2 ^ 84 + 1 / 2 ^ 36 / 2 ^ 51) +
            (1 / 2 ^ 50 * (1 + 1 / 2 ^ 51) + 6 / 10 / 2 ^ 51 + 1 / 2 ^ 1073) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 84 +
        1 / 2 ^ 36 / 2 ^ 51 ≤ 1 / 2 ^ 83) hU0.le
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (1 + 1 / 2 ^ 51) + 6 / 10 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
        1 / 2 ^ 49), (by ring : U * (1 / 2 ^ 83) = U / 2 ^ 83)]
    linarith
  have hS1e : |value S1.1.toBits + value S1.2.toBits -
      (value P2.toBits + value P3.toBits + (value ch.toBits + value cl.toBits))| ≤
      U / 2 ^ 130 + 1 / 2 ^ 100 := by
    have h1 : |value S1.1.toBits| / 2 ^ 52 ≤ (U / 2 ^ 36 + 6 / 10) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS1h (by norm_num)
    have : (3 * (U / 2 ^ 84 + 1 / 2 ^ 50) + (U / 2 ^ 36 + 6 / 10) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
        U / 2 ^ 130 + 1 / 2 ^ 100 := by
      have : (3 * (U / 2 ^ 84 + 1 / 2 ^ 50) + (U / 2 ^ 36 + 6 / 10) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 =
          U * ((3 / 2 ^ 84 + 1 / 2 ^ 36 / 2 ^ 52) / 2 ^ 53) +
            (3 / 2 ^ 50 + 6 / 10 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((3 : ℝ) / 2 ^ 84 + 1 / 2 ^ 36 / 2 ^ 52) /
        2 ^ 53 ≤ 1 / 2 ^ 130) hU0.le
      linarith [(by norm_num : ((3 : ℝ) / 2 ^ 50 + 6 / 10 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
        1 / 2 ^ 100), (by ring : U * (1 / 2 ^ 130) = U / 2 ^ 130)]
    have h2 : (3 * (U / 2 ^ 84 + 1 / 2 ^ 50) + |value S1.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
        (3 * (U / 2 ^ 84 + 1 / 2 ^ 50) + (U / 2 ^ 36 + 6 / 10) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  -- `S2`
  have hl3 : |value S1.1.toBits| < 2 ^ 898 := by
    have : U / 2 ^ 36 ≤ 2 ^ 801 / 2 ^ 36 := div_le_div_of_nonneg_right hU (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 36 + 6 / 10 < 2 ^ 898)]
  have hl4 : |value G1.toBits| < 2 ^ 898 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 4 < 2 ^ 898)]
  obtain ⟨t1f, t2f, t1e, t1l, t1h⟩ := sumDD_spec S1.1 S1.2 G1 G2 s1f s2f hg1 hg2 hl3 hl4
    (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) (by linarith) (by
      have : U / 2 ^ 83 ≤ 2 ^ 801 / 2 ^ 83 := div_le_div_of_nonneg_right hU (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 801 / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50 ≤ 2 ^ 800)])
  rw [show sumDD S1.1 S1.2 G1 G2 = S2 from rfl] at t1f t2f t1e t1l t1h
  have hS2h : |value S2.1.toBits| ≤ U / 2 ^ 35 + 7 / 10 := by
    have h1 := abs_add_le (value S1.1.toBits) (value G1.toBits)
    have h2 := mul_le_mul_of_nonneg_right (show |value S1.1.toBits + value G1.toBits| ≤
      U / 2 ^ 36 + 6 / 10 + 1 / 2 ^ 4 by linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have : (U / 2 ^ 36 + 6 / 10 + 1 / 2 ^ 4) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
        U / 2 ^ 35 + 7 / 10 := by
      have : (U / 2 ^ 36 + 6 / 10 + 1 / 2 ^ 4) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 =
          U * ((1 + 1 / 2 ^ 51) / 2 ^ 36) + ((6 / 10 + 1 / 2 ^ 4) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) := by
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 36 ≤ 1 / 2 ^ 35)
        hU0.le
      linarith [(by norm_num : ((6 : ℝ) / 10 + 1 / 2 ^ 4) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 7 / 10),
        (by ring : U * (1 / 2 ^ 35) = U / 2 ^ 35)]
    linarith
  have hS2l : |value S2.2.toBits| ≤ U / 2 ^ 82 + 1 / 2 ^ 48 := by
    have h1 : |value S2.1.toBits| / 2 ^ 51 ≤ (U / 2 ^ 35 + 7 / 10) / 2 ^ 51 :=
      div_le_div_of_nonneg_right hS2h (by norm_num)
    have : (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + (U / 2 ^ 35 + 7 / 10) / 2 ^ 51 +
        1 / 2 ^ 1073 ≤ U / 2 ^ 82 + 1 / 2 ^ 48 := by
      have : (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + (U / 2 ^ 35 + 7 / 10) / 2 ^ 51 +
          1 / 2 ^ 1073 = U * ((1 + 1 / 2 ^ 51) / 2 ^ 83 + 1 / 2 ^ 35 / 2 ^ 51) +
            ((1 / 2 ^ 49 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + 7 / 10 / 2 ^ 51 + 1 / 2 ^ 1073) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 51 : ℝ) / 2 ^ 83 +
        1 / 2 ^ 35 / 2 ^ 51 ≤ 1 / 2 ^ 82) hU0.le
      linarith [(by norm_num : ((1 : ℝ) / 2 ^ 49 + 1 / 2 ^ 50) * (1 + 1 / 2 ^ 51) + 7 / 10 / 2 ^ 51 +
        1 / 2 ^ 1073 ≤ 1 / 2 ^ 48), (by ring : U * (1 / 2 ^ 82) = U / 2 ^ 82)]
    linarith
  have hS2e : |value S2.1.toBits + value S2.2.toBits -
      (value S1.1.toBits + value S1.2.toBits + (value G1.toBits + value G2.toBits))| ≤
      U / 2 ^ 129 + 1 / 2 ^ 99 := by
    have h1 : |value S2.1.toBits| / 2 ^ 52 ≤ (U / 2 ^ 35 + 7 / 10) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hS2h (by norm_num)
    have : (3 * (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) + (U / 2 ^ 35 + 7 / 10) / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤ U / 2 ^ 129 + 1 / 2 ^ 99 := by
      have : (3 * (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) + (U / 2 ^ 35 + 7 / 10) / 2 ^ 52 +
          1 / 2 ^ 1074) / 2 ^ 53 = U * ((3 / 2 ^ 83 + 1 / 2 ^ 35 / 2 ^ 52) / 2 ^ 53) +
            (3 * (1 / 2 ^ 49 + 1 / 2 ^ 50) + 7 / 10 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : ((3 : ℝ) / 2 ^ 83 + 1 / 2 ^ 35 / 2 ^ 52) /
        2 ^ 53 ≤ 1 / 2 ^ 129) hU0.le
      linarith [(by norm_num : ((3 : ℝ) * (1 / 2 ^ 49 + 1 / 2 ^ 50) + 7 / 10 / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤ 1 / 2 ^ 99), (by ring : U * (1 / 2 ^ 129) = U / 2 ^ 129)]
    have h2 : (3 * (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) + |value S2.1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤ (3 * (U / 2 ^ 83 + 1 / 2 ^ 49 + 1 / 2 ^ 50) +
          (U / 2 ^ 35 + 7 / 10) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  -- `A = fastTwoSum P1 S2.1`, exact
  have hS2P : |value S2.1.toBits| ≤ |value P1.toBits| := by
    rw [abs_of_pos (show (0 : ℝ) < value P1.toBits by linarith)]
    have : U / 2 ^ 35 + 7 / 10 ≤ 3 / 10 * U := by
      have : U / 2 ^ 35 ≤ U / 100 := div_le_div_of_nonneg_left hU0.le (by norm_num) (by norm_num)
      linarith
    linarith
  obtain ⟨a1f, a2f, aeq, -, a2b⟩ := fastTwoSum_spec P1 S2.1 hp1 t1f hS2P (by
    rw [abs_of_pos (show (0 : ℝ) < value P1.toBits by linarith)]
    linarith [(by norm_num : (561 : ℝ) * 2 ^ 801 < 2 ^ 900), mul_le_mul_of_nonneg_left hU
      (by norm_num : (0 : ℝ) ≤ 561)])
  rw [show fastTwoSum P1 S2.1 = A from rfl] at a1f a2f aeq a2b
  have hA1 : 1 / 20 * U ≤ value A.1.toBits := by
    have h1 := abs_le.mp a2b
    have h2 := abs_le.mp (show |value S2.1.toBits| ≤ U / 2 ^ 35 + 7 / 10 from hS2h)
    have h3 : U / 2 ^ 35 ≤ U / 100 := div_le_div_of_nonneg_left hU0.le (by norm_num) (by norm_num)
    have h4 : |value A.1.toBits| / 2 ^ 52 ≤ (562 * U) / 2 ^ 52 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have := abs_add_le (value A.1.toBits + value A.2.toBits) (-value A.2.toBits)
      rw [show value A.1.toBits + value A.2.toBits + -value A.2.toBits = value A.1.toBits by ring,
        abs_neg, aeq] at this
      have h5 := abs_add_le (value P1.toBits) (value S2.1.toBits)
      rw [abs_of_pos (show 0 < value P1.toBits by linarith)] at h5
      have h6 : |value A.1.toBits| / 2 ^ 52 ≤ |value A.1.toBits| / 2 := div_le_div_of_nonneg_left
        (abs_nonneg _) (by norm_num) (by norm_num)
      nlinarith
    have h7 : (562 * U) / 2 ^ 52 ≤ U / 1000 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 1000), (abs_le.mp a2b).1,
      (by linarith : (7 : ℝ) / 10 ≤ 7 / 30 * U)]
  have hA0 : 0 < value A.1.toBits := by linarith
  -- `B = fastTwoSum A.2 S2.2`
  obtain ⟨b1f, b2f, be, b1b, b2b⟩ := TgammaAcc2.fts_approx A.2 S2.2 a2f t2f
    (|value A.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) (U / 2 ^ 82 + 1 / 2 ^ 48) a2b hS2l (by
      have h1 : |value A.1.toBits| ≤ 562 * U := by
        have := abs_add_le (value A.1.toBits + value A.2.toBits) (-value A.2.toBits)
        rw [show value A.1.toBits + value A.2.toBits + -value A.2.toBits = value A.1.toBits by ring,
          abs_neg, aeq] at this
        have h5 := abs_add_le (value P1.toBits) (value S2.1.toBits)
        rw [abs_of_pos (show 0 < value P1.toBits by linarith)] at h5
        have h6 : |value A.1.toBits| / 2 ^ 52 ≤ |value A.1.toBits| / 2 := div_le_div_of_nonneg_left
          (abs_nonneg _) (by norm_num) (by norm_num)
        nlinarith
      have h2 : |value A.1.toBits| / 2 ^ 52 ≤ 562 * 2 ^ 801 / 2 ^ 52 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        nlinarith
      have h3 : U / 2 ^ 82 ≤ 2 ^ 801 / 2 ^ 82 := div_le_div_of_nonneg_right hU (by norm_num)
      linarith [(by norm_num : (562 : ℝ) * 2 ^ 801 / 2 ^ 52 + 1 / 2 ^ 1074 + (2 ^ 801 / 2 ^ 82 +
        1 / 2 ^ 48) ≤ 2 ^ 1000)])
  rw [show fastTwoSum A.2 S2.2 = B from rfl] at b1f b2f be b1b b2b
  rw [abs_of_pos hA0] at be b1b b2b
  -- `U` against `A.1`
  have hUA : U ≤ 20 * value A.1.toBits := by linarith
  refine ⟨a1f, b1f, b2f, ?_, hA0, ?_, ?_⟩
  · have hid : value A.1.toBits + value B.1.toBits + value B.2.toBits -
        (value P1.toBits + value P2.toBits + value P3.toBits + (value ch.toBits + value cl.toBits) +
          (value G1.toBits + value G2.toBits)) =
        (value B.1.toBits + value B.2.toBits - (value A.2.toBits + value S2.2.toBits)) +
        (value S2.1.toBits + value S2.2.toBits -
          (value S1.1.toBits + value S1.2.toBits + (value G1.toBits + value G2.toBits))) +
        (value S1.1.toBits + value S1.2.toBits -
          (value P2.toBits + value P3.toBits + (value ch.toBits + value cl.toBits))) +
        (value A.1.toBits + value A.2.toBits - (value P1.toBits + value S2.1.toBits)) := by ring
    rw [hid, aeq, sub_self, add_zero]
    have h1 := abs_add_le ((value B.1.toBits + value B.2.toBits - (value A.2.toBits + value S2.2.toBits)) +
      (value S2.1.toBits + value S2.2.toBits -
        (value S1.1.toBits + value S1.2.toBits + (value G1.toBits + value G2.toBits))))
      (value S1.1.toBits + value S1.2.toBits -
        (value P2.toBits + value P3.toBits + (value ch.toBits + value cl.toBits)))
    have h2 := abs_add_le (value B.1.toBits + value B.2.toBits - (value A.2.toBits + value S2.2.toBits))
      (value S2.1.toBits + value S2.2.toBits -
        (value S1.1.toBits + value S1.2.toBits + (value G1.toBits + value G2.toBits)))
    have h3 : (U / 2 ^ 82 + 1 / 2 ^ 48) / 2 ^ 53 + (value A.1.toBits / 2 ^ 52 + 1 / 2 ^ 1074 +
        (U / 2 ^ 82 + 1 / 2 ^ 48)) / 2 ^ 104 ≤ U / 2 ^ 130 + 1 / 2 ^ 100 := by
      have hA562 : value A.1.toBits ≤ 562 * U := by
        have h6 := abs_le.mp a2b
        rw [abs_of_pos hA0] at h6
        have h7 := abs_le.mp hS2h
        have h8 : U / 2 ^ 35 ≤ U / 100 := div_le_div_of_nonneg_left hU0.le (by norm_num) (by norm_num)
        have h9 : value A.1.toBits / 2 ^ 52 ≤ value A.1.toBits / 2 :=
          div_le_div_of_nonneg_left hA0.le (by norm_num) (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1)]
      have : (U / 2 ^ 82 + 1 / 2 ^ 48) / 2 ^ 53 + (value A.1.toBits / 2 ^ 52 + 1 / 2 ^ 1074 +
          (U / 2 ^ 82 + 1 / 2 ^ 48)) / 2 ^ 104 ≤ (U / 2 ^ 82 + 1 / 2 ^ 48) / 2 ^ 53 +
          (562 * U / 2 ^ 52 + 1 / 2 ^ 1074 + (U / 2 ^ 82 + 1 / 2 ^ 48)) / 2 ^ 104 := by
        have := div_le_div_of_nonneg_right hA562 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
        have := div_le_div_of_nonneg_right (by linarith : value A.1.toBits / 2 ^ 52 + 1 / 2 ^ 1074 +
          (U / 2 ^ 82 + 1 / 2 ^ 48) ≤ 562 * U / 2 ^ 52 + 1 / 2 ^ 1074 + (U / 2 ^ 82 + 1 / 2 ^ 48))
          (by norm_num : (0 : ℝ) ≤ 2 ^ 104)
        linarith
      have h7 : (U / 2 ^ 82 + 1 / 2 ^ 48) / 2 ^ 53 + (562 * U / 2 ^ 52 + 1 / 2 ^ 1074 +
          (U / 2 ^ 82 + 1 / 2 ^ 48)) / 2 ^ 104 = U * (1 / 2 ^ 82 / 2 ^ 53 + (562 / 2 ^ 52 +
            1 / 2 ^ 82) / 2 ^ 104) + (1 / 2 ^ 48 / 2 ^ 53 + (1 / 2 ^ 1074 + 1 / 2 ^ 48) / 2 ^ 104) := by
        ring
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 82 / 2 ^ 53 + (562 / 2 ^ 52 +
        1 / 2 ^ 82) / 2 ^ 104 ≤ 1 / 2 ^ 130) hU0.le
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 / 2 ^ 53 + (1 / 2 ^ 1074 + 1 / 2 ^ 48) / 2 ^ 104 ≤
        1 / 2 ^ 100), (by ring : U * (1 / 2 ^ 130) = U / 2 ^ 130)]
    have h4 : U / 2 ^ 130 + 1 / 2 ^ 100 + (U / 2 ^ 129 + 1 / 2 ^ 99) + (U / 2 ^ 130 + 1 / 2 ^ 100) ≤
        U / 2 ^ 120 + 1 / 2 ^ 98 := by
      have : U / 2 ^ 130 + U / 2 ^ 129 + U / 2 ^ 130 ≤ U / 2 ^ 120 := by
        have : U / 2 ^ 130 + U / 2 ^ 129 + U / 2 ^ 130 = U * (1 / 2 ^ 130 + 1 / 2 ^ 129 + 1 / 2 ^ 130) := by
          ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 130 + 1 / 2 ^ 129 + 1 / 2 ^ 130 ≤
          1 / 2 ^ 120) hU0.le
        linarith [(by ring : U * (1 / 2 ^ 120) = U / 2 ^ 120)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 99 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 98)]
    linarith
  · -- `|B.1| ≤ A.1/2^45`
    have hA03 : 3 / 20 ≤ value A.1.toBits := by linarith
    have h1 : U / 2 ^ 82 ≤ 20 * value A.1.toBits / 2 ^ 82 := div_le_div_of_nonneg_right hUA (by norm_num)
    have h2 : (1 : ℝ) / 2 ^ 48 ≤ 20 / 3 * value A.1.toBits / 2 ^ 48 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have h3 : (1 : ℝ) / 2 ^ 1074 ≤ 20 / 3 * value A.1.toBits / 2 ^ 1074 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    set c : ℝ := 1 / 2 ^ 52 + 20 / 3 / 2 ^ 1074 + 20 / 2 ^ 82 + 20 / 3 / 2 ^ 48 with hc
    have key : value A.1.toBits / 2 ^ 52 + 1 / 2 ^ 1074 + (U / 2 ^ 82 + 1 / 2 ^ 48) ≤
        value A.1.toBits * c := by
      have : value A.1.toBits * c = value A.1.toBits / 2 ^ 52 + 20 / 3 * value A.1.toBits / 2 ^ 1074 +
          (20 * value A.1.toBits / 2 ^ 82 + 20 / 3 * value A.1.toBits / 2 ^ 48) := by rw [hc]; ring
      linarith
    have k2 := mul_le_mul_of_nonneg_right key (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
    have k3 := mul_le_mul_of_nonneg_left (show c * (1 + 1 / 2 ^ 53) ≤ 1 / 2 ^ 45 by rw [hc]; norm_num)
      hA0.le
    linarith [(by ring : value A.1.toBits * c * (1 + 1 / 2 ^ 53) =
      value A.1.toBits * (c * (1 + 1 / 2 ^ 53))),
      (by ring : value A.1.toBits * (1 / 2 ^ 45) = value A.1.toBits / 2 ^ 45)]
  · -- `|B.2| ≤ A.1/2^96`
    have hA03 : 3 / 20 ≤ value A.1.toBits := by linarith
    have h1 : U / 2 ^ 82 ≤ 20 * value A.1.toBits / 2 ^ 82 := div_le_div_of_nonneg_right hUA (by norm_num)
    have h2 : (1 : ℝ) / 2 ^ 48 ≤ 20 / 3 * value A.1.toBits / 2 ^ 48 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have h3 : (1 : ℝ) / 2 ^ 1074 ≤ 20 / 3 * value A.1.toBits / 2 ^ 1074 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    set c : ℝ := 1 / 2 ^ 52 + 20 / 3 / 2 ^ 1074 + 20 / 2 ^ 82 + 20 / 3 / 2 ^ 48 with hc
    have key : value A.1.toBits / 2 ^ 52 + 1 / 2 ^ 1074 + (U / 2 ^ 82 + 1 / 2 ^ 48) ≤
        value A.1.toBits * c := by
      have : value A.1.toBits * c = value A.1.toBits / 2 ^ 52 + 20 / 3 * value A.1.toBits / 2 ^ 1074 +
          (20 * value A.1.toBits / 2 ^ 82 + 20 / 3 * value A.1.toBits / 2 ^ 48) := by rw [hc]; ring
      linarith
    have k2 := div_le_div_of_nonneg_right key (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    have k3 := mul_le_mul_of_nonneg_left (show c / 2 ^ 51 ≤ 1 / 2 ^ 96 by rw [hc]; norm_num) hA0.le
    linarith [(by ring : value A.1.toBits * c / 2 ^ 51 = value A.1.toBits * (c / 2 ^ 51)),
      (by ring : value A.1.toBits * (1 / 2 ^ 96) = value A.1.toBits / 2 ^ 96)]

set_option maxHeartbeats 8000000 in
/-- **The code below `2^120` against `asymAcc`**, for one range of the series, given
`x - 1/2 = w1 + w2` within `xh/2^103`. -/
theorem asym_gen (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (o N P : ℕ) (Xq Xh Xl Rm lo hi Lp : ℚ) (C Cl E Λ K : List ℚ)
    (hok : LgammaPolyIv.stepsIvOk Lgamma.asymTable (o + 2) N P Xq Xh Xl C Cl E Λ K = true)
    (hval : LgammaAsymSeries.valOk Lgamma.asymTable (o + 2) N P Xq lo hi = true)
    (hlip : TgammaPolyLip.lipQ Xq (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) ≤ Lp)
    (hE0 : ∀ m, 0 ≤ E.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0) (hP : 0 < P) (hN1 : 1 ≤ N)
    (hon : o + 2 + 2 * N < 2 ^ 63)
    (hXh : Rm ^ 2 * (1 + 1 / 2 ^ 50) ≤ Xh) (hXl : Rm ^ 2 / 2 ^ 47 + 1 / 2 ^ 1069 ≤ Xl)
    (hX : Rm ^ 2 * (1 + 1 / 2 ^ 40) ≤ Xq) (hRm1 : Rm ≤ 1)
    (hEn : E.getD (N - 1) 0 ≤ 1 / 2 ^ 105) (hΛn : Λ.getD (N - 1) 0 ≤ 1 / 2 ^ 52)
    (hhi : hi ≤ 1 / 8) (hlo : -(1 / 8) ≤ lo) (hLp : Lp ≤ 1 / 2 ^ 8)
    (hc1 : Wasm.IEEE64.isFinite Lgamma.asymTable[o]! = true)
    (hc2 : Wasm.IEEE64.isFinite Lgamma.asymTable[o + 1]! = true)
    (hcv1 : |((PolyBound.ratOfWord Lgamma.asymTable[o]! : ℚ) : ℝ)| ≤ 1 / 2)
    (hcv2 : |((PolyBound.ratOfWord Lgamma.asymTable[o + 1]! : ℚ) : ℝ)| ≤ 1 / 2 ^ 50)
    (o' n' : UInt64) (ho : o'.toNat = o) (ho1 : (o' + 1).toNat = o + 1)
    (ho2 : (o' + 2).toNat = o + 2) (hn : n'.toNat = N)
    (xh xl w1 w2 : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hw1f : Finite w1.toBits) (hw2f : Finite w2.toBits)
    (hlo' : 15 / 4 ≤ value xh.toBits) (hhi' : value xh.toBits < 2 ^ 120)
    (hRm : 1 / value xh.toBits ≤ Rm) (hlb : |value xl.toBits| ≤ value xh.toBits / 2 ^ 51)
    (hw1lo : value xh.toBits - 1 / 2 ≤ value w1.toBits) (hw1hi : value w1.toBits ≤ value xh.toBits)
    (hw2 : |value w2.toBits| ≤ value w1.toBits / 2 ^ 50)
    (hw : |value w1.toBits + value w2.toBits - (value xh.toBits + value xl.toBits - 1 / 2)| ≤
      value xh.toBits / 2 ^ 103) :
    let r := asymW Lgamma.asymTable (Lgamma.asLogdAccurate Tgamma.logdTable H xh) xh xl w1 w2 (o', n')
    Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
      |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
          LgammaApprox.asymAcc o N (value xh.toBits + value xl.toBits)| ≤
        (value xh.toBits + value xl.toBits) * (1 / 2 ^ 88 + 1 / 2 ^ 91) ∧
      0 < value r.1.toBits ∧ |value r.2.1.toBits| ≤ value r.1.toBits / 2 ^ 45 ∧
      |value r.2.2.toBits| ≤ value r.1.toBits / 2 ^ 96 := by
  intro r
  have hx0 : 0 < value xh.toBits := by linarith
  -- the values of `x`
  have hvl : |value xl.toBits| ≤ value xh.toBits / 2 ^ 51 := hlb
  have hXlo : value xh.toBits * (1 - 1 / 2 ^ 51) ≤ value xh.toBits + value xl.toBits := by
    have := (abs_le.mp hvl).1; linarith
  have hXhi : value xh.toBits + value xl.toBits ≤ value xh.toBits * (1 + 1 / 2 ^ 51) := by
    have := (abs_le.mp hvl).2; linarith
  have hX0 : 0 < value xh.toBits + value xl.toBits := by nlinarith
  have hX374 : 374 / 100 ≤ value xh.toBits + value xl.toBits := by nlinarith
  -- `log x` from 1.31 to 84
  have hlogX : 131 / 100 ≤ Real.log (value xh.toBits + value xl.toBits) ∧
      Real.log (value xh.toBits + value xl.toBits) ≤ 84 := by
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    constructor
    · have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (value xh.toBits + value xl.toBits) / 4 by
        positivity)
      rw [Real.log_div hX0.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
      rw [inv_div] at h1
      have h2 : 4 / (value xh.toBits + value xl.toBits) ≤ 4 / (374 / 100) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX374
      push_cast at h1
      norm_num at hl2 h2 ⊢
      linarith
    · have h1 : Real.log (value xh.toBits + value xl.toBits) ≤ Real.log (2 ^ 121) :=
        Real.log_le_log hX0 (by nlinarith [(by norm_num : (2 : ℝ) ^ 120 * (1 + 1 / 2 ^ 51) ≤ 2 ^ 121)])
      rw [Real.log_pow] at h1
      push_cast at h1
      norm_num at hl2'
      nlinarith
  -- the reciprocal
  obtain ⟨zf, zlf, hz1, hz2, hz3⟩ := LgammaAsymRecip.recip_dd hF xh xl hxh hxl (by linarith)
    hhi'.le hlb
  -- the logarithm
  obtain ⟨t0f, Lf1, Lf2, hLe, hL1, hL2⟩ := LgammaAsymLog.log_dd hF hLA xh xl hxh hxl hlo' hhi'.le hlb
  set T := Lgamma.asLogdAccurate Tgamma.logdTable H xh with hTdef
  set L := LgammaAsymLog.corr T.2.1 T.2.2 xh xl with hLdef
  have hT1 : 1309 / 1000 ≤ value T.1.toBits ∧ value T.1.toBits ≤ 85 := by
    have h1 := abs_le.mp hLe
    have hT1a : |value T.1.toBits| ≤ 86 := by
      by_contra hc
      push Not at hc
      have : |value L.1.toBits| ≤ |value T.1.toBits| / 2 ^ 49 := by
        have : (1 : ℝ) / 2 ^ 48 ≤ |value T.1.toBits| / 2 ^ 50 := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
        linarith [(by ring : |value T.1.toBits| / 2 ^ 49 = |value T.1.toBits| / 2 ^ 50 +
          |value T.1.toBits| / 2 ^ 50)]
      have : |value L.2.toBits| ≤ |value T.1.toBits| / 2 ^ 49 := by
        have : (1 : ℝ) / 2 ^ 97 ≤ |value T.1.toBits| / 2 ^ 99 := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
        have : |value T.1.toBits| / 2 ^ 99 ≤ |value T.1.toBits| / 2 ^ 50 :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
        linarith [(by ring : |value T.1.toBits| / 2 ^ 49 = |value T.1.toBits| / 2 ^ 50 +
          |value T.1.toBits| / 2 ^ 50)]
      have h3 := abs_sub_abs_le_abs_sub (value T.1.toBits)
        (value T.1.toBits + value L.1.toBits + value L.2.toBits -
          Real.log (value xh.toBits + value xl.toBits))
      rw [show value T.1.toBits - (value T.1.toBits + value L.1.toBits + value L.2.toBits -
        Real.log (value xh.toBits + value xl.toBits)) = Real.log (value xh.toBits + value xl.toBits) -
          value L.1.toBits - value L.2.toBits by ring] at h3
      have h4 := abs_sub (Real.log (value xh.toBits + value xl.toBits) - value L.1.toBits)
        (value L.2.toBits)
      have h5 := abs_sub (Real.log (value xh.toBits + value xl.toBits)) (value L.1.toBits)
      rw [abs_of_pos (show (0 : ℝ) < Real.log (value xh.toBits + value xl.toBits) by
        linarith [hlogX.1])] at h5
      have : |value T.1.toBits| / 2 ^ 49 ≤ |value T.1.toBits| / 4 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith [hlogX.2, (by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 140 ≤ 1)]
    have hL1' : |value L.1.toBits| ≤ 1 / 2 ^ 40 := by
      have : |value T.1.toBits| / 2 ^ 50 ≤ 86 / 2 ^ 50 := div_le_div_of_nonneg_right hT1a (by norm_num)
      linarith [(by norm_num : (86 : ℝ) / 2 ^ 50 + 1 / 2 ^ 48 ≤ 1 / 2 ^ 40)]
    have hL2' : |value L.2.toBits| ≤ 1 / 2 ^ 90 := by
      have : |value T.1.toBits| / 2 ^ 99 ≤ 86 / 2 ^ 99 := div_le_div_of_nonneg_right hT1a (by norm_num)
      linarith [(by norm_num : (86 : ℝ) / 2 ^ 99 + 1 / 2 ^ 97 ≤ 1 / 2 ^ 90)]
    have h6 := abs_le.mp hL1'
    have h7 := abs_le.mp hL2'
    constructor <;> linarith [hlogX.1, hlogX.2,
      (by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 140 + 1 / 2 ^ 40 + 1 / 2 ^ 90 ≤ 1 / 1000)]
  -- the product
  have hW1 : 3 ≤ value w1.toBits := by linarith
  obtain ⟨p1f, p2f, p3f, hpe, hp1, hp2, hp3⟩ := LgammaAsymProd.prod_spec hF T.1 L.1 L.2 w1 w2 t0f Lf1 Lf2
    hw1f hw2f (by linarith [hT1.1]) (by linarith [hT1.2]) hL1 hL2 (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 120 ≤ 2 ^ 801)]) hw2
  set Pr := LgammaAsymProd.prodCode T.1 L.1 L.2 w1 w2 with hPrdef
  -- the series
  set R := 1 / value xh.toBits with hRdef
  have hR : 1 / 2 ^ 120 ≤ R := by
    rw [hRdef, div_le_div_iff₀ (by norm_num) hx0]; linarith
  obtain ⟨g1f, g2f, hge, hg1, hg2⟩ := LgammaAsymSeries.series_gen hF o N P Xq Xh Xl Rm lo hi Lp
    C Cl E Λ K hok hval hlip hE0 hΛ0 hP hN1 hon hXh hXl hX hRm1 hEn hΛn hhi hlo hLp (o' + 2) n' ho2 hn
    (1.0 / xh) ((Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)) zf zlf R
    (1 / (value xh.toBits + value xl.toBits)) hR hRm hz1 hz2 hz3
  set zh := 1.0 / xh with hzhdef
  set zl := (Fma.fma zh (-xh) 1.0 - xl * zh) * zh with hzldef
  set W := mulDD zh zl zh zl with hWdef
  set F := Lgamma.polyDD Lgamma.asymTable (o' + 2) n' W.1 W.2 0.0 with hFdef
  set G := mulDD zh zl F.1 F.2 with hGdef
  -- the constant
  have hch : entry Lgamma.asymTable o' = Float.ofBits Lgamma.asymTable[o]! := by
    unfold entry; rw [ho]
  have hcl : entry Lgamma.asymTable (o' + 1) = Float.ofBits Lgamma.asymTable[o + 1]! := by
    unfold entry; rw [ho1]
  have chf : Finite (entry Lgamma.asymTable o').toBits := by
    rw [hch]; exact TgammaWords.ofBits_finite _ hc1
  have clf : Finite (entry Lgamma.asymTable (o' + 1)).toBits := by
    rw [hcl]; exact TgammaWords.ofBits_finite _ hc2
  have chv : value (entry Lgamma.asymTable o').toBits =
      ((PolyBound.ratOfWord Lgamma.asymTable[o]! : ℚ) : ℝ) := by
    rw [hch]; exact TgammaWords.ofBits_value _ hc1
  have clv : value (entry Lgamma.asymTable (o' + 1)).toBits =
      ((PolyBound.ratOfWord Lgamma.asymTable[o + 1]! : ℚ) : ℝ) := by
    rw [hcl]; exact TgammaWords.ofBits_value _ hc2
  -- the last operations
  have hRle : R ≤ 4 / 15 := by
    rw [hRdef, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hP1lo : 3 / 10 * value w1.toBits ≤ value Pr.1.toBits := by
    have h1 := (abs_le.mp hp1).1
    have h2 : 309 / 1000 * value w1.toBits ≤ (value T.1.toBits - 1) * value w1.toBits :=
      mul_le_mul_of_nonneg_right (by linarith [hT1.1]) (by linarith)
    have h3 : 560 * value w1.toBits / 2 ^ 53 ≤ 9 / 1000 * value w1.toBits := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hP1hi : value Pr.1.toBits ≤ 561 * value w1.toBits := by
    have h1 := (abs_le.mp hp1).2
    have h2 : (value T.1.toBits - 1) * value w1.toBits ≤ 84 * value w1.toBits :=
      mul_le_mul_of_nonneg_right (by linarith [hT1.2]) (by linarith)
    have h3 : 560 * value w1.toBits / 2 ^ 53 ≤ value w1.toBits := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hG1b : |value G.1.toBits| ≤ 1 / 2 ^ 4 := by
    have h1 : R / 7 ≤ 4 / 15 / 7 := div_le_div_of_nonneg_right hRle (by norm_num)
    linarith [(by norm_num : (4 : ℝ) / 15 / 7 ≤ 1 / 2 ^ 4)]
  have hG2b : |value G.2.toBits| ≤ 1 / 2 ^ 50 := by
    have hR1 : R ≤ 1 := by linarith
    have h1 : R / 2 ^ 50 ≤ 1 / 2 ^ 50 := div_le_div_of_nonneg_right hR1 (by norm_num)
    linarith
  have hw801 : value w1.toBits ≤ 2 ^ 801 := by
    linarith [(by norm_num : (2 : ℝ) ^ 120 ≤ 2 ^ 801)]
  obtain ⟨a1f, b1f, b2f, hte, hA0, hB1, hB2⟩ := tail_spec Pr.1 Pr.2.1 Pr.2.2
    (entry Lgamma.asymTable o') (entry Lgamma.asymTable (o' + 1)) G.1 G.2 p1f p2f p3f chf clf g1f g2f
    (value w1.toBits) hW1 hw801 hP1lo hP1hi hp2 hp3
    (by rw [chv]; exact hcv1) (by rw [clv]; exact hcv2) hG1b hG2b
  -- the result in the names of `r`
  have hr1 : Finite r.1.toBits := a1f
  have hr2 : Finite r.2.1.toBits := b1f
  have hr3 : Finite r.2.2.toBits := b2f
  have hrA : 0 < value r.1.toBits := hA0
  have hrB1 : |value r.2.1.toBits| ≤ value r.1.toBits / 2 ^ 45 := hB1
  have hrB2 : |value r.2.2.toBits| ≤ value r.1.toBits / 2 ^ 96 := hB2
  have hre : |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
      (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
        (value (entry Lgamma.asymTable o').toBits + value (entry Lgamma.asymTable (o' + 1)).toBits) +
        (value G.1.toBits + value G.2.toBits))| ≤ value w1.toBits / 2 ^ 120 + 1 / 2 ^ 98 := hte
  refine ⟨hr1, hr2, hr3, ?_, hrA, hrB1, hrB2⟩
  -- the mathematics
  set X := value xh.toBits + value xl.toBits with hXdef
  set Ls := value T.1.toBits + value L.1.toBits + value L.2.toBits with hLsdef
  set Wv := value w1.toBits + value w2.toBits with hWvdef
  have hc : value (entry Lgamma.asymTable o').toBits + value (entry Lgamma.asymTable (o' + 1)).toBits =
      ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ) := by
    rw [chv, clv]; push_cast; rfl
  have hZ : (1 / X) ^ 2 = 1 / X ^ 2 := by rw [one_div_pow]
  rw [hZ] at hge
  unfold LgammaApprox.asymAcc
  set Pz := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) (1 / X ^ 2) with hPz
  set cq := ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ)
    with hcq
  have hid : value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
      ((X - 1 / 2) * (Real.log X - 1) + cq + 1 / X * Pz) =
      (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
          (value (entry Lgamma.asymTable o').toBits + value (entry Lgamma.asymTable (o' + 1)).toBits) +
          (value G.1.toBits + value G.2.toBits))) +
      (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits - (Ls - 1) * Wv) +
      (Ls - Real.log X) * Wv + (Real.log X - 1) * (Wv - (X - 1 / 2)) +
      (value (entry Lgamma.asymTable o').toBits + value (entry Lgamma.asymTable (o' + 1)).toBits - cq) +
      (value G.1.toBits + value G.2.toBits - 1 / X * Pz) := by ring
  rw [hid, hc, sub_self, add_zero]
  have hvxX : value xh.toBits ≤ X * (1 + 1 / 2 ^ 50) := by nlinarith
  have hWv : |Wv| ≤ X * (1 + 1 / 2 ^ 100) := by
    have := abs_le.mp hw
    have h1 : value xh.toBits / 2 ^ 103 ≤ X * (1 + 1 / 2 ^ 50) / 2 ^ 103 :=
      div_le_div_of_nonneg_right hvxX (by norm_num)
    have h2 : X * (1 + 1 / 2 ^ 50) / 2 ^ 103 ≤ X * (1 / 2 ^ 100) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [abs_le]; constructor <;> nlinarith
  have e3 : |(Ls - Real.log X) * Wv| ≤ (1 / 2 ^ 88 + 1 / 2 ^ 140) * (X * (1 + 1 / 2 ^ 100)) := by
    rw [abs_mul]; exact mul_le_mul hLe hWv (abs_nonneg _) (by norm_num)
  have e4 : |(Real.log X - 1) * (Wv - (X - 1 / 2))| ≤ 83 * (value xh.toBits / 2 ^ 103) := by
    rw [abs_mul]
    apply mul_le_mul _ hw (abs_nonneg _) (by norm_num)
    rw [abs_le]; constructor <;> linarith [hlogX.1, hlogX.2]
  have e6 : |value G.1.toBits + value G.2.toBits - 1 / X * Pz| ≤ 1 / 2 ^ 99 := by
    have := hge
    have : R / 2 ^ 99 ≤ 1 / 2 ^ 99 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have a1 := abs_add_le
    ((value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
          ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ) +
          (value G.1.toBits + value G.2.toBits))) +
      (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits - (Ls - 1) * Wv) +
      (Ls - Real.log X) * Wv + (Real.log X - 1) * (Wv - (X - 1 / 2)))
    (value G.1.toBits + value G.2.toBits - 1 / X * Pz)
  have a2 := abs_add_le
    ((value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
          ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ) +
          (value G.1.toBits + value G.2.toBits))) +
      (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits - (Ls - 1) * Wv) +
      (Ls - Real.log X) * Wv) ((Real.log X - 1) * (Wv - (X - 1 / 2)))
  have a3 := abs_add_le
    ((value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
          ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ) +
          (value G.1.toBits + value G.2.toBits))) +
      (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits - (Ls - 1) * Wv))
    ((Ls - Real.log X) * Wv)
  have a4 := abs_add_le
    (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits -
        (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits +
          ((LgammaApprox.q Lgamma.asymTable o + LgammaApprox.q Lgamma.asymTable (o + 1) : ℚ) : ℝ) +
          (value G.1.toBits + value G.2.toBits)))
    (value Pr.1.toBits + value Pr.2.1.toBits + value Pr.2.2.toBits - (Ls - 1) * Wv)
  rw [hc] at hre
  have tot : value w1.toBits / 2 ^ 120 + 1 / 2 ^ 98 + value w1.toBits / 2 ^ 92 +
      (1 / 2 ^ 88 + 1 / 2 ^ 140) * (X * (1 + 1 / 2 ^ 100)) + 83 * (value xh.toBits / 2 ^ 103) +
        1 / 2 ^ 99 ≤ X * (1 / 2 ^ 88 + 1 / 2 ^ 91) := by
    have h1 : value w1.toBits / 2 ^ 120 + value w1.toBits / 2 ^ 92 + 83 * (value xh.toBits / 2 ^ 103) ≤
        value xh.toBits * (1 / 2 ^ 120 + 1 / 2 ^ 92 + 83 / 2 ^ 103) := by
      have : value w1.toBits / 2 ^ 120 ≤ value xh.toBits / 2 ^ 120 :=
        div_le_div_of_nonneg_right hw1hi (by norm_num)
      have : value w1.toBits / 2 ^ 92 ≤ value xh.toBits / 2 ^ 92 :=
        div_le_div_of_nonneg_right hw1hi (by norm_num)
      linarith [(by ring : value xh.toBits * (1 / 2 ^ 120 + 1 / 2 ^ 92 + 83 / 2 ^ 103) =
        value xh.toBits / 2 ^ 120 + value xh.toBits / 2 ^ 92 + 83 * (value xh.toBits / 2 ^ 103))]
    have h2 := mul_le_mul_of_nonneg_right hvxX (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 120 + 1 / 2 ^ 92 +
      83 / 2 ^ 103)
    have h3 : (1 : ℝ) / 2 ^ 98 + 1 / 2 ^ 99 ≤ X * (1 / 2 ^ 99) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left (by norm_num : (1 + 1 / 2 ^ 50 : ℝ) * (1 / 2 ^ 120 +
      1 / 2 ^ 92 + 83 / 2 ^ 103) + (1 / 2 ^ 88 + 1 / 2 ^ 140) * (1 + 1 / 2 ^ 100) - 1 / 2 ^ 88 +
        1 / 2 ^ 99 ≤ 1 / 2 ^ 91) hX0.le
    nlinarith
  linarith


#print axioms asym_eq
#print axioms big_test
#print axioms tail_spec
#print axioms asym_gen

end Verified.Examples.LgammaAsymAcc
