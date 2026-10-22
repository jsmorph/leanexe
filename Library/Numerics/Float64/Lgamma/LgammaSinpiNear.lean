import Library.Numerics.Float64.Tgamma.TgammaSinpidLow

/-!
The branch of `Lgamma.asSinpipid` within `3/256` of an integer, where `sin (π z)/π` for
`z = 1/2 - |x - 1/2|` is the polynomial `z + z³ P (z²)` with `P (u) = (c138 + c139) + u (c140 +
u (c141 + u c142))`.  The code evaluates `u` as the double-double `z2 + z2l` with
`z2l = fma (z, z, -z2)`, the tail `u (c140 + u (c141 + u c142))` in double arithmetic, the sum with
`c138` exactly, the products with `u` and `z` in double-double arithmetic, and the sum with `z`
exactly.  `near_spec` bounds the result within `z/2^74` of `z + z³ P (z²)`, with the low part at
most `2^-50` of the high part, for `2^-53 ≤ z ≤ 3/256` and the coefficient bounds of the table.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinpiNear
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaMul Library.Numerics.Float64.Tgamma.TgammaSinpidLow

set_option exponentiation.threshold 4096

/-- The code of the branch. -/
def nearTail (z c138 c139 c140 c141 c142 : Float) : Float × Float :=
  let z2 := z * z
  let z2l := Library.Numerics.Arithmetic.Fma.fma z z (-z2)
  let fl := z2 * (c140 + z2 * (c141 + z2 * c142))
  let A := fastTwoSum c138 fl
  let B := mulDD z2 z2l A.1 (A.2 + c139)
  let C := mulDDD z B.1 B.2
  let D := fastTwoSum z C.1
  (D.1, C.2 + D.2)

set_option maxHeartbeats 2000000 in
/-- **The branch near the integers.** -/
theorem near_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (z c138 c139 c140 c141 c142 : Float)
    (hz : Finite z.toBits) (hz0 : 1 / 2 ^ 53 ≤ value z.toBits) (hz1 : value z.toBits ≤ 3 / 256)
    (h138 : Finite c138.toBits) (h139 : Finite c139.toBits) (h140 : Finite c140.toBits)
    (h141 : Finite c141.toBits) (h142 : Finite c142.toBits)
    (b138 : 1644 / 1000 ≤ -value c138.toBits ∧ -value c138.toBits ≤ 1645 / 1000)
    (b139 : |value c139.toBits| ≤ 1 / 2 ^ 54) (b140 : |value c140.toBits| ≤ 82 / 100)
    (b141 : |value c141.toBits| ≤ 20 / 100) (b142 : |value c142.toBits| ≤ 3 / 100) :
    let R := nearTail z c138 c139 c140 c141 c142
    Finite R.1.toBits ∧ Finite R.2.toBits ∧
      |value R.1.toBits + value R.2.toBits - (value z.toBits + value z.toBits ^ 3 *
        ((value c138.toBits + value c139.toBits) + value z.toBits ^ 2 * (value c140.toBits +
          value z.toBits ^ 2 * (value c141.toBits + value z.toBits ^ 2 * value c142.toBits))))| ≤
        value z.toBits / 2 ^ 74 ∧
      |value R.2.toBits| ≤ |value R.1.toBits| / 2 ^ 50 := by
  intro R
  obtain ⟨Z, hZd⟩ : ∃ v, v = value z.toBits := ⟨_, rfl⟩
  rw [← hZd] at hz0 hz1 ⊢
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hz0
  have hZa : |value z.toBits| = Z := by rw [← hZd, abs_of_pos hZ0]
  have hU : Z ^ 2 ≤ 9 / 65536 := by nlinarith
  have hU0 : 0 ≤ Z ^ 2 := sq_nonneg Z
  have hUa : |Z ^ 2| ≤ 9 / 65536 := by rw [abs_of_nonneg hU0]; exact hU
  -- `z2 = z z`
  have hz2 := fapprox_mul (fapprox_self z hz) (fapprox_self z hz) Z Z (le_of_eq hZa) (le_of_eq hZa)
    (Z * Z) (by simp) (by nlinarith)
  rw [← hZd, ← sq] at hz2
  have hz2' : FApprox (z * z) (Z ^ 2) (Z ^ 2 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    hz2.mono (le_of_eq (by ring))
  have hz2c : FApprox (z * z) (Z ^ 2) (9 / 65536 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    hz2'.mono (by linarith [div_le_div_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 2 ^ 53)])
  obtain ⟨v2, hv2⟩ : ∃ v, v = value (z * z).toBits := ⟨_, rfl⟩
  have he2 : |v2 - Z ^ 2| ≤ Z ^ 2 / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [hv2]; exact hz2'.2
  -- `z2l = fma (z, z, -z2)`
  have hna := fapprox_neg (fapprox_self (z * z) hz2.1)
  have hnav : value (-(z * z)).toBits = -v2 := by
    have h0 := abs_nonpos_iff.mp hna.2; rw [hv2]; linarith
  have hfm := fma_approx hF z z (-(z * z)) hz hz hna.1 (by
    rw [hnav, ← hZd, ← sq, ← sub_eq_add_neg, abs_sub_comm]
    linarith [(by norm_num : (9 / 65536 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
      div_le_div_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 2 ^ 53)])
  rw [hnav, ← hZd, ← sq, ← sub_eq_add_neg] at hfm
  obtain ⟨vl, hvl⟩ : ∃ v, v = value (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z))).toBits := ⟨_, rfl⟩
  have hel : |vl - (Z ^ 2 - v2)| ≤ |Z ^ 2 - v2| / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [hvl]; exact hfm.2
  have he2' : |Z ^ 2 - v2| ≤ 9 / 65536 / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_sub_comm]
    linarith [div_le_div_of_nonneg_right hU (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  have hδu : |v2 + vl - Z ^ 2| ≤ 1 / 2 ^ 118 := by
    have : v2 + vl - Z ^ 2 = vl - (Z ^ 2 - v2) := by ring
    rw [this]
    linarith [(by norm_num : ((9 / 65536 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 118), div_le_div_of_nonneg_right he2' (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  have hvlb : |vl| ≤ 1 / 2 ^ 65 := by
    have := abs_sub_abs_le_abs_sub vl (Z ^ 2 - v2)
    linarith [(by norm_num : ((9 / 65536 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ 1 / 2 ^ 65), div_le_div_of_nonneg_right he2' (by positivity : (0 : ℝ) ≤ 2 ^ 53)]
  have hv2b : |v2| ≤ 1374 / 10 ^ 7 := by
    have := abs_sub_abs_le_abs_sub v2 (Z ^ 2)
    rw [abs_of_nonneg hU0] at this
    linarith [(by norm_num : (9 / 65536 : ℝ) + (9 / 65536 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 1374 / 10 ^ 7)]
  -- `fl = z2 (c140 + z2 (c141 + z2 c142))`
  have ha1 := (fapprox_mul hz2c (fapprox_self c142 h142) (9 / 65536) (3 / 100) hUa b142
    (42 / 10 ^ 7) (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 69 : ℝ) by norm_num)
  have hb1 : |value c141.toBits + Z ^ 2 * value c142.toBits| ≤ 2001 / 10000 := by
    have h1 := abs_add_le (value c141.toBits) (Z ^ 2 * value c142.toBits)
    have h2 : |Z ^ 2 * value c142.toBits| ≤ 9 / 65536 * (3 / 100) := by
      rw [abs_mul]; exact mul_le_mul hUa b142 (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (20 / 100 : ℝ) + 9 / 65536 * (3 / 100) ≤ 2001 / 10000)]
  have ha2 := (fapprox_add (fapprox_self c141 h141) ha1 (2002 / 10000) (by
    linarith [(by norm_num : (2001 / 10000 : ℝ) + (0 + 1 / 2 ^ 69) ≤ 2002 / 10000)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 55 : ℝ) by norm_num)
  have ha3 := (fapprox_mul hz2c ha2 (9 / 65536) (2001 / 10000) hUa hb1 (275 / 10 ^ 7)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 66 : ℝ) by norm_num)
  have hb3 : |value c140.toBits + Z ^ 2 * (value c141.toBits + Z ^ 2 * value c142.toBits)| ≤
      8201 / 10000 := by
    have h1 := abs_add_le (value c140.toBits) (Z ^ 2 * (value c141.toBits + Z ^ 2 * value c142.toBits))
    have h2 : |Z ^ 2 * (value c141.toBits + Z ^ 2 * value c142.toBits)| ≤ 9 / 65536 * (2001 / 10000) := by
      rw [abs_mul]; exact mul_le_mul hUa hb1 (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (82 / 100 : ℝ) + 9 / 65536 * (2001 / 10000) ≤ 8201 / 10000)]
  have ha4 := (fapprox_add (fapprox_self c140 h140) ha3 (8202 / 10000) (by
    linarith [(by norm_num : (8201 / 10000 : ℝ) + (0 + 1 / 2 ^ 66) ≤ 8202 / 10000)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 53 : ℝ) by norm_num)
  have hfl := (fapprox_mul hz2c ha4 (9 / 65536) (8201 / 10000) hUa hb3 (1127 / 10 ^ 7)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 64 : ℝ) by norm_num)
  obtain ⟨T, hT⟩ : ∃ v, v = Z ^ 2 * (value c140.toBits + Z ^ 2 * (value c141.toBits +
      Z ^ 2 * value c142.toBits)) := ⟨_, rfl⟩
  rw [← hT] at hfl
  have hTb : |T| ≤ 1127 / 10 ^ 7 := by
    rw [hT, abs_mul]
    linarith [mul_le_mul hUa hb3 (abs_nonneg _) (by norm_num),
      (by norm_num : (9 / 65536 : ℝ) * (8201 / 10000) ≤ 1127 / 10 ^ 7)]
  -- `A = c138 + fl`
  obtain ⟨vf, hvf⟩ : ∃ v, v = value (z * z * (c140 + z * z * (c141 + z * z * c142))).toBits :=
    ⟨_, rfl⟩
  have hfl2 : |vf - T| ≤ 1 / 2 ^ 64 := by rw [hvf]; exact hfl.2
  have hfb : |vf| ≤ 1128 / 10 ^ 7 := by
    have := abs_sub_abs_le_abs_sub vf T
    linarith [(by norm_num : (1127 / 10 ^ 7 : ℝ) + 1 / 2 ^ 64 ≤ 1128 / 10 ^ 7)]
  have h138a : |value c138.toBits| = -value c138.toBits := abs_of_neg (by linarith [b138.1])
  obtain ⟨hA1f, hA2f, hAsum, hA2q, hA2⟩ := fastTwoSum_spec c138 _ h138 hfl.1
    (by rw [h138a, ← hvf]; linarith [b138.1])
    (by rw [h138a]; linarith [b138.2, (by norm_num : (1645 / 1000 : ℝ) < 2 ^ 900)])
  rw [← hvf] at hAsum hA2q
  obtain ⟨vA1, hvA1⟩ : ∃ v, v = value (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1.toBits := ⟨_, rfl⟩
  obtain ⟨vA2, hvA2⟩ : ∃ v, v = value (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2.toBits := ⟨_, rfl⟩
  rw [← hvA1, ← hvA2] at hAsum hA2
  rw [← hvA2] at hA2q
  have hA1b : |vA1| ≤ 1646 / 1000 := by
    have : vA1 = value c138.toBits + vf - vA2 := by linarith
    rw [this]
    have h1 := abs_sub (value c138.toBits + vf) vA2
    have h2 := abs_add_le (value c138.toBits) vf
    rw [h138a] at h2
    linarith [b138.2, (by norm_num : (1645 / 1000 : ℝ) + 2 * (1128 / 10 ^ 7) ≤ 1646 / 1000)]
  have hA2b : |vA2| ≤ 1 / 2 ^ 51 := by
    linarith [(by norm_num : (1646 / 1000 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 51)]
  -- `fl' = A.2 + c139`
  have hfl' := (fapprox_add (fapprox_self _ hA2f) (fapprox_self c139 h139) (1 / 2 ^ 50) (by
    rw [← hvA2]
    have := abs_add_le vA2 (value c139.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 54 + (0 + 0) ≤ 1 / 2 ^ 50)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 103 : ℝ) by norm_num)
  rw [← hvA2] at hfl'
  obtain ⟨vF, hvF⟩ : ∃ v, v = value ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139).toBits := ⟨_, rfl⟩
  have hF2 : |vF - (vA2 + value c139.toBits)| ≤ 1 / 2 ^ 103 := by rw [hvF]; exact hfl'.2
  have hFb : |vF| ≤ 1 / 2 ^ 49 := by
    have h1 := abs_sub_abs_le_abs_sub vF (vA2 + value c139.toBits)
    have h2 := abs_add_le vA2 (value c139.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 54 + 1 / 2 ^ 103 ≤ 1 / 2 ^ 49)]
  -- `B = (z2 + z2l) (A.1 + fl')`
  obtain ⟨hB1f, hB2f, heB, hlB, hhB⟩ := mulDD_spec hF (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    _ _ hz2.1 hfm.1 hA1f hfl'.1
    (1646 / 1000 * (1374 / 10 ^ 7)) (1646 / 1000 * (1 / 2 ^ 65)) (1 / 2 ^ 49 * (1374 / 10 ^ 7))
    (1 / 2 ^ 49 * (1 / 2 ^ 65))
    (by rw [← hvA1, ← hv2]; exact mul_le_mul hA1b hv2b (abs_nonneg _) (by norm_num))
    (by rw [← hvA1, ← hvl]; exact mul_le_mul hA1b hvlb (abs_nonneg _) (by norm_num))
    (by rw [← hvF, ← hv2]; exact mul_le_mul hFb hv2b (abs_nonneg _) (by norm_num))
    (by rw [← hvF, ← hvl]; exact mul_le_mul hFb hvlb (abs_nonneg _) (by norm_num))
    (by norm_num) (by norm_num)
  rw [← hv2, ← hvl, ← hvA1, ← hvF] at heB
  obtain ⟨vB1, hvB1⟩ : ∃ v, v = value (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).1.toBits :=
    ⟨_, rfl⟩
  obtain ⟨vB2, hvB2⟩ : ∃ v, v = value (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).2.toBits :=
    ⟨_, rfl⟩
  rw [← hvB1, ← hvB2] at heB
  rw [← hvB2] at hlB
  rw [← hvB1] at hhB
  have hB1b : |vB1| ≤ 2263 / 10 ^ 7 := by
    linarith [(by norm_num : (1646 / 1000 * (1374 / 10 ^ 7) : ℝ) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      2263 / 10 ^ 7)]
  have hB2b : |vB2| ≤ 1 / 2 ^ 61 := by
    linarith [(by norm_num : ((1646 / 1000 * (1 / 2 ^ 65) + 1 / 2 ^ 49 * (1374 / 10 ^ 7)) : ℝ) *
      (1 + 1 / 2 ^ 50) + 1646 / 1000 * (1374 / 10 ^ 7) / 2 ^ 52 + 1 / 2 ^ 1070 ≤ 1 / 2 ^ 61)]
  -- `B` against `Z² NP`
  obtain ⟨NP, hNP⟩ : ∃ v, v = value c138.toBits + value c139.toBits + T := ⟨_, rfl⟩
  have hNPb : |NP| ≤ 1646 / 1000 := by
    rw [hNP]
    have h1 := abs_add_le (value c138.toBits + value c139.toBits) T
    have h2 := abs_add_le (value c138.toBits) (value c139.toBits)
    rw [h138a] at h2
    linarith [b138.2, (by norm_num : (1645 / 1000 : ℝ) + 1 / 2 ^ 54 + 1127 / 10 ^ 7 ≤ 1646 / 1000)]
  have hεA : |vA1 + vF - NP| ≤ 1 / 2 ^ 64 + 1 / 2 ^ 103 := by
    have : vA1 + vF - NP = (vf - T) + (vF - (vA2 + value c139.toBits)) := by rw [hNP]; linarith
    rw [this]
    have := abs_add_le (vf - T) (vF - (vA2 + value c139.toBits))
    linarith
  have hu2 : |v2 + vl| ≤ 13741 / 10 ^ 8 := by
    have := abs_add_le v2 vl
    linarith [(by norm_num : (1374 / 10 ^ 7 : ℝ) + 1 / 2 ^ 65 ≤ 13741 / 10 ^ 8)]
  have hEB : |vB1 + vB2 - Z ^ 2 * NP| ≤ 13741 / 10 ^ 8 * (1 / 2 ^ 64 + 1 / 2 ^ 103) +
      1646 / 1000 * (1 / 2 ^ 118) + 1 / 2 ^ 105 := by
    have h1 : (v2 + vl) * (vA1 + vF) - Z ^ 2 * NP =
        (v2 + vl) * (vA1 + vF - NP) + NP * (v2 + vl - Z ^ 2) := by ring
    have h2 : |(v2 + vl) * (vA1 + vF) - Z ^ 2 * NP| ≤
        13741 / 10 ^ 8 * (1 / 2 ^ 64 + 1 / 2 ^ 103) + 1646 / 1000 * (1 / 2 ^ 118) := by
      rw [h1]
      have h3 := abs_add_le ((v2 + vl) * (vA1 + vF - NP)) (NP * (v2 + vl - Z ^ 2))
      rw [abs_mul, abs_mul] at h3
      have h4 := mul_le_mul hu2 hεA (abs_nonneg _) (by norm_num)
      have h5 := mul_le_mul hNPb hδu (abs_nonneg _) (by norm_num)
      linarith
    have h3 := abs_add_le (vB1 + vB2 - (v2 + vl) * (vA1 + vF)) ((v2 + vl) * (vA1 + vF) - Z ^ 2 * NP)
    rw [show vB1 + vB2 - (v2 + vl) * (vA1 + vF) + ((v2 + vl) * (vA1 + vF) - Z ^ 2 * NP) =
      vB1 + vB2 - Z ^ 2 * NP by ring] at h3
    linarith [(by norm_num : (1 / 2 ^ 49 * (1 / 2 ^ 65) : ℝ) + (4 * (1646 / 1000 * (1 / 2 ^ 65) +
      1 / 2 ^ 49 * (1374 / 10 ^ 7)) + 1646 / 1000 * (1374 / 10 ^ 7) / 2 ^ 51) / 2 ^ 53 +
      1 / 2 ^ 1070 ≤ 1 / 2 ^ 105)]
  -- `C = z B`
  obtain ⟨hC1f, hC2f, heC, hlC, hhC⟩ := mulDDD_spec hF z _ _ hz hB1f hB2f (Z * (2263 / 10 ^ 7))
    (Z * (1 / 2 ^ 61))
    (by rw [← hvB1, hZa, mul_comm Z]; exact mul_le_mul_of_nonneg_right hB1b hZ0.le)
    (by rw [← hvB2, hZa, mul_comm Z]; exact mul_le_mul_of_nonneg_right hB2b hZ0.le)
    (by nlinarith) (by nlinarith)
  rw [← hZd, ← hvB1, ← hvB2] at heC
  obtain ⟨vC1, hvC1⟩ : ∃ v, v = value (mulDDD z (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).1
    (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).2).1.toBits :=
    ⟨_, rfl⟩
  obtain ⟨vC2, hvC2⟩ : ∃ v, v = value (mulDDD z (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).1
    (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).2).2.toBits :=
    ⟨_, rfl⟩
  rw [← hvC1, ← hvC2] at heC
  rw [← hvC2] at hlC
  rw [← hvC1] at hhC
  -- `D = z + C.1`
  have hC1z : |vC1| ≤ |value z.toBits| := by
    rw [hZa]
    have : Z * (2263 / 10 ^ 7) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ Z := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 * (1 / 2 ^ 53))]
    linarith
  obtain ⟨hD1f, hD2f, hDsum, -, -⟩ := fastTwoSum_spec z _ hz hC1f (by rw [← hvC1]; exact hC1z)
    (by rw [hZa]; linarith [(by norm_num : (3 / 256 : ℝ) < 2 ^ 900)])
  have hDt := fts_low z _ hz hC1f (by
    have := abs_add_le (value z.toBits) vC1
    rw [hZa] at this; rw [← hvC1]
    linarith [(by norm_num : (2 * (3 / 256) : ℝ) < 2 ^ 1023)]) hDsum
  rw [← hZd, ← hvC1] at hDsum
  obtain ⟨vD1, hvD1⟩ : ∃ v, v = value (fastTwoSum z (mulDDD z (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).1
    (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).2).1).1.toBits :=
    ⟨_, rfl⟩
  obtain ⟨vD2, hvD2⟩ : ∃ v, v = value (fastTwoSum z (mulDDD z (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).1
    (mulDD (z * z) (Library.Numerics.Arithmetic.Fma.fma z z (-(z * z)))
    (fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).1
    ((fastTwoSum c138 (z * z * (c140 + z * z * (c141 + z * z * c142)))).2 + c139)).2).1).2.toBits :=
    ⟨_, rfl⟩
  rw [← hvD1, ← hvD2] at hDsum hDt
  -- the last sum
  have hw := fapprox_add (fapprox_self _ hC2f) (fapprox_self _ hD2f) (|vC2| + |vD2|)
    (by rw [← hvC2, ← hvD2]; simp only [add_zero]; exact abs_add_le _ _) (by
      have : |vD1| ≤ 2 := by
        have h1 := abs_sub_abs_le_abs_sub vD1 (Z + vC1)
        have : vD1 - (Z + vC1) = -vD2 := by linarith
        rw [this, abs_neg] at h1
        have h2 := abs_add_le Z vC1
        rw [abs_of_pos hZ0] at h2
        nlinarith
      nlinarith)
  rw [← hvC2, ← hvD2] at hw
  have hR1 : value R.1.toBits = vD1 := by rw [hvD1]; rfl
  have hw' : FApprox R.2 (vC2 + vD2) _ := hw
  refine ⟨hD1f, hw'.1, ?_, ?_⟩
  · rw [hR1]
    obtain ⟨vR2, hvR2⟩ : ∃ v, v = value R.2.toBits := ⟨_, rfl⟩
    have hw2 : |vR2 - (vC2 + vD2)| ≤ 0 + 0 + (|vC2| + |vD2|) / 2 ^ 53 := by rw [hvR2]; exact hw'.2
    rw [← hvR2]
    have key : Z + Z ^ 3 * ((value c138.toBits + value c139.toBits) + Z ^ 2 * (value c140.toBits +
        Z ^ 2 * (value c141.toBits + Z ^ 2 * value c142.toBits))) = Z + Z * (Z ^ 2 * NP) := by
      rw [hNP, hT]; ring
    rw [key]
    have hsplit : vD1 + vR2 - (Z + Z * (Z ^ 2 * NP)) = (vR2 - (vC2 + vD2)) +
        (vC1 + vC2 - Z * (vB1 + vB2)) + Z * (vB1 + vB2 - Z ^ 2 * NP) := by linarith
    rw [hsplit]
    have t1 := abs_add_le ((vR2 - (vC2 + vD2)) + (vC1 + vC2 - Z * (vB1 + vB2)))
      (Z * (vB1 + vB2 - Z ^ 2 * NP))
    have t2 := abs_add_le (vR2 - (vC2 + vD2)) (vC1 + vC2 - Z * (vB1 + vB2))
    have t3 : |Z * (vB1 + vB2 - Z ^ 2 * NP)| = Z * |vB1 + vB2 - Z ^ 2 * NP| := by
      rw [abs_mul, abs_of_pos hZ0]
    have hZEB := mul_le_mul_of_nonneg_left hEB hZ0.le
    have hD1b : |vD1| ≤ Z * 1001 / 1000 := by
      have h1 : vD1 = Z + vC1 - vD2 := by linarith
      have h2 : |vD1| ≤ |Z + vC1| + |vD2| := by rw [h1]; exact abs_sub _ _
      have h3 := abs_add_le Z vC1
      rw [abs_of_pos hZ0] at h3
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 53)),
        (by norm_num : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 52) ≤ 1 / 2 ^ 52)]
    linarith [(by norm_num : (13741 / 10 ^ 8 * (1 / 2 ^ 64 + 1 / 2 ^ 103) + 1646 / 1000 * (1 / 2 ^ 118) +
      1 / 2 ^ 105 : ℝ) ≤ 1 / 2 ^ 75), (by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 53))]
  · rw [hR1]
    obtain ⟨vR2, hvR2⟩ : ∃ v, v = value R.2.toBits := ⟨_, rfl⟩
    have hw2 : |vR2 - (vC2 + vD2)| ≤ 0 + 0 + (|vC2| + |vD2|) / 2 ^ 53 := by rw [hvR2]; exact hw'.2
    rw [← hvR2]
    have h1 := abs_sub_abs_le_abs_sub vR2 (vC2 + vD2)
    have h2 := abs_add_le vC2 vD2
    have hD1lo : Z * 9997 / 10000 ≤ |vD1| := by
      have h6 : Z ≤ |vD1| + |vD2| + |vC1| := by
        have := le_abs_self vD1; have := le_abs_self vD2; have := neg_abs_le vC1
        linarith
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 53)),
        (by norm_num : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 52) ≤ 1 / 2 ^ 52)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 53))]

#print axioms near_spec

end Library.Numerics.Float64.Lgamma.LgammaSinpiNear
