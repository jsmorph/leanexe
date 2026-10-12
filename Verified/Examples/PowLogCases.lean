import Verified.Examples.PowLogMain

/-!
The relative error of `Pow.powLog` for one table entry.  The three cases of
`PowLogMain.core_bound` give `|y + tail - L| ≤ (7/8) 2 ^ -65 |L|` and `|tail| ≤ 2 ^ -50 |y|` for
`L = k log 2 + log z`: `k ≠ 0`, where `|L| ≥ 0.34 |k|` (`case_k`); `k = 0` with `logc ≠ 0`,
where `|r| ≤ 1.03 |L|` and `|L| ≥ 1/460` (`case_c`); and `k = 0` with `logc = 0`, where
`L = log (1 + r)` and `|r| ≥ 2 ^ -53` (`case_one`).  The three cases are lemmas on real numbers,
so that `linarith` works in a small context.
-/

namespace Verified.Examples.PowLogCases
open CodeLib.IEEE64 LeanExe.ProofKit PowLogTable

set_option exponentiation.threshold 4096

/-- From `|v1 + v2 - L| ≤ ε |L|`, `|v2| ≤ 2 u |v1| + B`, and `B ≤ ε |L|`: `|v2| ≤ |v1| / 2 ^ 50`. -/
theorem tail_real (v1 v2 L ε B : ℝ) (hε : ε ≤ 1 / 2 ^ 64)
    (hm : |v1 + v2 - L| ≤ ε * |L|) (ht : |v2| ≤ 2 / 2 ^ 53 * |v1| + B) (hB : B ≤ ε * |L|) :
    |v2| ≤ |v1| / 2 ^ 50 := by
  have hL0 := abs_nonneg L
  have h0 := abs_nonneg v1
  have h00 := abs_nonneg v2
  have h1 : |L| ≤ |v1| + |v2| + ε * |L| := by
    have := abs_sub_abs_le_abs_sub L (v1 + v2)
    rw [abs_sub_comm] at this
    have := abs_add_le v1 v2
    linarith
  have h2 : ε * |L| ≤ 1 / 2 ^ 64 * |L| := mul_le_mul_of_nonneg_right hε hL0
  have h3 : |L| ≤ 2 * (|v1| + |v2|) := by linarith
  have h4 : ε * |L| ≤ 1 / 2 ^ 64 * (2 * (|v1| + |v2|)) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  linarith

theorem cube_bound (R : ℝ) (hR : |R| ≤ 23 / 4000) : |R| ^ 3 ≤ (23 / 4000) ^ 2 * |R| := by
  have hR0 := abs_nonneg R
  have h2 : |R| ^ 2 ≤ (23 / 4000) ^ 2 := pow_le_pow_left₀ hR0 hR 2
  calc
    |R| ^ 3 = |R| ^ 2 * |R| := by ring
    _ ≤ (23 / 4000) ^ 2 * |R| := mul_le_mul_of_nonneg_right h2 hR0

theorem square_bound (R : ℝ) (hR : |R| ≤ 23 / 4000) : R ^ 2 ≤ 23 / 4000 * |R| := by
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right hR (abs_nonneg R)

/-- The bound for `k ≠ 0`, where `|L| ≥ 0.34 |k|`. -/
theorem case_k (v1 v2 L R Kr lt T μ : ℝ) (hK1 : 1 ≤ |Kr|) (hK' : |Kr| ≤ 1100)
    (hR : |R| ≤ 23 / 4000) (hltb : |lt| ≤ 1 / 2 ^ 43) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 2 ^ 1000)
    (hL : 34 / 100 * |Kr| ≤ |L|) (hTb : |T + R| ≤ 763 * |Kr|)
    (hE : |v1 + v2 - L| ≤ |Kr| / 2 ^ 91 + 1 / 2 ^ 97 + |R| * (6 / 2 ^ 70) +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
        40 * (|Kr| + 1) * μ))
    (hT : |v2| ≤ 2 / 2 ^ 53 * |v1| +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
        40 * (|Kr| + 1) * μ)) :
    |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| ∧ |v2| ≤ |v1| / 2 ^ 50 := by
  have hR0 := abs_nonneg R
  have hR3 := cube_bound R hR
  have hH : (|R| + 3 / 2 ^ 22) ^ 2 ≤ 1 / 10000 := by
    have h1 : |R| + 3 / 2 ^ 22 ≤ 1 / 100 := by
      linarith [show (3 : ℝ) / 2 ^ 22 ≤ 1 / 1000 by norm_num]
    have := pow_le_pow_left₀ (by positivity) h1 2
    linarith [show ((1 : ℝ) / 100) ^ 2 = 1 / 10000 by norm_num]
  have hKμ : (|Kr| + 1) * μ ≤ 1101 * (1 / 2 ^ 1000) :=
    mul_le_mul (by linarith) hμ1 hμ0 (by norm_num)
  have hB : 12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
      3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
      40 * (|Kr| + 1) * μ ≤ 1 / 10 / 2 ^ 65 * |L| := by
    have hlt0 := abs_nonneg lt
    linarith
  have hmain : |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| := by linarith
  exact ⟨hmain, tail_real v1 v2 L (7 / 8 / 2 ^ 65) _ (by norm_num) hmain hT
    (hB.trans (by linarith [abs_nonneg L]))⟩

/-- The bound for `k = 0` and `logc ≠ 0`, where `|L| ≥ |r|` and `|L| ≥ 1/460`. -/
theorem case_c (v1 v2 L R Kr lt T μ : ℝ) (hK0 : Kr = 0)
    (hR : |R| ≤ 23 / 4000) (hltb : |lt| ≤ 1 / 2 ^ 43) (hμ1 : μ ≤ 1 / 2 ^ 1000)
    (hL1 : |R| ≤ 103 / 100 * |L|) (hL2 : 1 / 460 ≤ |L|) (hTb : |T + R| ≤ 36 / 100)
    (hE : |v1 + v2 - L| ≤ |Kr| / 2 ^ 91 + 1 / 2 ^ 97 + |R| * (6 / 2 ^ 70) +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
        40 * (|Kr| + 1) * μ))
    (hT : |v2| ≤ 2 / 2 ^ 53 * |v1| +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
        40 * (|Kr| + 1) * μ)) :
    |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| ∧ |v2| ≤ |v1| / 2 ^ 50 := by
  have hK : |Kr| = 0 := by rw [hK0, abs_zero]
  have hKμ : |Kr| * μ = 0 := by rw [hK, zero_mul]
  have hR0 := abs_nonneg R
  have hR3 := cube_bound R hR
  have hH : (|R| + 3 / 2 ^ 22) ^ 2 ≤ 1 / 10000 := by
    have h1 : |R| + 3 / 2 ^ 22 ≤ 1 / 100 := by
      linarith [show (3 : ℝ) / 2 ^ 22 ≤ 1 / 1000 by norm_num]
    have := pow_le_pow_left₀ (by positivity) h1 2
    linarith [show ((1 : ℝ) / 100) ^ 2 = 1 / 10000 by norm_num]
  have hB : 12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22)) +
      3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + (|R| + 3 / 2 ^ 22) ^ 2) +
      40 * (|Kr| + 1) * μ ≤ 6 / 10 / 2 ^ 65 * |L| := by
    have hlt0 := abs_nonneg lt
    linarith
  have hmain : |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| := by linarith
  exact ⟨hmain, tail_real v1 v2 L (7 / 8 / 2 ^ 65) _ (by norm_num) hmain hT
    (hB.trans (by linarith [abs_nonneg L]))⟩

/-- The bound for `k = 0` and `logc = 0`, where `|L| ≥ (1 - 0.006) |r|` and `|r| ≥ 2 ^ -53`. -/
theorem case_one (v1 v2 L R Kr lt T μ : ℝ) (hK0 : Kr = 0) (hlt : lt = 0) (hT0 : T = 0)
    (hR : |R| ≤ 23 / 4000) (hμ1 : μ ≤ 1 / 2 ^ 1000)
    (hRmin : 1 / 2 ^ 53 ≤ |R|) (hLR : |R| * (1 - 1006 / 1000 * (23 / 4000)) ≤ |L|)
    (hE : |v1 + v2 - L| ≤ |Kr| / 2 ^ 91 + |R| * (6 / 2 ^ 70) +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 9 / 2 ^ 22 * |R|) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + 4 * R ^ 2) +
        40 * (|Kr| + 1) * μ))
    (hT : |v2| ≤ 2 / 2 ^ 53 * |v1| +
      (12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 9 / 2 ^ 22 * |R|) +
        3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + 4 * R ^ 2) +
        40 * (|Kr| + 1) * μ)) :
    |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| ∧ |v2| ≤ |v1| / 2 ^ 50 := by
  have hK : |Kr| = 0 := by rw [hK0, abs_zero]
  have hKμ : |Kr| * μ = 0 := by rw [hK, zero_mul]
  have hlt' : |lt| = 0 := by rw [hlt, abs_zero]
  have hTR : |T + R| = |R| := by rw [hT0, zero_add]
  have hR0 := abs_nonneg R
  have hR3 := cube_bound R hR
  have hR2 := square_bound R hR
  have hμR : μ ≤ |R| / 2 ^ 900 := by
    have : (1 : ℝ) / 2 ^ 1000 ≤ (1 / 2 ^ 53) / 2 ^ 900 := by norm_num
    have h2 : (1 / 2 ^ 53) / 2 ^ 900 ≤ |R| / 2 ^ 900 :=
      div_le_div_of_nonneg_right hRmin (by positivity)
    linarith
  have hB : 12 / 2 ^ 53 * (|Kr| / 2 ^ 44 + |lt| + 9 / 2 ^ 22 * |R|) +
      3 / 2 ^ 53 * |R| ^ 3 + 24 / 2 ^ 106 * (|T + R| + 4 * R ^ 2) +
      40 * (|Kr| + 1) * μ ≤ 8 / 10 / 2 ^ 65 * |L| := by
    linarith
  have hmain : |v1 + v2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| := by linarith
  exact ⟨hmain, tail_real v1 v2 L (7 / 8 / 2 ^ 65) _ (by norm_num) hmain hT
    (hB.trans (by linarith [abs_nonneg L]))⟩

/-- The case analysis for one entry. -/
theorem core_relative (iz kd : UInt64) (e f : Nat) (he : e = 1022 ∨ e = 1023) (hf : f < 2 ^ 52)
    (hf1023 : e = 1023 → f + 2 ^ 31 < 2 ^ 52) (hiz : iz.toNat = e * 2 ^ 52 + f)
    (i : Fin 128) (hie : e = 1022 → i.val ≤ 75) (hie' : e = 1023 → 75 ≤ i.val)
    (hzl : e = 1022 → (lowU i.val : ℝ) ≤ value iz ∧ value iz ≤ (highU i.val : ℝ))
    (hzl' : e = 1023 → (lowL i.val : ℝ) ≤ value iz ∧ value iz ≤ (highL i.val : ℝ))
    (K : Int) (hkf : Finite kd) (hkv : value kd = K) (hK : |K| ≤ 1100)
    (hx1 : ¬ (K = 0 ∧ value iz = 1)) :
    let W := PowLogEval.logWords iz kd Pow.powLogTable[4 * i.val]!
      Pow.powLogTable[4 * i.val + 2]! Pow.powLogTable[4 * i.val + 3]!
    let L := K * Real.log 2 + Real.log (value iz)
    Finite W.1 ∧ Finite W.2 ∧ |value W.1 + value W.2 - L| ≤ 7 / 8 / 2 ^ 65 * |L| ∧
      |value W.2| ≤ |value W.1| / 2 ^ 50 := by
  intro W L
  obtain ⟨hW1f, hW2f, hzpos, hR, hlcb, hltb, hlogz, hzero, hpos, hneg, hlc0, hE, hE1, hT1, hT⟩ :=
    PowLogMain.core_bound iz kd e f he hf hf1023 hiz i hie hie' hzl hzl' K hkf hkv hK
  set invc := Pow.powLogTable[4 * i.val]!
  set lc := Pow.powLogTable[4 * i.val + 2]!
  set lt := Pow.powLogTable[4 * i.val + 3]!
  set R := value iz * value invc - 1
  have hμ0 : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  have hμ1 : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon]
  have hR2 : R ^ 2 ≤ (23 / 4000) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg R) hR 2
    rwa [sq_abs] at this
  have hl1 := PowLogMain.log1p_linear R hR
  obtain ⟨-, hln2⟩ := PowLogMain.ln2_error
  refine ⟨hW1f, hW2f, ?_⟩
  by_cases hK0 : K = 0
  · have hKr : (K : ℝ) = 0 := by rw [hK0, Int.cast_zero]
    have hLz : L = Real.log (value iz) := by
      show (K : ℝ) * Real.log 2 + Real.log (value iz) = _
      rw [hKr, zero_mul, zero_add]
    by_cases hc0 : value lc = 0
    · -- entries 74 and 75: `log z = log (1 + r)`
      obtain ⟨h1, h2, h3, h4⟩ := hzero (hlc0 hc0)
      have hlz : Real.log (value iz) = Real.log (1 + R) := by
        have := abs_eq_zero.mp h4
        linarith
      have hR0 : R ≠ 0 := by
        intro h0
        apply hx1
        refine ⟨hK0, ?_⟩
        have : value iz * value invc = 1 := by linarith
        rwa [h1, mul_one] at this
      have hRmin : 1 / 2 ^ 53 ≤ |R| := by
        obtain ⟨Z, -, -, -, hzv, -, hZ, -⟩ := PowLogReduce.split_state iz e f he hf hf1023 hiz
        have hzval : value iz = (Z : ℝ) / 2 ^ 53 := by
          rw [PowLogReduce.value_of_scaled iz Z 1021 (by norm_num) hzv]
          norm_num
        have hRZ : R = ((Z : ℝ) - 2 ^ 53) / 2 ^ 53 := by
          show value iz * value invc - 1 = _
          rw [h1, mul_one, hzval, sub_div, div_self (by positivity : (2 : ℝ) ^ 53 ≠ 0)]
        have hint : (Z : ℝ) - 2 ^ 53 = (((Z : Int) - 2 ^ 53 : Int) : ℝ) := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
        have hne : ((Z : Int) - 2 ^ 53) ≠ 0 := by
          intro h0
          apply hR0
          rw [hRZ, hint, h0, Int.cast_zero, zero_div]
        have h1' : (1 : ℝ) ≤ |(Z : ℝ) - 2 ^ 53| := by
          have h5 : (1 : Int) ≤ |(Z : Int) - 2 ^ 53| := Int.one_le_abs hne
          have h6 := (Int.cast_le (R := ℝ)).mpr h5
          rw [Int.cast_one, Int.cast_abs] at h6
          rw [hint]
          exact h6
        rw [hRZ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
        exact div_le_div_of_nonneg_right h1' (by positivity)
      have hLR : |R| * (1 - 1006 / 1000 * (23 / 4000)) ≤ |L| := by
        rw [hLz, hlz]
        have h5 := abs_sub_abs_le_abs_sub R (Real.log (1 + R))
        have h7 : |R - Real.log (1 + R)| = |Real.log (1 + R) - R| := abs_sub_comm _ _
        have h6 := square_bound R hR
        linarith
      have hc := case_one (value W.1) (value W.2) L R (K : ℝ) (value lt)
        ((K : ℝ) * value 0x3FE62E42FEFA3800 + value lc) multiplicationUnderflowEpsilon hKr h3
        (by rw [hKr, h2, zero_mul, add_zero]) hR hμ1 hRmin hLR (hE1 (hlc0 hc0))
        (hT1 (hlc0 hc0))
      exact hc
    · -- `logc ≠ 0`: `|log z| ≥ |r|` and `|log z| ≥ 1/460`
      have hsep : |R| ≤ |value lc + R| ∧ 1 / 450 ≤ |value lc + R| := by
        rcases lt_or_gt_of_ne hc0 with hn | hp
        · obtain ⟨h1, h2⟩ := hneg hn
          have hs : value lc + R < 0 := by linarith
          rw [abs_of_neg hs]
          refine ⟨?_, by linarith⟩
          rcases le_or_gt 0 R with hr | hr
          · rw [abs_of_nonneg hr]
            linarith
          · rw [abs_of_neg hr]
            linarith
        · obtain ⟨h1, h2⟩ := hpos hp
          have hs : 0 < value lc + R := by linarith
          rw [abs_of_pos hs]
          refine ⟨?_, by linarith⟩
          rcases le_or_gt 0 R with hr | hr
          · rw [abs_of_nonneg hr]
            linarith
          · rw [abs_of_neg hr]
            linarith
      have hdiff : |L - (value lc + R)| ≤ 1 / 2 ^ 97 + 1006 / 1000 * R ^ 2 + 1 / 2 ^ 43 := by
        rw [hLz]
        have h1 := abs_le.mp hlogz
        have h2 := abs_le.mp hl1
        have h3 := abs_le.mp hltb
        rw [abs_le]
        constructor <;> linarith
      have hd2 : 1006 / 1000 * R ^ 2 ≤ 1006 / 1000 * (23 / 4000) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by norm_num)
      have h7 := abs_sub_abs_le_abs_sub (value lc + R) L
      have h8 : |value lc + R - L| = |L - (value lc + R)| := abs_sub_comm _ _
      have hL2 : 1 / 460 ≤ |L| := by
        have : (1 : ℝ) / 2 ^ 97 + 1006 / 1000 * (23 / 4000) ^ 2 + 1 / 2 ^ 43 ≤
            1 / 450 - 1 / 460 := by norm_num
        linarith
      have hL1 : |R| ≤ 103 / 100 * |L| := by
        have h9 : 1006 / 1000 * R ^ 2 ≤ 1006 / 1000 * (23 / 4000 * |R|) :=
          mul_le_mul_of_nonneg_left (square_bound R hR) (by norm_num)
        have h10 : (1 : ℝ) / 2 ^ 97 + 1 / 2 ^ 43 ≤ 1 / 100 * (1 / 460) := by norm_num
        linarith
      have hTb : |(K : ℝ) * value 0x3FE62E42FEFA3800 + value lc + R| ≤ 36 / 100 := by
        rw [hKr, zero_mul, zero_add]
        have := abs_add_le (value lc) R
        linarith
      exact case_c (value W.1) (value W.2) L R (K : ℝ) (value lt)
        ((K : ℝ) * value 0x3FE62E42FEFA3800 + value lc) multiplicationUnderflowEpsilon hKr hR
        hltb hμ1 hL1 hL2 hTb hE hT
  · -- `k ≠ 0`: `|L| ≥ 0.34 |k|`
    have hK1 : (1 : ℝ) ≤ |(K : ℝ)| := by
      have : (1 : Int) ≤ |K| := Int.one_le_abs hK0
      exact_mod_cast this
    have hK' : |(K : ℝ)| ≤ 1100 := by exact_mod_cast hK
    have hlz : |Real.log (value iz)| ≤ 3526 / 10000 := by
      have h1 := abs_le.mp hlogz
      have h2 := abs_le.mp hl1
      have h3 := abs_le.mp hltb
      have h4 := abs_le.mp hlcb
      have h5 := abs_le.mp hR
      have h6 : 1006 / 1000 * R ^ 2 ≤ 1006 / 1000 * (23 / 4000) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by norm_num)
      rw [abs_le]
      constructor <;> linarith
    have hL : 34 / 100 * |(K : ℝ)| ≤ |L| := by
      have h1 := abs_sub_abs_le_abs_sub ((K : ℝ) * Real.log 2) L
      have h2 : L - (K : ℝ) * Real.log 2 = Real.log (value iz) := by
        show (K : ℝ) * Real.log 2 + Real.log (value iz) - (K : ℝ) * Real.log 2 = _
        ring
      rw [abs_sub_comm, h2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)] at h1
      have h3 : |(K : ℝ)| * (6931 / 10000) ≤ |(K : ℝ)| * Real.log 2 :=
        mul_le_mul_of_nonneg_left hln2 (abs_nonneg _)
      linarith
    have hTb : |(K : ℝ) * value 0x3FE62E42FEFA3800 + value lc + R| ≤ 763 * |(K : ℝ)| := by
      have h1 := abs_add_le ((K : ℝ) * value 0x3FE62E42FEFA3800 + value lc) R
      have h2 : |(K : ℝ) * value 0x3FE62E42FEFA3800 + value lc| ≤
          |(K : ℝ)| * (6932 / 10000) + 3466 / 10000 := by
        have := abs_add_le ((K : ℝ) * value 0x3FE62E42FEFA3800) (value lc)
        obtain ⟨-, -, hh0, hh1, -⟩ := PowLogSum.ln2_words
        rw [abs_mul, abs_of_pos hh0] at this
        have : |(K : ℝ)| * value 0x3FE62E42FEFA3800 ≤ |(K : ℝ)| * (6932 / 10000) :=
          mul_le_mul_of_nonneg_left hh1 (abs_nonneg _)
        linarith
      linarith
    exact case_k (value W.1) (value W.2) L R (K : ℝ) (value lt)
      ((K : ℝ) * value 0x3FE62E42FEFA3800 + value lc) multiplicationUnderflowEpsilon hK1 hK'
      hR hltb hμ0 hμ1 hL hTb hE hT

#print axioms tail_real
#print axioms cube_bound
#print axioms square_bound
#print axioms case_k
#print axioms case_c
#print axioms case_one
#print axioms core_relative

end Verified.Examples.PowLogCases
