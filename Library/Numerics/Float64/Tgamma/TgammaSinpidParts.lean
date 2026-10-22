import Library.Numerics.Float64.Tgamma.TgammaSinpidLow

/-!
The two products of `Tgamma.asSinpid` before their sum.  The sine product `C1 = (qh + ql') (ch + cl)`,
with `(qh, ql) = c134 + q` exact and `ql' = ql + s0`, approximates `(ch + cl) (c134 + s0 + Q)` for
the sine polynomial's exact value `Q` (`sin_part`).  The cosine product `P = T2 (sh + sl)`, with
`(th, tl) = c130 + p` exact and `T2 = d (th + (tl + c0))`, approximates `d (c130 + c0 + P') (sh + sl)`
for the cosine polynomial's exact value `P'` (`cos_part`).  The bounds are proportional to the table
values `ch` and `sh` up to terms below `2^-1068`, so that the ends of the table, where one of them
is zero, need no separate analysis.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSinpidParts
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaSinpidLow

set_option exponentiation.threshold 4096

set_option maxHeartbeats 1000000 in
/-- **The sine product** `C1`. -/
theorem sin_part (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (q c134 s0 ch cl : Float) (Qv : ℝ)
    (hq : FApprox q Qv (21 / 10 ^ 23)) (hQv : |Qv| ≤ 617 / 10 ^ 9)
    (h134f : Finite c134.toBits) (h134 : 2454 / 10 ^ 5 ≤ value c134.toBits)
    (h134' : value c134.toBits ≤ 2455 / 10 ^ 5)
    (hs0f : Finite s0.toBits) (hs0 : |value s0.toBits| ≤ 957 / 10 ^ 21)
    (hchf : Finite ch.toBits) (hclf : Finite cl.toBits) (hch0 : 0 ≤ value ch.toBits)
    (hch1 : value ch.toBits ≤ 1) (hcl : |value cl.toBits| ≤ value ch.toBits / 2 ^ 53) :
    let Q := fastTwoSum c134 q
    let C1 := mulDD Q.1 (Q.2 + s0) ch cl
    Finite C1.1.toBits ∧ Finite C1.2.toBits ∧
      |value C1.1.toBits + value C1.2.toBits -
          (value ch.toBits + value cl.toBits) * (value c134.toBits + value s0.toBits + Qv)| ≤
        value ch.toBits * (212 / 10 ^ 24) + 1 / 2 ^ 1069 ∧
      |value C1.1.toBits| ≤ value ch.toBits * (2461 / 10 ^ 5) + 1 / 2 ^ 1075 ∧
      |value C1.2.toBits| ≤ value ch.toBits * (84 / 1000) / 2 ^ 53 + 1 / 2 ^ 1069 ∧
      value ch.toBits * (245 / 10 ^ 4) - 1 / 2 ^ 1068 ≤ |value C1.1.toBits| := by
  intro Q C1
  have hs0w : |value s0.toBits| ≤ 1 / 2 ^ 59 := by
    linarith [(by norm_num : (957 / 10 ^ 21 : ℝ) ≤ 1 / 2 ^ 59)]
  have hqm := hq.mag
  have hqb : |value q.toBits| ≤ 618 / 10 ^ 9 := by
    linarith [(by norm_num : (617 / 10 ^ 9 : ℝ) + 21 / 10 ^ 23 ≤ 618 / 10 ^ 9)]
  have h134a : |value c134.toBits| = value c134.toBits := abs_of_pos (by linarith)
  obtain ⟨hQ1f, hQ2f, hQsum, hQ2q, hQ2⟩ := fastTwoSum_spec c134 q h134f hq.1
    (by rw [h134a]; linarith) (by rw [h134a]; linarith [(by norm_num : (2455 / 10 ^ 5 : ℝ) < 2 ^ 900)])
  have hQt := fts_low c134 q h134f hq.1 (by
    have := abs_add_le (value c134.toBits) (value q.toBits)
    linarith [(by norm_num : (2455 / 10 ^ 5 : ℝ) + 618 / 10 ^ 9 < 2 ^ 1023)]) hQsum
  obtain ⟨vq1, hvq1⟩ : ∃ v, v = value Q.1.toBits := ⟨_, rfl⟩
  obtain ⟨vq2, hvq2⟩ : ∃ v, v = value Q.2.toBits := ⟨_, rfl⟩
  rw [← hvq1, ← hvq2] at hQsum hQt
  rw [← hvq2] at hQ2q
  rw [← hvq1, ← hvq2] at hQ2
  have hq1b : |vq1| ≤ 2456 / 10 ^ 5 := by
    have : vq1 = value c134.toBits + value q.toBits - vq2 := by linarith
    rw [this]
    have h1 := abs_sub (value c134.toBits + value q.toBits) vq2
    have h2 := abs_add_le (value c134.toBits) (value q.toBits)
    rw [h134a] at h2
    linarith [(by norm_num : (2455 / 10 ^ 5 : ℝ) + 618 / 10 ^ 9 + 618 / 10 ^ 9 ≤ 2456 / 10 ^ 5)]
  have hq2b : |vq2| ≤ 1 / 2 ^ 57 := by
    linarith [(by norm_num : (2456 / 10 ^ 5 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 57)]
  -- `ql' = ql + s0`
  have hql := (fapprox_add (fapprox_self Q.2 hQ2f) (fapprox_self s0 hs0f) (1 / 2 ^ 56) (by
    rw [← hvq2]
    have := abs_add_le vq2 (value s0.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 57 + 1 / 2 ^ 59 + (0 + 0) ≤ 1 / 2 ^ 56)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 109 : ℝ) by norm_num)
  rw [← hvq2] at hql
  have hqlt := fapprox_add (fapprox_self Q.2 hQ2f) (fapprox_self s0 hs0f)
    (|value Q.2.toBits| + |value s0.toBits|) (by simp only [add_zero]; exact abs_add_le _ _)
    (by rw [← hvq2]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 57 + 1 / 2 ^ 59 < 2 ^ 1023)])
  rw [← hvq2] at hqlt
  obtain ⟨vql, hvql⟩ : ∃ v, v = value (Q.2 + s0).toBits := ⟨_, rfl⟩
  have hqlt2 : |vql| ≤ (|vq2| + |value s0.toBits|) * (1 + 1 / 2 ^ 53) := by
    have h1 : |vql - (vq2 + value s0.toBits)| ≤ 0 + 0 + (|vq2| + |value s0.toBits|) / 2 ^ 53 := by
      rw [hvql]; exact hqlt.2
    have h2 := abs_sub_abs_le_abs_sub vql (vq2 + value s0.toBits)
    have h3 := abs_add_le vq2 (value s0.toBits)
    linarith
  have hq2t : |vq2| ≤ 2456 / 10 ^ 5 / 2 ^ 53 * (1 + 1 / 2 ^ 52) := by
    have := mul_le_mul_of_nonneg_right hq1b (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 53 * (1 + 1 / 2 ^ 52))
    linarith
  have hqlT : |vql| ≤ (2456 / 10 ^ 5 / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 957 / 10 ^ 21) *
      (1 + 1 / 2 ^ 53) := by
    have := hs0
    nlinarith [abs_nonneg vq2, abs_nonneg (value s0.toBits)]
  have hql2 : |vql - (vq2 + value s0.toBits)| ≤ 1 / 2 ^ 109 := by rw [hvql]; exact hql.2
  have hqlb : |vql| ≤ 1 / 2 ^ 55 := by
    have h1 := abs_add_le vq2 (value s0.toBits)
    have h2 := abs_sub_abs_le_abs_sub vql (vq2 + value s0.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 57 + 1 / 2 ^ 59 + 1 / 2 ^ 109 ≤ 1 / 2 ^ 55)]
  -- the product
  obtain ⟨Ch, hChd⟩ : ∃ v, v = value ch.toBits := ⟨_, rfl⟩
  rw [← hChd] at hch0 hch1 hcl ⊢
  have hcha : |value ch.toBits| = Ch := by rw [← hChd, abs_of_nonneg hch0]
  have hcl0 : 0 ≤ Ch / 2 ^ 52 := div_nonneg hch0 (by norm_num)
  have hcl52 : |value cl.toBits| ≤ Ch / 2 ^ 52 := by linarith
  obtain ⟨hC1f, hC2f, he, hl, hh⟩ := mulDD_spec hF Q.1 (Q.2 + s0) ch cl hQ1f hql.1 hchf hclf
    (Ch * (2456 / 10 ^ 5)) (Ch * (1 / 2 ^ 55)) (Ch / 2 ^ 52 * (2456 / 10 ^ 5))
    (Ch / 2 ^ 52 * (1 / 2 ^ 55))
    (by rw [hcha, ← hvq1]; exact mul_le_mul_of_nonneg_left hq1b hch0)
    (by rw [hcha, ← hvql]; exact mul_le_mul_of_nonneg_left hqlb hch0)
    (by rw [← hvq1]; exact mul_le_mul hcl52 hq1b (abs_nonneg _) hcl0)
    (by rw [← hvql]; exact mul_le_mul hcl52 hqlb (abs_nonneg _) hcl0)
    (by linarith [(by norm_num : (2456 / 10 ^ 5 : ℝ) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 / 2 ^ 55 : ℝ) + 1 / 2 ^ 52 * (2456 / 10 ^ 5) ≤ 2 ^ 900)])
  rw [← hvq1, ← hvql, ← hChd] at he
  have hlw := mulDD_low hF Q.1 (Q.2 + s0) ch cl hQ1f hql.1 hchf hclf
    (by rw [hcha, ← hvq1]; have := mul_le_mul hch1 hq1b (abs_nonneg _) zero_le_one
        linarith [(by norm_num : (2456 / 10 ^ 5 : ℝ) ≤ 2 ^ 900)])
    (by rw [hcha, ← hvql]; have := mul_le_mul hch1 hqlb (abs_nonneg _) zero_le_one
        linarith [(by norm_num : (1 / 2 ^ 55 : ℝ) ≤ 2 ^ 800)])
    (by rw [← hvq1]; have := mul_le_mul hcl52 hq1b (abs_nonneg _) hcl0
        linarith [(by norm_num : (1 / 2 ^ 52 * (2456 / 10 ^ 5) : ℝ) ≤ 2 ^ 800),
          mul_le_mul_of_nonneg_right hch1 (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 52 * (2456 / 10 ^ 5))])
  rw [hcha, ← hvq1, ← hvql] at hlw
  have hlw1 : Ch * |vql| ≤ Ch * ((2456 / 10 ^ 5 / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 957 / 10 ^ 21) *
      (1 + 1 / 2 ^ 53)) := mul_le_mul_of_nonneg_left hqlT hch0
  have hlw2 : |value cl.toBits| * |vq1| ≤ Ch / 2 ^ 53 * (2456 / 10 ^ 5) :=
    mul_le_mul hcl hq1b (abs_nonneg _) (div_nonneg hch0 (by norm_num))
  refine ⟨hC1f, hC2f, ?_⟩
  obtain ⟨c1, hc1⟩ : ∃ v, v = value C1.1.toBits := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ v, v = value C1.2.toBits := ⟨_, rfl⟩
  obtain ⟨vcl, hvcl⟩ : ∃ v, v = value cl.toBits := ⟨_, rfl⟩
  rw [← hc1, ← hc2] at he
  rw [← hc2] at hl hlw
  rw [← hc1] at hh hlw
  rw [← hc1, ← hc2, ← hvcl]
  rw [← hvcl] at he hcl
  -- `qh + ql'` against the exact kernel
  obtain ⟨K, hK⟩ : ∃ v, v = value c134.toBits + value s0.toBits + Qv := ⟨_, rfl⟩
  have hdel : |vq1 + vql - K| ≤ 1 / 2 ^ 109 + 21 / 10 ^ 23 := by
    have h1 : vq1 + vql - K = (vql - (vq2 + value s0.toBits)) + (value q.toBits - Qv) := by
      rw [hK]; linarith
    rw [h1]
    have h2 := abs_add_le (vql - (vq2 + value s0.toBits)) (value q.toBits - Qv)
    linarith [hq.2]
  have hsn : |Ch + vcl| ≤ Ch * (1 + 1 / 2 ^ 52) := by
    have := abs_add_le Ch vcl
    rw [abs_of_nonneg hch0] at this
    linarith
  have hprod : |(vq1 + vql) * (Ch + vcl) - (Ch + vcl) * K| ≤
      Ch * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 109 + 21 / 10 ^ 23) := by
    rw [show (vq1 + vql) * (Ch + vcl) - (Ch + vcl) * K = (Ch + vcl) * (vq1 + vql - K) by ring,
      abs_mul]
    exact mul_le_mul hsn hdel (abs_nonneg _) (mul_nonneg hch0 (by norm_num))
  have herr : |c1 + c2 - (Ch + vcl) * K| ≤ Ch * (212 / 10 ^ 24) + 1 / 2 ^ 1069 := by
    have h1 := abs_add_le (c1 + c2 - (vq1 + vql) * (Ch + vcl)) ((vq1 + vql) * (Ch + vcl) - (Ch + vcl) * K)
    rw [show c1 + c2 - (vq1 + vql) * (Ch + vcl) + ((vq1 + vql) * (Ch + vcl) - (Ch + vcl) * K) =
      c1 + c2 - (Ch + vcl) * K by ring] at h1
    have h2 : Ch * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 109 + 21 / 10 ^ 23) +
        (Ch / 2 ^ 52 * (1 / 2 ^ 55) + (4 * (Ch * (1 / 2 ^ 55) + Ch / 2 ^ 52 * (2456 / 10 ^ 5)) +
          Ch * (2456 / 10 ^ 5) / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070) ≤
        Ch * (212 / 10 ^ 24) + 1 / 2 ^ 1069 := by
      have : (1 + 1 / 2 ^ 52 : ℝ) * (1 / 2 ^ 109 + 21 / 10 ^ 23) + (1 / 2 ^ 52 * (1 / 2 ^ 55) +
          (4 * (1 / 2 ^ 55 + 1 / 2 ^ 52 * (2456 / 10 ^ 5)) + 2456 / 10 ^ 5 / 2 ^ 51) / 2 ^ 53) ≤
          212 / 10 ^ 24 := by norm_num
      have h3 := mul_le_mul_of_nonneg_left this hch0
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 1069)]
    linarith
  refine ⟨by rw [← hK]; exact herr, ?_, ?_, ?_⟩
  · linarith [(by norm_num : (2456 / 10 ^ 5 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 2461 / 10 ^ 5)]
  · have hk : ((2456 / 10 ^ 5 / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 957 / 10 ^ 21) * (1 + 1 / 2 ^ 53) +
        1 / 2 ^ 53 * (2456 / 10 ^ 5) + 2461 / 10 ^ 5 / 2 ^ 53 : ℝ) * (1 + 1 / 2 ^ 50) ≤
        84 / 1000 / 2 ^ 53 := by norm_num
    have hc1b : |c1| / 2 ^ 53 ≤ Ch * (2461 / 10 ^ 5) / 2 ^ 53 + 1 / 2 ^ 1075 / 2 ^ 53 := by
      linarith
    have hk2 := mul_le_mul_of_nonneg_left hk hch0
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 / 2 ^ 53 * (1 + 1 / 2 ^ 50) + 1 / 2 ^ 1070 ≤
      1 / 2 ^ 1069)]
  · -- the lower bound
    have hK0 : 24539 / 10 ^ 6 ≤ K := by
      rw [hK]
      have := (abs_le.mp hs0).1
      have := (abs_le.mp hQv).1
      linarith [(by norm_num : (2454 / 10 ^ 5 : ℝ) - 1 / 2 ^ 59 - 617 / 10 ^ 9 ≥ 24539 / 10 ^ 6)]
    have hlo : Ch * (1 - 1 / 2 ^ 52) * (24539 / 10 ^ 6) ≤ (Ch + vcl) * K := by
      have h1 : Ch * (1 - 1 / 2 ^ 52) ≤ Ch + vcl := by
        have := (abs_le.mp hcl).1; linarith
      exact mul_le_mul h1 hK0 (by norm_num) (by
        have := (abs_le.mp hcl).1
        linarith [(by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 52), mul_nonneg hch0
          (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 52)])
    have h1 := (abs_le.mp herr).1
    have h2 := (abs_le.mp hl).2
    have h3 : c1 ≤ |c1| := le_abs_self c1
    have h4 := le_abs_self c2
    have h5 : (1 - 1 / 2 ^ 52 : ℝ) * (24539 / 10 ^ 6) - 212 / 10 ^ 24 -
        ((1 / 2 ^ 55 + 1 / 2 ^ 52 * (2456 / 10 ^ 5)) * (1 + 1 / 2 ^ 50) + 2456 / 10 ^ 5 / 2 ^ 52) ≥
        245 / 10 ^ 4 := by norm_num
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1069 + 1 / 2 ^ 1070 ≤ 1 / 2 ^ 1068)]

/-- **The cosine product** `P`. -/
theorem cos_part (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d p c130 c0 sh sl : Float) (Pv : ℝ)
    (hdf : Finite d.toBits) (hD : |value d.toBits| ≤ 1 / 2)
    (hp : FApprox p Pv (1 / 2 ^ 77)) (hPv : |Pv| ≤ 1 / 2 ^ 26)
    (h130f : Finite c130.toBits) (h130 : 1 / 4000 ≤ |value c130.toBits|)
    (h130' : |value c130.toBits| ≤ 1 / 3300)
    (hc0f : Finite c0.toBits) (hc0 : |value c0.toBits| ≤ 1 / 2 ^ 65)
    (hshf : Finite sh.toBits) (hslf : Finite sl.toBits) (hsh0 : 0 ≤ value sh.toBits)
    (hsh1 : value sh.toBits ≤ 1) (hsl : |value sl.toBits| ≤ value sh.toBits / 2 ^ 52) :
    let T := fastTwoSum c130 p
    let T2 := mulDDD d T.1 (T.2 + c0)
    let P := mulDD T2.1 T2.2 sh sl
    Finite P.1.toBits ∧ Finite P.2.toBits ∧
      |value P.1.toBits + value P.2.toBits -
          value d.toBits * (value c130.toBits + value c0.toBits + Pv) *
            (value sh.toBits + value sl.toBits)| ≤ value sh.toBits / 2 ^ 77 + 1 / 2 ^ 1069 ∧
      |value P.1.toBits| ≤ value sh.toBits / 5997 + 1 / 2 ^ 1075 ∧
      |value P.2.toBits| ≤ value sh.toBits / 2 ^ 60 + 1 / 2 ^ 1070 := by
  intro T T2 P
  have hpm := hp.mag
  have hpb : |value p.toBits| ≤ 1 / 2 ^ 26 + 1 / 2 ^ 77 := by linarith
  obtain ⟨hT1f, hT2f, hTsum, hT2p, hT2⟩ := fastTwoSum_spec c130 p h130f hp.1
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 26 + 1 / 2 ^ 77 ≤ 1 / 4000)])
    (by linarith [(by norm_num : (1 / 3300 : ℝ) < 2 ^ 900)])
  obtain ⟨vt1, hvt1⟩ : ∃ v, v = value T.1.toBits := ⟨_, rfl⟩
  obtain ⟨vt2, hvt2⟩ : ∃ v, v = value T.2.toBits := ⟨_, rfl⟩
  rw [← hvt1, ← hvt2] at hTsum
  rw [← hvt2] at hT2p
  rw [← hvt1, ← hvt2] at hT2
  have ht1b : |vt1| ≤ 1 / 3000 := by
    have : vt1 = value c130.toBits + value p.toBits - vt2 := by linarith
    rw [this]
    have h1 := abs_sub (value c130.toBits + value p.toBits) vt2
    have h2 := abs_add_le (value c130.toBits) (value p.toBits)
    linarith [(by norm_num : (1 / 3300 : ℝ) + 2 * (1 / 2 ^ 26 + 1 / 2 ^ 77) ≤ 1 / 3000)]
  have ht2b : |vt2| ≤ 1 / 2 ^ 63 := by
    linarith [(by norm_num : (1 / 3000 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 63)]
  -- `tl' = tl + c0`
  have htl := (fapprox_add (fapprox_self T.2 hT2f) (fapprox_self c0 hc0f) (1 / 2 ^ 62) (by
    rw [← hvt2]
    have := abs_add_le vt2 (value c0.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 63 + 1 / 2 ^ 65 + (0 + 0) ≤ 1 / 2 ^ 62)])
    (by norm_num)).mono (show _ ≤ (1 / 2 ^ 115 : ℝ) by norm_num)
  rw [← hvt2] at htl
  obtain ⟨vtl, hvtl⟩ : ∃ v, v = value (T.2 + c0).toBits := ⟨_, rfl⟩
  have htl2 : |vtl - (vt2 + value c0.toBits)| ≤ 1 / 2 ^ 115 := by rw [hvtl]; exact htl.2
  have htlb : |vtl| ≤ 1 / 2 ^ 61 := by
    have h1 := abs_add_le vt2 (value c0.toBits)
    have h2 := abs_sub_abs_le_abs_sub vtl (vt2 + value c0.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 63 + 1 / 2 ^ 65 + 1 / 2 ^ 115 ≤ 1 / 2 ^ 61)]
  -- `T2 = d (th + tl')`
  obtain ⟨D, hDd⟩ : ∃ v, v = value d.toBits := ⟨_, rfl⟩
  rw [← hDd] at hD ⊢
  have hD0 : 0 ≤ |D| := abs_nonneg D
  obtain ⟨hT21f, hT22f, he2, hl2, hh2⟩ := mulDDD_spec hF d T.1 (T.2 + c0) hdf hT1f htl.1
    (|D| / 3000) (|D| / 2 ^ 61)
    (by rw [← hvt1, ← hDd]; have := mul_le_mul_of_nonneg_right ht1b hD0; linarith)
    (by rw [← hvtl, ← hDd]; have := mul_le_mul_of_nonneg_right htlb hD0; linarith)
    (by linarith [(by norm_num : (1 / 2 / 3000 : ℝ) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 / 2 / 2 ^ 61 : ℝ) ≤ 2 ^ 900)])
  rw [← hDd, ← hvt1, ← hvtl] at he2
  obtain ⟨u1, hu1⟩ : ∃ v, v = value T2.1.toBits := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ v, v = value T2.2.toBits := ⟨_, rfl⟩
  rw [← hu1, ← hu2] at he2
  rw [← hu2] at hl2
  rw [← hu1] at hh2
  have hu1b : |u1| ≤ 1 / 5999 := by
    linarith [(by norm_num : (1 / 2 / 3000 : ℝ) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 1 / 5999)]
  have hu2b : |u2| ≤ 1 / 2 ^ 61 := by
    linarith [(by norm_num : (1 / 2 / 2 ^ 61 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 / 3000 / 2 ^ 52 +
      1 / 2 ^ 1071 ≤ 1 / 2 ^ 61)]
  -- `T2` against `d K`
  obtain ⟨K, hK⟩ : ∃ v, v = value c130.toBits + value c0.toBits + Pv := ⟨_, rfl⟩
  have hdel : |vt1 + vtl - K| ≤ 1 / 2 ^ 115 + 1 / 2 ^ 77 := by
    have h1 : vt1 + vtl - K = (vtl - (vt2 + value c0.toBits)) + (value p.toBits - Pv) := by
      rw [hK]; linarith
    rw [h1]
    have h2 := abs_add_le (vtl - (vt2 + value c0.toBits)) (value p.toBits - Pv)
    linarith [hp.2]
  have hT2e : |u1 + u2 - D * K| ≤ 1 / 2 ^ 78 + 1 / 2 ^ 112 + 1 / 2 ^ 1072 := by
    have h1 : |D * (vt1 + vtl) - D * K| ≤ 1 / 2 * (1 / 2 ^ 115 + 1 / 2 ^ 77) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul hD hdel (abs_nonneg _) (by norm_num)
    have h2 := abs_add_le (u1 + u2 - D * (vt1 + vtl)) (D * (vt1 + vtl) - D * K)
    rw [show u1 + u2 - D * (vt1 + vtl) + (D * (vt1 + vtl) - D * K) = u1 + u2 - D * K by ring] at h2
    linarith [(by norm_num : (3 * (1 / 2 / 2 ^ 61) + 1 / 2 / 3000 / 2 ^ 51 : ℝ) / 2 ^ 53 +
      1 / 2 * (1 / 2 ^ 115 + 1 / 2 ^ 77) ≤ 1 / 2 ^ 78 + 1 / 2 ^ 112)]
  -- `P = T2 (sh + sl)`
  obtain ⟨Sh, hShd⟩ : ∃ v, v = value sh.toBits := ⟨_, rfl⟩
  rw [← hShd] at hsh0 hsh1 hsl ⊢
  have hsha : |value sh.toBits| = Sh := by rw [← hShd, abs_of_nonneg hsh0]
  have hsl0 : 0 ≤ Sh / 2 ^ 52 := by positivity
  obtain ⟨hP1f, hP2f, heP, hlP, hhP⟩ := mulDD_spec hF T2.1 T2.2 sh sl hT21f hT22f hshf hslf
    (Sh * (1 / 5999)) (Sh * (1 / 2 ^ 61)) (Sh / 2 ^ 52 * (1 / 5999)) (Sh / 2 ^ 52 * (1 / 2 ^ 61))
    (by rw [hsha, ← hu1]; exact mul_le_mul_of_nonneg_left hu1b hsh0)
    (by rw [hsha, ← hu2]; exact mul_le_mul_of_nonneg_left hu2b hsh0)
    (by rw [← hu1]; exact mul_le_mul hsl hu1b (abs_nonneg _) hsl0)
    (by rw [← hu2]; exact mul_le_mul hsl hu2b (abs_nonneg _) hsl0)
    (by linarith [(by norm_num : (1 / 5999 : ℝ) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 / 2 ^ 61 : ℝ) + 1 / 2 ^ 52 * (1 / 5999) ≤ 2 ^ 900)])
  rw [← hu1, ← hu2, ← hShd] at heP
  obtain ⟨p1, hp1d⟩ : ∃ v, v = value P.1.toBits := ⟨_, rfl⟩
  obtain ⟨p2, hp2d⟩ : ∃ v, v = value P.2.toBits := ⟨_, rfl⟩
  rw [← hp1d, ← hp2d] at heP
  rw [← hp2d] at hlP
  rw [← hp1d] at hhP
  rw [← hp1d, ← hp2d]
  refine ⟨hP1f, hP2f, ?_, ?_, ?_⟩
  · obtain ⟨vsl, hvsl⟩ : ∃ v, v = value sl.toBits := ⟨_, rfl⟩
    rw [← hvsl] at heP hsl ⊢
    have hcs : |Sh + vsl| ≤ Sh * (1 + 1 / 2 ^ 52) := by
      have := abs_add_le Sh vsl
      rw [abs_of_nonneg hsh0] at this
      linarith
    have h1 : |(u1 + u2) * (Sh + vsl) - D * K * (Sh + vsl)| ≤
        (1 / 2 ^ 78 + 1 / 2 ^ 112 + 1 / 2 ^ 1072) * (Sh * (1 + 1 / 2 ^ 52)) := by
      rw [← sub_mul, abs_mul]
      exact mul_le_mul hT2e hcs (abs_nonneg _) (by positivity)
    have h2 := abs_add_le (p1 + p2 - (u1 + u2) * (Sh + vsl))
      ((u1 + u2) * (Sh + vsl) - D * K * (Sh + vsl))
    rw [show p1 + p2 - (u1 + u2) * (Sh + vsl) +
      ((u1 + u2) * (Sh + vsl) - D * K * (Sh + vsl)) =
      p1 + p2 - D * K * (Sh + vsl) by ring] at h2
    rw [← hK]
    have h3 : (1 / 2 ^ 78 + 1 / 2 ^ 112 + 1 / 2 ^ 1072 : ℝ) * (Sh * (1 + 1 / 2 ^ 52)) ≤
        Sh * ((1 / 2 ^ 78 + 1 / 2 ^ 112) * (1 + 1 / 2 ^ 52)) + 2 / 2 ^ 1072 := by
      nlinarith
    linarith [(by norm_num : (1 / 2 ^ 78 + 1 / 2 ^ 112 : ℝ) * (1 + 1 / 2 ^ 52) +
      (1 / 2 ^ 52 * (1 / 2 ^ 61) + (4 * (1 / 2 ^ 61 + 1 / 2 ^ 52 * (1 / 5999)) +
        1 / 5999 / 2 ^ 51) / 2 ^ 53) ≤ 1 / 2 ^ 77)]
  · linarith [(by norm_num : (1 / 5999 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 1 / 5997)]
  · linarith [(by norm_num : ((1 / 2 ^ 61 : ℝ) + 1 / 2 ^ 52 * (1 / 5999)) * (1 + 1 / 2 ^ 50) +
      1 / 5999 / 2 ^ 52 ≤ 1 / 2 ^ 60)]

#print axioms sin_part
#print axioms cos_part

end Library.Numerics.Float64.Tgamma.TgammaSinpidParts
