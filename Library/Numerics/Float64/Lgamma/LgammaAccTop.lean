import Library.Numerics.Float64.Lgamma.LgammaAccPath
import Library.Numerics.Float64.Lgamma.LgammaFastTop

/-!
**The accurate path of `lgamma` from `2^800` to the threshold `x1`** within one step of
`log Γ x` (`accurate_top`).  The code's tests below 1/4 and its seven windows fail there
(`win_top`), and `Lgamma.asLgammaAsymAccurate` computes `(l0 - 1 + l1 + l2) (x - 1/2)` from the
logarithm `l0 + l1 + l2` of `x`, within `2^-62` of `log Γ x` relative (`asym_top`, from
`LgammaAsymAcc.asym_big`).  `log Γ x` stays below `2^1024 - 5 · 2^969`
(`LgammaFastTop.lgamma_le_top`), and the sums of the renormalization stay below the overflow
threshold `2^1024 - 2^970`: its first and third `fastTwoSum` add a high part and a part below half
of it, which `Library.Numerics.Float64.Tgamma.TgammaDDTop.fastTwoSum_spec_small` keeps exact up to the threshold, and its second and
fourth add low parts (`norm_top`).
The pair is within `2^-60` of `log Γ x`, its high part exceeds 3/8, so the polynomials about the
negative zeros do not apply, and its rounded sum is within one step (`sum_within_top`), as is a
row of the table of hard cases (`LgammaAccFinal.final_of_sum`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccTop
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaDDTop LgammaAccWin
  LgammaAccTests LgammaAccWalk LgammaWalk GammaThresholds

set_option exponentiation.threshold 4096

/-- The triple of `Lgamma.asLgammaAsymAccurate` from `2^800` on, near `L = log Γ x`. -/
def TopTriple (L : ℝ) (r : Float × Float × Float) : Prop :=
  Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - L| ≤ L / 2 ^ 62 ∧
    4 ≤ value r.1.toBits ∧ |value r.2.1.toBits| ≤ value r.1.toBits / 2 ^ 40 ∧
    |value r.2.2.toBits| ≤ value r.1.toBits / 2 ^ 80 ∧ 1 ≤ L ∧ L ≤ 2 ^ 1024 - 5 * 2 ^ 969

/-- The pair after the renormalization, near `L = log Γ x`. -/
def TopPair (L : ℝ) (p : Float × Float) : Prop :=
  Finite p.1.toBits ∧ Finite p.2.toBits ∧ 1 ≤ value p.1.toBits ∧
    |L - (value p.1.toBits + value p.2.toBits)| ≤ L / 2 ^ 60 ∧ 1 ≤ L ∧
    L ≤ 2 ^ 1024 - 5 * 2 ^ 969

set_option maxHeartbeats 4000000 in
/-- **The renormalization** of a triple with `TopTriple`: four `fastTwoSum` and the adjustment of
the low part. -/
theorem norm_top (L : ℝ) (a b c : Float) (hT : TopTriple L (a, b, c))
    (h1 l1 : Float) (e1 : fastTwoSum a b = (h1, l1))
    (l2 ll2 : Float) (e2 : fastTwoSum l1 c = (l2, ll2))
    (h3 l3 : Float) (e3 : fastTwoSum h1 l2 = (h3, l3))
    (l4 ll4 : Float) (e4 : fastTwoSum l3 ll2 = (l4, ll4)) (cond : Bool) :
    TopPair L (if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)) := by
  obtain ⟨fa, fb, fc, hE, ha4, hb, hc, hL1, hL⟩ := hT
  simp only at fa fb fc hE ha4 hb hc
  set A := value a.toBits with hAdef
  set B := value b.toBits with hBdef
  set C := value c.toBits with hCdef
  have hE' := abs_le.mp hE
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  -- the magnitudes
  have hA2 : A ≤ 2 * L := by linarith
  have hAmax : A ≤ 2 ^ 1025 := by linarith
  have hab0 : 0 < A + B := by linarith
  have hab : |A + B| < 2 ^ 1024 - 2 ^ 970 := by
    rw [abs_of_pos hab0]
    have : A / 2 ^ 80 ≤ 2 ^ 1025 / 2 ^ 80 := div_le_div_of_nonneg_right hAmax (by norm_num)
    have : L / 2 ^ 62 ≤ (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 62 := div_le_div_of_nonneg_right hL (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 1024 - 5 * 2 ^ 969 + (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 62 +
      2 ^ 1025 / 2 ^ 80 < 2 ^ 1024 - 2 ^ 970)]
  -- the first `fastTwoSum`: exact
  have hA' : |A| = A := abs_of_pos (by linarith)
  obtain ⟨f1, g1, s1, k1, -⟩ := fastTwoSum_spec_small a b fa fb (by rw [hA']; linarith)
    (by rw [hA']; linarith) (by linarith [(by norm_num : (2 : ℝ) ^ 1025 / 2 ^ 40 < 2 ^ 1022),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 40)]) hab
  rw [e1] at f1 g1 s1 k1
  dsimp only at f1 g1 s1 k1
  have k1' : |value l1.toBits| ≤ A / 2 ^ 40 := k1.trans hb
  -- the second: the low parts
  obtain ⟨f2, g2, d2, k2, m2⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc2.fts_approx l1 c g1 fc (A / 2 ^ 40) (A / 2 ^ 80) k1' hc
    (by linarith [(by norm_num : (2 : ℝ) ^ 1025 / 2 ^ 40 + 2 ^ 1025 / 2 ^ 80 ≤ 2 ^ 1000),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 40),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 80)])
  rw [e2] at f2 g2 d2 k2 m2
  dsimp only at f2 g2 d2 k2 m2
  have hA0 : 0 ≤ A := by linarith
  have k2' : |value l2.toBits| ≤ A / 2 ^ 39 := by
    linarith [(by ring : (A / 2 ^ 40 + A / 2 ^ 80) * (1 + 1 / 2 ^ 53) =
      A * ((1 / 2 ^ 40 + 1 / 2 ^ 80) * (1 + 1 / 2 ^ 53))),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 40 + 1 / 2 ^ 80 : ℝ) * (1 + 1 / 2 ^ 53) ≤
        1 / 2 ^ 39) hA0, (by ring : A * (1 / 2 ^ 39) = A / 2 ^ 39)]
  have m2' : |value ll2.toBits| ≤ A / 2 ^ 90 := by
    linarith [(by ring : (A / 2 ^ 40 + A / 2 ^ 80) / 2 ^ 51 = A * ((1 / 2 ^ 40 + 1 / 2 ^ 80) / 2 ^ 51)),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 40 + 1 / 2 ^ 80 : ℝ) / 2 ^ 51 ≤
        1 / 2 ^ 90) hA0, (by ring : A * (1 / 2 ^ 90) = A / 2 ^ 90)]
  have d2' : |value l2.toBits + value ll2.toBits - (value l1.toBits + C)| ≤ A / 2 ^ 132 := by
    linarith [(by ring : A / 2 ^ 80 / 2 ^ 53 + (A / 2 ^ 40 + A / 2 ^ 80) / 2 ^ 104 =
      A * (1 / 2 ^ 80 / 2 ^ 53 + (1 / 2 ^ 40 + 1 / 2 ^ 80) / 2 ^ 104)),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 80 / 2 ^ 53 +
        (1 / 2 ^ 40 + 1 / 2 ^ 80) / 2 ^ 104 : ℝ) ≤ 1 / 2 ^ 132) hA0,
      (by ring : A * (1 / 2 ^ 132) = A / 2 ^ 132)]
  -- the third: exact
  have hl1 := abs_le.mp k1'
  have hl2 := abs_le.mp k2'
  have hll2 := abs_le.mp m2'
  have hd2 := abs_le.mp d2'
  have hh1 : value h1.toBits = A + B - value l1.toBits := by linarith
  have hh1lo : A / 2 ≤ value h1.toBits := by linarith
  have hh1' : |value h1.toBits| = value h1.toBits := abs_of_pos (by linarith)
  have hsum3 : |value h1.toBits + value l2.toBits| < 2 ^ 1024 - 2 ^ 970 := by
    rw [abs_lt]
    have : A / 2 ^ 80 ≤ 2 ^ 1025 / 2 ^ 80 := div_le_div_of_nonneg_right hAmax (by norm_num)
    have : A / 2 ^ 90 ≤ 2 ^ 1025 / 2 ^ 90 := div_le_div_of_nonneg_right hAmax (by norm_num)
    have : A / 2 ^ 132 ≤ 2 ^ 1025 / 2 ^ 132 := div_le_div_of_nonneg_right hAmax (by norm_num)
    have : L / 2 ^ 62 ≤ (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 62 := div_le_div_of_nonneg_right hL (by norm_num)
    constructor
    · linarith
    · linarith [(by norm_num : (2 : ℝ) ^ 1024 - 5 * 2 ^ 969 + (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 62 +
        2 ^ 1025 / 2 ^ 80 + 2 ^ 1025 / 2 ^ 90 + 2 ^ 1025 / 2 ^ 132 < 2 ^ 1024 - 2 ^ 970)]
  obtain ⟨f3, g3, s3, k3, -⟩ := fastTwoSum_spec_small h1 l2 f1 f2 (by rw [hh1']; linarith)
    (by rw [hh1']; linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1025 / 2 ^ 39 < 2 ^ 1022),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 39)]) hsum3
  rw [e3] at f3 g3 s3 k3
  dsimp only at f3 g3 s3 k3
  have k3' : |value l3.toBits| ≤ A / 2 ^ 39 := k3.trans k2'
  -- the fourth: the low parts
  obtain ⟨f4, g4, d4, k4, m4⟩ := Library.Numerics.Float64.Tgamma.TgammaAcc2.fts_approx l3 ll2 g3 g2 (A / 2 ^ 39) (A / 2 ^ 90) k3'
    m2' (by linarith [(by norm_num : (2 : ℝ) ^ 1025 / 2 ^ 39 + 2 ^ 1025 / 2 ^ 90 ≤ 2 ^ 1000),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 39),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 90)])
  rw [e4] at f4 g4 d4 k4 m4
  dsimp only at f4 g4 d4 k4 m4
  have k4' : |value l4.toBits| ≤ A / 2 ^ 38 := by
    linarith [(by ring : (A / 2 ^ 39 + A / 2 ^ 90) * (1 + 1 / 2 ^ 53) =
      A * ((1 / 2 ^ 39 + 1 / 2 ^ 90) * (1 + 1 / 2 ^ 53))),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 39 + 1 / 2 ^ 90 : ℝ) * (1 + 1 / 2 ^ 53) ≤
        1 / 2 ^ 38) hA0, (by ring : A * (1 / 2 ^ 38) = A / 2 ^ 38)]
  have m4' : |value ll4.toBits| ≤ A / 2 ^ 89 := by
    linarith [(by ring : (A / 2 ^ 39 + A / 2 ^ 90) / 2 ^ 51 = A * ((1 / 2 ^ 39 + 1 / 2 ^ 90) / 2 ^ 51)),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 39 + 1 / 2 ^ 90 : ℝ) / 2 ^ 51 ≤
        1 / 2 ^ 89) hA0, (by ring : A * (1 / 2 ^ 89) = A / 2 ^ 89)]
  have d4' : |value l4.toBits + value ll4.toBits - (value l3.toBits + value ll2.toBits)| ≤
      A / 2 ^ 141 := by
    linarith [(by ring : A / 2 ^ 90 / 2 ^ 53 + (A / 2 ^ 39 + A / 2 ^ 90) / 2 ^ 104 =
      A * (1 / 2 ^ 90 / 2 ^ 53 + (1 / 2 ^ 39 + 1 / 2 ^ 90) / 2 ^ 104)),
      mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 90 / 2 ^ 53 +
        (1 / 2 ^ 39 + 1 / 2 ^ 90) / 2 ^ 104 : ℝ) ≤ 1 / 2 ^ 141) hA0,
      (by ring : A * (1 / 2 ^ 141) = A / 2 ^ 141)]
  have hl3 := abs_le.mp k3'
  have hl4 := abs_le.mp k4'
  have hll4 := abs_le.mp m4'
  have hd4 := abs_le.mp d4'
  -- the pair before the adjustment
  have hpair : |value h3.toBits + value l4.toBits - (A + B + C)| ≤ A / 2 ^ 88 := by
    rw [abs_le]
    constructor <;> linarith
  have hh3 : 1 ≤ value h3.toBits := by linarith
  have hl4b : |value l4.toBits| ≤ 2 ^ 1000 := by
    linarith [(by norm_num : (2 : ℝ) ^ 1025 / 2 ^ 38 ≤ 2 ^ 1000),
      div_le_div_of_nonneg_right hAmax (by norm_num : (0 : ℝ) ≤ 2 ^ 38)]
  obtain ⟨af, ad⟩ := LgammaAccNorm.adjust26 l4 ll4 f4 hl4b
  have had := abs_le.mp ad
  have hA88 : A / 2 ^ 88 ≤ L / 2 ^ 87 := by
    have := div_le_div_of_nonneg_right hA2 (by norm_num : (0 : ℝ) ≤ 2 ^ 88)
    linarith [(by ring : 2 * L / 2 ^ 88 = L / 2 ^ 87)]
  have hA87 : A / 2 ^ 87 ≤ L / 2 ^ 86 := by
    have := div_le_div_of_nonneg_right hA2 (by norm_num : (0 : ℝ) ≤ 2 ^ 87)
    linarith [(by ring : 2 * L / 2 ^ 87 = L / 2 ^ 86)]
  have hηL : 1 / 2 ^ 1075 ≤ L / 2 ^ 1000 := by
    have := div_le_div_of_nonneg_right hL1 (by norm_num : (0 : ℝ) ≤ 2 ^ 1000)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000)]
  have hL60 : L / 2 ^ 62 + L / 2 ^ 86 + L / 2 ^ 1000 ≤ L / 2 ^ 60 := by
    have : L / 2 ^ 62 + L / 2 ^ 86 + L / 2 ^ 1000 = L * (1 / 2 ^ 62 + 1 / 2 ^ 86 + 1 / 2 ^ 1000) := by
      ring
    rw [this]
    have := mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 62 + 1 / 2 ^ 86 + 1 / 2 ^ 1000 : ℝ) ≤
      1 / 2 ^ 60) (by linarith : (0 : ℝ) ≤ L)
    linarith [(by ring : L * (1 / 2 ^ 60) = L / 2 ^ 60)]
  by_cases hcnd : cond = true
  · rw [if_pos hcnd]
    refine ⟨f3, af, hh3, ?_, hL1, hL⟩
    simp only
    have hp := abs_le.mp hpair
    have h5 : |value l4.toBits| / 2 ^ 51 ≤ A / 2 ^ 38 / 2 ^ 51 :=
      div_le_div_of_nonneg_right k4' (by norm_num)
    rw [abs_le]
    constructor <;> linarith [(by ring : A / 2 ^ 38 / 2 ^ 51 = A / 2 ^ 89)]
  · rw [if_neg hcnd]
    refine ⟨f3, f4, hh3, ?_, hL1, hL⟩
    simp only
    have hp := abs_le.mp hpair
    rw [abs_le]
    constructor <;> linarith

/-- **The rounded sum** of a pair within `2^-60` of `L` from 1 to `2^1024 - 5 · 2^969` is within
one step of `L`. -/
theorem sum_within_top (fh fl : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits) (L : ℝ)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 2 ^ 1024 - 5 * 2 ^ 969)
    (h : |L - (value fh.toBits + value fl.toBits)| ≤ L / 2 ^ 60) :
    F64SignedRounding.WithinSteps 1 L (fh + fl).toBits := by
  set S := value fh.toBits + value fl.toBits with hSdef
  have hS := abs_le.mp h
  have hS0 : 0 < S := by
    have : L / 2 ^ 60 ≤ L / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    linarith
  have hSmax : |S| < 2 ^ 1024 - 2 ^ 970 := by
    rw [abs_of_pos hS0]
    have : L / 2 ^ 60 ≤ (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 60 := div_le_div_of_nonneg_right hL2 (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 1024 - 5 * 2 ^ 969 + (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 60 <
      2 ^ 1024 - 2 ^ 970)]
  have hr := F64TopPack.add_real_relative_top fh.toBits fl.toBits hfh hfl hSmax
  rw [← F64Bits.toBits_add] at hr
  obtain ⟨hwf, hw⟩ := hr
  apply F64RelativeStep.within_one_relative _ _ hwf
  · rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1)]
  · have hu : unitRoundoff64 = 1 / 2 ^ 53 := by norm_num [unitRoundoff64]
    rw [hu] at hw ⊢
    rw [abs_of_pos (show (0 : ℝ) < L by linarith)]
    rw [abs_of_pos hS0] at hw
    have k := abs_sub_le (value (fh + fl).toBits) S L
    have k1 : |S - L| ≤ L / 2 ^ 60 := by rw [abs_sub_comm]; exact h
    have k2 : 1 / 2 ^ 53 * S ≤ 1 / 2 ^ 53 * (L + L / 2 ^ 60) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have k3 : 1 / 2 ^ 53 * (L + L / 2 ^ 60) + L / 2 ^ 60 ≤ 11 / 8 * (1 / 2 ^ 53) * L := by
      have : 1 / 2 ^ 53 * (L + L / 2 ^ 60) + L / 2 ^ 60 =
          L * (1 / 2 ^ 53 * (1 + 1 / 2 ^ 60) + 1 / 2 ^ 60) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 / 2 ^ 53 * (1 + 1 / 2 ^ 60) + 1 / 2 ^ 60 : ℝ) ≤
        11 / 8 * (1 / 2 ^ 53)) (by linarith : (0 : ℝ) ≤ L)
      linarith [(by ring : L * (11 / 8 * (1 / 2 ^ 53)) = 11 / 8 * (1 / 2 ^ 53) * L)]
    linarith

set_option maxHeartbeats 1000000 in
/-- **The last two steps of `Lgamma.accurate`** from a pair with `TopPair`. -/
theorem tail_top (hDb : LgammaApprox.DbFact) (sx : Float) (hsx : Finite sx.toBits)
    (fh fl : Float) (hP : TopPair (GammaBasic.lgamma (value sx.toBits)) (fh, fl)) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits))
      (Lgamma.polyDD.match_1 (fun _ => Float)
        (if fh.abs < Float.ofBits 4600427019358961664 then
          Lgamma.accurate.match_1 (fun _ => Float × Float) (Lgamma.rootRange fh.abs sx) fun o n k sc =>
            if (o == 0) = true then (fh, fl)
            else
              Lgamma.polyDD.match_1 (fun _ => Float × Float)
                (fastTwoSum (entry Lgamma.accurateTable o + sx) (entry Lgamma.accurateTable (o + 1)))
                fun zh zl =>
                have zl := zl + entry Lgamma.accurateTable (o + 2)
                have sh := zh * sc
                have sl := zl * sc
                have fl := sh * Lgamma.polyD Lgamma.accurateTable (o + 3 + 2 * (n - k)) k sh
                Lgamma.polyDD.match_1 (fun _ => Float × Float)
                  (Lgamma.polyDD Lgamma.accurateTable (o + 3) (n - k) sh sl fl) fun fh fl => mulDD zh zl fh fl
        else (fh, fl))
        fun fh fl =>
          if fl.toBits + 2 &&& 4294967295 ≤ 2 then Lgamma.database Lgamma.dbTable sx (fh + fl) else fh + fl).toBits := by
  obtain ⟨hf1, hf2, hfh1, herr, hL1, hL2⟩ := hP
  simp only at hf1 hf2 hfh1 herr
  obtain ⟨haf, hafv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float fh hf1
  have hn : ¬ fh.abs < Float.ofBits 4600427019358961664 := by
    rw [F64UpperWord.float_lt_iff _ _ haf LgammaAccTail.c38.1, hafv, LgammaAccTail.c38.2,
      abs_of_pos (show (0 : ℝ) < value fh.toBits by linarith)]
    exact not_lt.mpr (by linarith)
  rw [if_neg hn]
  exact LgammaAccFinal.final_of_sum hDb sx hsx _ fh fl
    (sum_within_top fh fl hf1 hf2 _ hL1 hL2 herr)

/-- From `2^800` on, the window test about `c` of `Lgamma.accurate` fails. -/
theorem win_top (x c : Float) (cv : ℝ) (hx : Finite x.toBits) (hc : Finite c.toBits)
    (hcv : value c.toBits = cv) (hc0 : 0 ≤ cv) (hc4 : cv ≤ 4)
    (hx0 : 2 ^ 800 ≤ value x.toBits) (hxb : value x.toBits ≤ 2 ^ 1015) :
    ¬ (x - c).abs < 0.25 := by
  intro h
  have ha := fapprox_sub (approx_self _ hx) (approx_self _ hc)
    (|value x.toBits - value c.toBits|) (by simp)
    (by rw [hcv, abs_lt]; constructor <;>
      linarith [(by norm_num : (2 : ℝ) ^ 1015 + 4 < 2 ^ 1023)])
  obtain ⟨hdf, he⟩ := ha
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float _ hdf
  have h' := (lt_test _ _ _ _ haf c025.1 hav c025.2).mp h
  rw [hcv] at he
  simp only [add_zero, zero_add] at he
  have hpos : 0 < value x.toBits - cv := by linarith [(by norm_num : (4 : ℝ) < 2 ^ 800)]
  have hy : 2 ^ 799 ≤ |value x.toBits - cv| := by
    rw [abs_of_pos hpos]
    linarith [(by norm_num : (2 : ℝ) ^ 799 + 4 ≤ 2 ^ 800)]
  have := abs_sub_abs_le_abs_sub (value x.toBits - cv) (value (x - c).toBits)
  rw [abs_sub_comm (value x.toBits - cv)] at this
  have : |value x.toBits - cv| / 2 ^ 53 ≤ |value x.toBits - cv| / 2 :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
  linarith [(by norm_num : (1 : ℝ) / 4 < 2 ^ 799 / 2)]

/-- `x1 (log x1 - 1 + 2^-44 + 2^-50)`, with the bound on `log x1` of `LgammaFastTop`, stays below
`2^1024 - 13 · 2^968`. -/
theorem product_x1 :
    (x1 : ℚ) * (LgammaFastTop.logX1Hi - 1 + 1 / 2 ^ 44 + 1 / 2 ^ 50) ≤ 2 ^ 1024 - 13 * 2 ^ 968 := by
  decide +kernel

/-- **The triple of `asLgammaAsymAccurate`** from `2^800` to `x1` has `TopTriple`. -/
theorem asym_top (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAF : LgammaApprox.AsymFact) (x : Float) (hx : Finite x.toBits)
    (hlo : 2 ^ 800 ≤ value x.toBits) (hhi : value x.toBits ≤ (x1 : ℝ)) :
    TopTriple (GammaBasic.lgamma (value x.toBits))
      (Lgamma.asLgammaAsymAccurate Tgamma.logdTable Lgamma.logAccurateTable Lgamma.asymTable
        x 0.0) := by
  set vx := value x.toBits with hvx
  have hx0 : 0 < vx := lt_of_lt_of_le (by positivity) hlo
  have h1015 : vx ≤ 2 ^ 1015 := hhi.trans LgammaFastTop.x1_le_1015
  have hge : (2 : ℝ) ^ 120 ≤ vx := le_trans (by norm_num) hlo
  -- the product below the threshold
  have hprod : vx * (Real.log vx - 1 + 1 / 2 ^ 44 + 1 / 2 ^ 50) ≤ 2 ^ 1024 - 13 * 2 ^ 968 := by
    have hl := (Real.log_le_log hx0 hhi).trans LgammaFastTop.log_x1_le
    have hl0 : 83 ≤ Real.log vx := by
      have h1 := Real.log_le_log (by positivity) hge
      rw [Real.log_pow] at h1
      have hl2 := Real.log_two_gt_d9
      norm_num at hl2
      push_cast at h1
      linarith
    have hk := (Rat.cast_le (K := ℝ)).mpr product_x1
    push_cast at hk
    calc vx * (Real.log vx - 1 + 1 / 2 ^ 44 + 1 / 2 ^ 50)
        ≤ (x1 : ℝ) * ((LgammaFastTop.logX1Hi : ℝ) - 1 + 1 / 2 ^ 44 + 1 / 2 ^ 50) :=
          mul_le_mul hhi (by linarith) (by linarith) (by linarith)
      _ ≤ 2 ^ 1024 - 13 * 2 ^ 968 := hk
  -- the code from `2^120` on
  have hr := LgammaAsymAcc.asym_eq Tgamma.logdTable Lgamma.logAccurateTable Lgamma.asymTable x 0.0
  have hc : ¬ x < Float.ofBits 0x4770000000000000 := fun h => by
    have := (F64UpperWord.float_lt_iff _ _ hx LgammaAsymAcc.c120.1).mp h
    rw [LgammaAsymAcc.c120.2] at this
    linarith
  rw [if_neg hc] at hr
  rw [hr]
  obtain ⟨a, b, c, e, -, q1, q2, hP1⟩ := LgammaAsymAcc.asym_big hF hLA hAF x 0.0 hx c00.1 hge
    h1015 hprod (by rw [c00.2, abs_zero]; norm_num)
  rw [c00.2, add_zero] at e
  set L := GammaBasic.lgamma vx with hLdef
  have hL := LgammaFastTop.lgamma_le_top vx (by linarith [(by norm_num : (2 : ℝ) ≤ 2 ^ 800)]) hhi
  have he := abs_le.mp e
  have hq1 := abs_le.mp q1
  have hq2 := abs_le.mp q2
  -- `L` against `x`
  have hLx : vx ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 800)]
  refine ⟨a, b, c, ?_, by linarith, q1, q2, hL1, hL⟩
  have : vx / 2 ^ 86 ≤ L / 2 ^ 86 := div_le_div_of_nonneg_right hLx (by norm_num)
  rw [abs_le]
  constructor <;> linarith [(by ring : 1 / 2 ^ 63 * L + L / 2 ^ 86 =
    L * (1 / 2 ^ 63 + 1 / 2 ^ 86)), mul_le_mul_of_nonneg_left
      (by norm_num : (1 / 2 ^ 63 + 1 / 2 ^ 86 : ℝ) ≤ 1 / 2 ^ 62) (by linarith : (0 : ℝ) ≤ L),
    (by ring : L * (1 / 2 ^ 62) = L / 2 ^ 62)]

set_option maxHeartbeats 16000000 in
/-- **The accurate path from `2^800` to `x1`** within one step of `log Γ x`. -/
theorem accurate_top (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAF : LgammaApprox.AsymFact) (hDb : LgammaApprox.DbFact)
    (sx : Float) (hsx : Finite sx.toBits)
    (hlo : 2 ^ 800 ≤ value sx.toBits) (hhi : value sx.toBits ≤ (x1 : ℝ)) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits))
      (Lgamma.accurate Tgamma.logdTable Lgamma.logAccurateTable Lgamma.sinpiTable
        Lgamma.asymTable Lgamma.accurateTable Lgamma.dbTable sx).toBits := by
  have hpos : 0 < value sx.toBits := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨hxf, hxv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float sx hsx
  have hxv' : value sx.abs.toBits = value sx.toBits := by rw [hxv, abs_of_pos hpos]
  have hsn : ¬ sx < 0.0 := fun h => by
    have := (lt_test sx 0.0 _ 0 hsx c00.1 rfl c00.2).mp h
    linarith
  have h1015 : value sx.abs.toBits ≤ 2 ^ 1015 := by
    rw [hxv']; exact hhi.trans LgammaFastTop.x1_le_1015
  have h800 : 2 ^ 800 ≤ value sx.abs.toBits := by rw [hxv']; exact hlo
  rw [Lgamma.accurate.eq_1]
  refine (?_ : (fun r : Float =>
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits)) r.toBits) _)
  spec_step (TopPair (GammaBasic.lgamma (value sx.toBits)))
  swap
  · intro fh fl hP
    exact tail_top hDb sx hsx fh fl hP
  have hn100 : ¬ sx.abs < Float.ofBits 4156822456062967808 := by
    rw [lt_test _ _ _ (1 / 2 ^ 100) hxf (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide)) hxv'
      (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
        show PolyBound.ratOfWord 4156822456062967808 = 1 / 2 ^ 100 by decide +kernel]
          norm_num)]
    exact not_lt.mpr (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 ≤ 2 ^ 800)])
  acc_step
  · intro h; exact absurd h hn100
  intro _
  have hnq : ¬ sx.abs < 0.25 := by
    rw [lt_test _ _ _ _ hxf c025.1 hxv' c025.2]
    exact not_lt.mpr (by linarith [(by norm_num : (1 : ℝ) / 4 ≤ 2 ^ 800)])
  acc_step
  · intro h; exact absurd h hnq
  intro _
  spec_step (TopTriple (GammaBasic.lgamma (value sx.toBits)))
  swap
  · intro fh fl fll hW
    spec_step (TopTriple (GammaBasic.lgamma (value sx.toBits)))
    swap
    · intro a b c hR
      acc_step; intro h1 l1 e1
      acc_step; intro l2 ll2 e2
      acc_step; intro h3 l3 e3
      acc_step; intro l4 ll4 e4
      acc_step; intro f5 e5 he5
      exact norm_top _ a b c hR h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 _
    acc_step
    · intro h; exact absurd h hsn
    intro _
    exact hW
  have w05 := win_top sx.abs 0.5 (1 / 2) hxf c05.1 c05.2 (by norm_num) (by norm_num) h800 h1015
  have w25 := win_top sx.abs 2.5 (5 / 2) hxf c25.1 c25.2 (by norm_num) (by norm_num) h800 h1015
  have w35 := win_top sx.abs 3.5 (7 / 2) hxf c35.1 c35.2 (by norm_num) (by norm_num) h800 h1015
  have w10 := win_top sx.abs 1.0 1 hxf c10.1 c10.2 (by norm_num) (by norm_num) h800 h1015
  have w15 := win_top sx.abs 1.5 (3 / 2) hxf c15.1 c15.2 (by norm_num) (by norm_num) h800 h1015
  have w20 := win_top sx.abs 2.0 2 hxf c20.1 c20.2 (by norm_num) (by norm_num) h800 h1015
  have w30 := win_top sx.abs 3.0 3 hxf c30.1 c30.2 (by norm_num) (by norm_num) h800 h1015
  acc_step
  · intro h; exact absurd h w05
  intro _
  acc_step
  · intro h; exact absurd h w25
  intro _
  acc_step
  · intro h; exact absurd h w35
  intro _
  acc_step
  · intro h; exact absurd h w10
  intro _
  acc_step
  · intro h; exact absurd h w15
  intro _
  acc_step
  · intro h; exact absurd h w20
  intro _
  acc_step
  · intro h; exact absurd h w30
  intro _
  acc_step
  intro xh xl hxx
  rw [if_neg hsn] at hxx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxx
  have h := asym_top hF hLA hAF sx.abs hxf h800 (by rw [hxv']; exact hhi)
  rwa [hxv'] at h

#print axioms norm_top
#print axioms sum_within_top
#print axioms tail_top
#print axioms asym_top
#print axioms accurate_top

end Library.Numerics.Float64.Lgamma.LgammaAccTop
