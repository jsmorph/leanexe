import Verified.Examples.LgammaAccNegLarge
import Verified.Examples.LgammaAccTests

/-!
**The accurate path of `lgamma`** within one step of `log |Γ x|` (`accurate_within`), for every
non-integer double `x` with `|x| ≤ 2^800` other than the 14 ends of the windows, `±1/4` to `±13/4`
in steps of `1/2`, given `2^-1000 ≤ |log |Γ x|| ≤ 2^1020`.  The proof walks the code's block with
`acc_step` and `spec_step`: the branches below `1/4` give `LgammaAccTail.AccPair` through
`LgammaAccLow`, the windows and Stirling's series give the triple of `LgammaAccPos.PosSpec` at a
positive argument and of `NegW` at a negative one, the reflection and the renormalization give
`AccPair` (`LgammaAccNeg.ready_pair`), and `tail_within` finishes.  `past_windows` places the
argument of Stirling's series at or above 15/4.
-/

namespace Verified.Examples.LgammaAccPath
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma TgammaDD LgammaAccWin LgammaAccWinSmall
  LgammaLogAccKern LgammaAccTail LgammaAccWalk LgammaAccTests LgammaAccPos LgammaAccNeg
  LgammaAccNegLarge LgammaWalk

set_option exponentiation.threshold 4096

/-- The triple of `log Γ (1 + |x|)` at a negative argument, from a window or from Stirling's
series. -/
def NegW (x : Float) (r : Float × Float × Float) : Prop :=
  (value x.toBits < 21 / 2 ∧ NegSmall (GammaBasic.lgamma (1 + value x.toBits)) r) ∨
    (21 / 2 ≤ value x.toBits ∧
      NegLarge (GammaBasic.lgamma (1 + value x.toBits)) (1 + value x.toBits) r)

/-- Outside the seven windows and their ends, from 1/4 on, the argument is at least 15/4. -/
theorem past_windows (t : ℝ) (h14 : 1 / 4 ≤ t)
    (n1 : ¬ (1 / 2 - 1 / 4 < t ∧ t < 1 / 2 + 1 / 4)) (n2 : ¬ (5 / 2 - 1 / 4 < t ∧ t < 5 / 2 + 1 / 4))
    (n3 : ¬ (7 / 2 - 1 / 4 < t ∧ t < 7 / 2 + 1 / 4)) (n4 : ¬ (1 - 1 / 4 < t ∧ t < 1 + 1 / 4))
    (n5 : ¬ (3 / 2 - 1 / 4 < t ∧ t < 3 / 2 + 1 / 4)) (n6 : ¬ (2 - 1 / 4 < t ∧ t < 2 + 1 / 4))
    (n7 : ¬ (3 - 1 / 4 < t ∧ t < 3 + 1 / 4))
    (hends : ∀ k : ℕ, k < 7 → t ≠ (2 * k + 1) / 4) : 15 / 4 ≤ t := by
  by_contra hlt
  push Not at hlt
  have h0 := hends 0 (by norm_num)
  have h1 := hends 1 (by norm_num)
  have h2 := hends 2 (by norm_num)
  have h3 := hends 3 (by norm_num)
  have h4 := hends 4 (by norm_num)
  have h5 := hends 5 (by norm_num)
  have h6 := hends 6 (by norm_num)
  norm_num at h0 h1 h2 h3 h4 h5 h6
  simp only [not_and_or, not_lt] at n1 n2 n3 n4 n5 n6 n7
  rcases n1 with n1 | n1 <;> rcases n4 with n4 | n4 <;> rcases n5 with n5 | n5 <;>
    rcases n6 with n6 | n6 <;> rcases n2 with n2 | n2 <;> rcases n7 with n7 | n7 <;>
    rcases n3 with n3 | n3 <;>
    first
    | linarith
    | exact h0 (by linarith)
    | exact h1 (by linarith)
    | exact h2 (by linarith)
    | exact h3 (by linarith)
    | exact h4 (by linarith)
    | exact h5 (by linarith)
    | exact h6 (by linarith)

/-- The branches below `1/4` give `AccPair`. -/
theorem low_acc (L : ℝ) (sx : Float) (p : Float × Float) (hp : LgammaAccLow.LowSpec L p) :
    AccPair L sx p := by
  obtain ⟨f1, f2, h1, -, he⟩ := hp
  refine ⟨f1, f2, fun h => by linarith, fun _ => ?_⟩
  rw [abs_sub_comm]
  refine he.trans ?_
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)


set_option maxHeartbeats 16000000 in
/-- **The accurate path** within one step of `log |Γ x|`. -/
theorem accurate_within (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (hAF : LgammaApprox.AsymFact)
    (hCF : LgammaApprox.CancelFact) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (hDb : LgammaApprox.DbFact)
    (sx : Float) (hsx : Finite sx.toBits) (hint : ∀ n : ℤ, value sx.toBits ≠ n)
    (hbig : |value sx.toBits| ≤ 2 ^ 800)
    (hends : ∀ k : ℕ, k < 7 → |value sx.toBits| ≠ (2 * k + 1) / 4)
    (hL1 : 1 / 2 ^ 1000 ≤ |GammaBasic.lgamma (value sx.toBits)|)
    (hL2 : |GammaBasic.lgamma (value sx.toBits)| ≤ 2 ^ 1020) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits))
      (Lgamma.accurate Tgamma.logdTable Lgamma.logAccurateTable Lgamma.sinpiTable
        Lgamma.asymTable Lgamma.accurateTable Lgamma.dbTable sx).toBits := by
  obtain ⟨hxf, hxv⟩ := TgammaFloor.abs_float sx hsx
  have h0 : value sx.toBits ≠ 0 := fun h => hint 0 (by rw [h]; norm_num)
  have hneg_iff : sx < 0.0 ↔ value sx.toBits < 0 := lt_test sx 0.0 _ 0 hsx c00.1 rfl c00.2
  have hpos_iff : sx > 0.0 ↔ 0 < value sx.toBits := lt_test 0.0 sx 0 _ c00.1 hsx c00.2 rfl
  rw [Lgamma.accurate.eq_1]
  refine (?_ : (fun r : Float =>
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits)) r.toBits) _)
  spec_step (AccPair (GammaBasic.lgamma (value sx.toBits)) sx)
  swap
  · intro fh fl hP
    exact tail_within hF hRF hRM hDb sx hsx hL1 hL2 fh fl hP
  have hw100 : sx.abs < Float.ofBits 4156822456062967808 ↔ |value sx.toBits| < 1 / 2 ^ 100 := by
    apply lt_test _ _ _ _ hxf (TgammaWords.ofBits_finite _ (by decide)) hxv
    rw [TgammaWords.ofBits_value _ (by decide),
      show PolyBound.ratOfWord 4156822456062967808 = 1 / 2 ^ 100 by decide +kernel]
    norm_num
  acc_step
  · -- below `2^-100`
    intro h100
    acc_step; intro lh ll lll hT
    acc_step; intro a b hab
    acc_step; intro c d hcd
    acc_step; intro f e he
    acc_step; intro p54 hp54
    subst p54
    exact low_acc _ sx _ (LgammaAccLow.tiny_spec hF hLA sx hsx h0 (hw100.mp h100) lh ll lll hT
      a b hab c d hcd _)
  intro hn100
  have h100 : 1 / 2 ^ 100 ≤ |value sx.toBits| := by
    by_contra h; push Not at h; exact hn100 (hw100.mpr h)
  have hq_iff : sx.abs < 0.25 ↔ |value sx.toBits| < 1 / 4 := lt_test _ _ _ _ hxf c025.1 hxv c025.2
  acc_step
  · -- from `2^-100` to `1/4`
    intro hq
    acc_step; intro p0 p1 hP
    acc_step; intro m0 m1 hM
    acc_step; intro lh ll lll hT
    acc_step; intro s0 s1 hS'
    acc_step; intro u0 u1 hU
    acc_step; intro v0 v1 hV
    acc_step; intro f e he
    acc_step; intro p54 hp54
    subst p54
    exact low_acc _ sx _ (LgammaAccLow.low_spec hF hLA hAP sx hsx h100 (hq_iff.mp hq) p0 p1 hP
      m0 m1 hM lh ll lll hT s0 s1 hS' u0 u1 hU v0 v1 hV _)
  intro hnq
  have hx14 : 1 / 4 ≤ value sx.abs.toBits := by
    rw [hxv]; by_contra h; push Not at h; exact hnq (hq_iff.mpr h)
  have hxb : value sx.abs.toBits ≤ 2 ^ 1000 := by
    rw [hxv]; linarith [(by norm_num : (2 : ℝ) ^ 800 ≤ 2 ^ 1000)]
  have hends' : ∀ k : ℕ, k < 7 → value sx.abs.toBits ≠ (2 * k + 1) / 4 := by
    intro k hk; rw [hxv]; exact hends k hk
  have w05 := win_test sx.abs 0.5 (1 / 2) hxf c05.1 c05.2 (Or.inl rfl) (by norm_num) hx14 hxb
  have w25 := win_test sx.abs 2.5 (5 / 2) hxf c25.1 c25.2 (Or.inr (by norm_num)) (by norm_num)
    hx14 hxb
  have w35 := win_test sx.abs 3.5 (7 / 2) hxf c35.1 c35.2 (Or.inr (by norm_num)) (by norm_num)
    hx14 hxb
  have w10 := win_test sx.abs 1.0 1 hxf c10.1 c10.2 (Or.inr (by norm_num)) (by norm_num) hx14 hxb
  have w15 := win_test sx.abs 1.5 (3 / 2) hxf c15.1 c15.2 (Or.inr (by norm_num)) (by norm_num)
    hx14 hxb
  have w20 := win_test sx.abs 2.0 2 hxf c20.1 c20.2 (Or.inr (by norm_num)) (by norm_num) hx14 hxb
  have w30 := win_test sx.abs 3.0 3 hxf c30.1 c30.2 (Or.inr (by norm_num)) (by norm_num) hx14 hxb
  have hE : Emid ≤ 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 := by unfold Emid; norm_num
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · --------------------------------------------------------------- negative arguments
    have hxv' : value sx.abs.toBits = -value sx.toBits := by rw [hxv, abs_of_neg hneg]
    have hsn : sx < 0.0 := hneg_iff.mpr hneg
    have hsp : ¬ sx > 0.0 := fun h => by linarith [hpos_iff.mp h]
    spec_step (NegW sx.abs)
    swap
    · intro fh fl fll hW
      spec_step (NormReady (GammaBasic.lgamma (value sx.toBits)) sx)
      swap
      · intro a b c hR
        acc_step; intro h1 l1 e1
        acc_step; intro l2 ll2 e2
        acc_step; intro h3 l3 e3
        acc_step; intro l4 ll4 e4
        acc_step; intro f5 e5 he5
        exact ready_pair _ sx a b c hR h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 _
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro phi hphi
      acc_step; intro sh sl hA
      acc_step; intro lh ll lll hT
      acc_step; intro ll2 hll2
      acc_step; intro a1 b1 hS1
      acc_step; intro h2 l2 hP2
      acc_step; intro a3 b3 hS3
      rcases hW with ⟨hs, hsm⟩ | ⟨hl, hlg⟩
      · rw [hxv] at hsm hs
        exact small_ready hF hS hSA hLA sx hsx hneg hint
          (by rw [abs_of_neg hneg] at hs; linarith)
          (by rw [hxv'] at hx14; linarith) fh fl fll hsm phi hphi
          sh sl hA lh ll lll hT ll2 hll2 a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
      · rw [hxv] at hlg hl
        exact large_ready hF hS hSA hLA hCF sx hsx hint
          (by rw [abs_of_neg hneg] at hl; linarith)
          (by have := (abs_le.mp hbig).1; linarith) fh fl fll hlg phi hphi
          sh sl hA lh ll lll hT ll2 hll2 a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
    -- the windows and Stirling's series at a negative argument
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w05.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step
      · intro h; exact absurd h hsp
      intro _
      have hwin := w05_neg hF hAP sx.abs hxf c1 c2 p0 p1 hP
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin hE (by norm_num) (by norm_num)⟩
    intro hn05
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w25.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step; intro lh ll lll hT
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro mh ml mll hM
      acc_step; intro a4 b4 hS4
      acc_step; intro h5 l5 hP5
      acc_step; intro a6 b6 hS6
      have hwin := w25_neg hF hLA hAP sx.abs hxf c1 c2 p0 p1 hP lh ll lll hT a1 b1 hS1 h2' l2 hP2
        a3 b3 hS3 mh ml mll hM a4 b4 hS4 h5 l5 hP5 a6 b6 hS6
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin hE (by norm_num) (by norm_num)⟩
    intro hn25
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w35.mp hw
      norm_num at c1 c2
      acc_step; intro bh bl bll hTb
      acc_step; intro ah al all hTa
      acc_step; intro s1 t1 hS1
      acc_step; intro s0 u hP0
      acc_step; intro s1' s2 hS2
      acc_step; intro p0 p1 hP
      acc_step; intro a1 b1 hS3
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS4
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro mh ml mll hM
      acc_step; intro a4 b4 hS5
      acc_step; intro h5 l5 hP5
      acc_step; intro a6 b6 hS6
      have hwin := w35_neg hF hLA hAP sx.abs hxf c1 c2 bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u
        hP0 s1' s2 hS2 p0 p1 hP a1 b1 hS3 h2' l2 hP2 a3 b3 hS4 mh ml mll hM a4 b4 hS5 h5 l5 hP5
        a6 b6 hS6
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin hE (by norm_num) (by norm_num)⟩
    intro hn35
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w10.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro lh ll lll hT
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      have hwin := w1_neg hF hLA hAP sx.abs hxf c1 c2 p0 p1 hP m0 m1 hM lh ll lll hT a1 b1 hS1
        h2' l2 hP2 a3 b3 hS3
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin (by norm_num) (by norm_num)
        (by norm_num)⟩
    intro hn10
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w15.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro lh ll lll hT
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      have hwin := w15_neg hF hLA hAP sx.abs hxf c1 c2 p0 p1 hP lh ll lll hT a1 b1 hS1
        h2' l2 hP2 a3 b3 hS3
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin hE (by norm_num) (by norm_num)⟩
    intro hn15
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w20.mp hw
      norm_num at c1 c2
      acc_step; intro lh ll lll hT
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro mh ml mll hM2
      acc_step; intro a4 b4 hS4
      acc_step; intro h5 l5 hP5
      acc_step; intro a6 b6 hS6
      have hwin := w2_neg hF hLA hAP sx.abs hxf c1 c2 lh ll lll hT p0 p1 hP m0 m1 hM a1 b1 hS1
        h2' l2 hP2 a3 b3 hS3 mh ml mll hM2 a4 b4 hS4 h5 l5 hP5 a6 b6 hS6
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin (by norm_num) (by norm_num)
        (by norm_num)⟩
    intro hn20
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w30.mp hw
      norm_num at c1 c2
      acc_step; intro bh bl bll hTb
      acc_step; intro ah al all hTa
      acc_step; intro s1 t1 hS1
      acc_step; intro s0 u hP0
      acc_step; intro s1' s2 hS2
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step; intro a1 b1 hS3
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS4
      acc_step
      swap
      · intro h; exact absurd hsn h
      intro _
      acc_step; intro mh ml mll hM2
      acc_step; intro a4 b4 hS5
      acc_step; intro h5 l5 hP5
      acc_step; intro a6 b6 hS6
      have hwin := w3_neg hF hLA hAP sx.abs hxf c1 c2 bh bl bll hTb ah al all hTa s1 t1 hS1 s0 u
        hP0 s1' s2 hS2 p0 p1 hP m0 m1 hM a1 b1 hS3 h2' l2 hP2 a3 b3 hS4 mh ml mll hM2 a4 b4 hS5
        h5 l5 hP5 a6 b6 hS6
      rw [add_comm] at hwin
      exact Or.inl ⟨by linarith, win_small _ _ _ _ _ hwin (by norm_num) (by norm_num)
        (by norm_num)⟩
    intro hn30
    -- Stirling's series at `|x| + 1`
    have h154 := past_windows _ hx14 (fun h => hn05 (w05.mpr h)) (fun h => hn25 (w25.mpr h))
      (fun h => hn35 (w35.mpr h)) (fun h => hn10 (w10.mpr h)) (fun h => hn15 (w15.mpr h))
      (fun h => hn20 (w20.mpr h)) (fun h => hn30 (w30.mpr h)) hends'
    acc_step
    intro xh xl hxx
    rw [if_pos hsn] at hxx
    rcases lt_or_ge (value sx.abs.toBits) (21 / 2) with h21 | h21
    · exact Or.inl ⟨h21, LgammaAccNegAsym.asym_small hF hLA hAF sx.abs hxf h154 h21 xh xl hxx⟩
    · exact Or.inr ⟨h21, asym_large hF hLA hAF sx.abs hxf h21 (by rw [hxv]; exact hbig) xh xl hxx⟩
  · --------------------------------------------------------------- positive arguments
    have hxv' : value sx.abs.toBits = value sx.toBits := by rw [hxv, abs_of_pos hpos]
    have hsn : ¬ sx < 0.0 := fun h => by linarith [hneg_iff.mp h]
    have hsp : sx > 0.0 := hpos_iff.mpr hpos
    spec_step (PosSpec (GammaBasic.lgamma (value sx.abs.toBits)))
    swap
    · intro fh fl fll hW
      spec_step (NormReady (GammaBasic.lgamma (value sx.toBits)) sx)
      swap
      · intro a b c hR
        acc_step; intro h1 l1 e1
        acc_step; intro l2 ll2 e2
        acc_step; intro h3 l3 e3
        acc_step; intro l4 ll4 e4
        acc_step; intro f5 e5 he5
        exact ready_pair _ sx a b c hR h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 _
      acc_step
      · intro h; exact absurd h hsn
      intro _
      have := pos_ready _ sx _ hW
      rwa [hxv'] at this
    have hx1 : value sx.abs.toBits ≠ 1 := by
      rw [hxv']; exact fun h => hint 1 (by rw [h]; norm_num)
    have hx2 : value sx.abs.toBits ≠ 2 := by
      rw [hxv']; exact fun h => hint 2 (by rw [h]; norm_num)
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w05.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step
      swap
      · intro h; exact absurd hsp h
      intro _
      acc_step; intro lh ll lll hT
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      exact win_pos _ _ _ _ _ (w05_pos hF hLA hAP sx.abs hxf c1 c2 p0 p1 hP lh ll lll hT a1 b1 hS1
        h2' l2 hP2 a3 b3 hS3) (LgammaAccLower.pos_quarter _ c1 c2) hE (by norm_num) (by norm_num)
    intro hn05
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w25.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step; intro lh ll lll hT
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact win_pos _ _ _ _ _ (w25_pos hF hLA hAP sx.abs hxf c1 c2 p0 p1 hP lh ll lll hT a1 b1 hS1
        h2' l2 hP2 a3 b3 hS3) (LgammaAccLower.pos_large _ (by linarith)) (by norm_num)
        (by norm_num) (by norm_num)
    intro hn25
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w35.mp hw
      norm_num at c1 c2
      acc_step; intro bh bl bll hTb
      acc_step; intro ah al all hTa
      acc_step; intro s1 t1 hS1
      acc_step; intro s0 u hP0
      acc_step; intro s1' s2 hS2
      acc_step; intro p0 p1 hP
      acc_step; intro a1 b1 hS3
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS4
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact win_pos _ _ _ _ _ (w35_pos hF hLA hAP sx.abs hxf c1 c2 bh bl bll hTb ah al all hTa
        s1 t1 hS1 s0 u hP0 s1' s2 hS2 p0 p1 hP a1 b1 hS3 h2' l2 hP2 a3 b3 hS4)
        (LgammaAccLower.pos_large _ (by linarith)) (by norm_num) (by norm_num) (by norm_num)
    intro hn35
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w10.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact rel_pos _ _ _ (w1_pos hF hAP sx.abs hxf c1 c2 hx1 p0 p1 hP m0 m1 hM) (by norm_num)
        (by norm_num) (by rw [hxv']; exact hL1)
    intro hn10
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w15.mp hw
      norm_num at c1 c2
      acc_step; intro p0 p1 hP
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact win_pos _ _ _ _ _ (w15_pos hF hAP sx.abs hxf c1 c2 p0 p1 hP)
        (LgammaAccLower.pos_mid _ c1 c2) hE (by norm_num) (by norm_num)
    intro hn15
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w20.mp hw
      norm_num at c1 c2
      acc_step; intro lh ll lll hT
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step; intro a1 b1 hS1
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS3
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact rel_pos _ _ _ (w2_pos hF hLA hAP sx.abs hxf c1 c2 hx2 lh ll lll hT p0 p1 hP m0 m1 hM
        a1 b1 hS1 h2' l2 hP2 a3 b3 hS3) (by norm_num) (by norm_num) (by rw [hxv']; exact hL1)
    intro hn20
    acc_step
    · intro hw
      obtain ⟨c1, c2⟩ := w30.mp hw
      norm_num at c1 c2
      acc_step; intro bh bl bll hTb
      acc_step; intro ah al all hTa
      acc_step; intro s1 t1 hS1
      acc_step; intro s0 u hP0
      acc_step; intro s1' s2 hS2
      acc_step; intro p0 p1 hP
      acc_step; intro m0 m1 hM
      acc_step; intro a1 b1 hS3
      acc_step; intro h2' l2 hP2
      acc_step; intro a3 b3 hS4
      acc_step
      · intro h; exact absurd h hsn
      intro _
      exact win_pos _ _ _ _ _ (w3_pos hF hLA hAP sx.abs hxf c1 c2 bh bl bll hTb ah al all hTa
        s1 t1 hS1 s0 u hP0 s1' s2 hS2 p0 p1 hP m0 m1 hM a1 b1 hS3 h2' l2 hP2 a3 b3 hS4).1
        (LgammaAccLower.pos_large _ (by linarith)) (by norm_num) (by norm_num) (by norm_num)
    intro hn30
    have h154 := past_windows _ hx14 (fun h => hn05 (w05.mpr h)) (fun h => hn25 (w25.mpr h))
      (fun h => hn35 (w35.mpr h)) (fun h => hn10 (w10.mpr h)) (fun h => hn15 (w15.mpr h))
      (fun h => hn20 (w20.mpr h)) (fun h => hn30 (w30.mpr h)) hends'
    acc_step
    intro xh xl hxx
    rw [if_neg hsn] at hxx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxx
    exact asym_pos hF hLA hAF sx.abs hxf h154 (by rw [hxv']; linarith [(abs_le.mp hbig).2,
      (by norm_num : (2 : ℝ) ^ 800 ≤ 2 ^ 801)])

end Verified.Examples.LgammaAccPath
