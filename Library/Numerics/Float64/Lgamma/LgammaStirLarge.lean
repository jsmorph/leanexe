import LeanExe.ProofKit.GammaFitsX
import Library.Numerics.Float64.Lgamma.LgammaStirFast

/-!
The Stirling fits of `cr_lgamma` from 16 on (`lgamma.c`, commit `ff2f71f6`): the fast path's fit
(`Lgamma.mainTable` words 397 to 405) within `7 · 10 ^ -20` of `lgamma`, relative, for `x ≥ 16`
(`fast_large`), and the accurate path's first fit (`Lgamma.asymTable` words 0 to 15) within
`2 ^ -63`, relative, for `x ≥ 48 - 2 ^ -40` (`asym0_large`).  On each range `[X, 1/lo]` the
kernel check `fitRangeOk` bounds the fit's error (`GammaFitsX.fit_range`), and a Taylor model of
`lgamma` at `X` with the monotony of `lgamma` above 2 makes the bound relative (`range_rel`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaStirLarge

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaFitsX
  GammaThresholds Library.Numerics.Float64.Tgamma.TgammaFactsBase LgammaStirFast

/-- The accurate path's fit from 48 on: the constant and the coefficients. -/
def c0Asym0 : ℚ := q Lgamma.asymTable 0 + q Lgamma.asymTable 1

def pAsym0 : List ℚ := ddCoeffs Lgamma.asymTable 2 7

/-- One range `[X, 1/lo]`: the fit within `ε` of `lgamma` there, and `lgamma X ≥ Lq - e`, give
the relative bound `rel`. -/
theorem range_rel (n : ℕ) (ly lp : LogData) (lo X C0 Lq e ε rel : ℚ) (P : List ℚ) (depth : ℕ)
    (hf : fitRangeOk lo X C0 P ε depth = true)
    (hp : lgammaDiffOk cfgZ ⟨X, n, log2Lo, log2Hi, ly, lp⟩ (.const Lq) e 0 = true)
    (hε : (ε : ℝ) ≤ rel * (Lq - e)) (hrel : (0 : ℝ) ≤ rel) {x : ℝ} (hx : (X : ℝ) ≤ x)
    (hlo : (lo : ℝ) * x ≤ 1) : |lgamma x - fit C0 P x| ≤ rel * lgamma x := by
  have h1 := fit_range lo X C0 P ε depth hf hx hlo
  have h2 := lgammaDiffOk_sound cfgZ ⟨X, n, log2Lo, log2Hi, ly, lp⟩ (.const Lq) e 0 cfgZ_pi hp
    (t := 0) (by simp [cfgZ])
  simp only [TaylorModel.Expr.eval, add_zero] at h2
  have hX2 : (2 : ℝ) ≤ X := by
    simp only [fitRangeOk, Bool.and_eq_true, decide_eq_true_eq] at hf
    have : (16 : ℝ) ≤ X := by exact_mod_cast hf.1.1
    linarith
  have hm : lgamma X ≤ lgamma x := lgamma_mono hX2 hx
  have h2' := (abs_le.mp h2).1
  calc |lgamma x - fit C0 P x| ≤ ε := h1
    _ ≤ rel * (Lq - e) := hε
    _ ≤ rel * lgamma x := mul_le_mul_of_nonneg_left (by linarith) hrel

theorem rf_0 :
    fitRangeOk (1 / 24) (16) c0Fast pFast (604408439 / 2 ^ 88) 1 = true := by
  decide +kernel

theorem pf_0 : lgammaDiffOk cfgZ ⟨(16), 0, log2Lo, log2Hi,
      ⟨4,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (251294296416348363 / 2 ^ 53)) (251294296416348363 / 2 ^ 103) 0 = true := by
  decide +kernel

theorem rf_1 :
    fitRangeOk (1 / 32) (24) c0Fast pFast (559002237 / 2 ^ 87) 1 = true := by
  decide +kernel

theorem pf_1 : lgammaDiffOk cfgZ ⟨(24), 0, log2Lo, log2Hi,
      ⟨5,
          (-1458721407273604283815534425793 / 5070602400912917605986812821504),
          (-5834885629094417135262137703169 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (1859326438854509703 / 2 ^ 55)) (1859326438854509703 / 2 ^ 105) 0 = true := by
  decide +kernel

theorem rf_2 :
    fitRangeOk (1 / 48) (32) c0Fast pFast (52868315 / 2 ^ 83) 0 = true := by
  decide +kernel

theorem pf_2 : lgammaDiffOk cfgZ ⟨(32), 0, log2Lo, log2Hi,
      ⟨5,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (21981006805952769 / 2 ^ 48)) (21981006805952769 / 2 ^ 98) 0 = true := by
  decide +kernel

theorem rf_3 :
    fitRangeOk (1 / 64) (48) c0Fast pFast (740921859 / 2 ^ 86) 0 = true := by
  decide +kernel

theorem pf_3 : lgammaDiffOk cfgZ ⟨(48), 0, log2Lo, log2Hi,
      ⟨6,
          (-1458721407273604283815534425793 / 5070602400912917605986812821504),
          (-5834885629094417135262137703169 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (1232209381385464701 / 2 ^ 53)) (1232209381385464701 / 2 ^ 103) 0 = true := by
  decide +kernel

theorem rf_4 :
    fitRangeOk (1 / 80) (64) c0Fast pFast (1088663979 / 2 ^ 86) 0 = true := by
  decide +kernel

theorem pf_4 : lgammaDiffOk cfgZ ⟨(64), 0, log2Lo, log2Hi,
      ⟨6,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (452632741216901207 / 2 ^ 51)) (452632741216901207 / 2 ^ 101) 0 = true := by
  decide +kernel

theorem rf_5 :
    fitRangeOk (1 / 96) (80) c0Fast pFast (1458477265 / 2 ^ 86) 0 = true := by
  decide +kernel

theorem pf_5 : lgammaDiffOk cfgZ ⟨(80), 0, log2Lo, log2Hi,
      ⟨6,
          (2262944454084133636698307228415 / 10141204801825835211973625643008),
          (4525888908168267273396614456833 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (1212779287035324723 / 2 ^ 52)) (1212779287035324723 / 2 ^ 102) 0 = true := by
  decide +kernel

theorem rf_6 :
    fitRangeOk (1 / 128) (96) c0Fast pFast (1845850157 / 2 ^ 86) 0 = true := by
  decide +kernel

theorem pf_6 : lgammaDiffOk cfgZ ⟨(96), 0, log2Lo, log2Hi,
      ⟨7,
          (-1458721407273604283815534425793 / 5070602400912917605986812821504),
          (-5834885629094417135262137703169 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (767447286066392057 / 2 ^ 51)) (767447286066392057 / 2 ^ 101) 0 = true := by
  decide +kernel

theorem rf_7 :
    fitRangeOk (1 / 192) (128) c0Fast pFast (1331123707 / 2 ^ 85) 0 = true := by
  decide +kernel

theorem pf_7 : lgammaDiffOk cfgZ ⟨(128), 0, log2Lo, log2Hi,
      ⟨7,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (2213759926251127287 / 2 ^ 52)) (2213759926251127287 / 2 ^ 102) 0 = true := by
  decide +kernel

theorem rf_8 :
    fitRangeOk (1 / 256) (192) c0Fast pFast (276123887 / 2 ^ 82) 0 = true := by
  decide +kernel

theorem pf_8 : lgammaDiffOk cfgZ ⟨(192), 0, log2Lo, log2Hi,
      ⟨8,
          (-1458721407273604283815534425793 / 5070602400912917605986812821504),
          (-5834885629094417135262137703169 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (918430034113330691 / 2 ^ 50)) (918430034113330691 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem rf_9 :
    fitRangeOk (0) (256) c0Fast pFast (393238651 / 2 ^ 82) 0 = true := by
  decide +kernel

theorem pf_9 : lgammaDiffOk cfgZ ⟨(256), 0, log2Lo, log2Hi,
      ⟨8,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (1307971546427156285 / 2 ^ 50)) (1307971546427156285 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem ra_0 :
    fitRangeOk (0) (52776558133247 / 2 ^ 40) c0Asym0 pAsym0 (1147584413 / 2 ^ 86) 0 = true := by
  decide +kernel

theorem pa_0 : lgammaDiffOk cfgZ ⟨(52776558133247 / 2 ^ 40), 0, log2Lo, log2Hi,
      ⟨5,
          (4111904701319155867730938309817 / 10141204801825835211973625643008),
          (8223809402638311735461876619637 / 20282409603651670423947251286016)⟩,
      ⟨0,
          (-1 / 20282409603651670423947251286016),
          (1 / 20282409603651670423947251286016)⟩⟩
    (.const (616104690692716537 / 2 ^ 52)) (616104690692716537 / 2 ^ 102) 0 = true := by
  decide +kernel

/-- The fast path's fit within `7 · 10 ^ -20` of `lgamma`, relative, from 16 on. -/
theorem fast_large : ∀ x : ℝ, (16 : ℝ) ≤ x →
    |lgamma x - fit c0Fast pFast x| ≤ (7 / 10 ^ 20) * lgamma x := by
  intro x hx
  rcases le_or_gt x (24 : ℝ) with h0 | h0
  · have h := range_rel 0 _ _ (1 / 24) (16) c0Fast (251294296416348363 / 2 ^ 53)
      (251294296416348363 / 2 ^ 103) (604408439 / 2 ^ 88) (7 / 10 ^ 20) pFast 1 rf_0 pf_0
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (32 : ℝ) with h1 | h1
  · have h := range_rel 0 _ _ (1 / 32) (24) c0Fast (1859326438854509703 / 2 ^ 55)
      (1859326438854509703 / 2 ^ 105) (559002237 / 2 ^ 87) (7 / 10 ^ 20) pFast 1 rf_1 pf_1
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (48 : ℝ) with h2 | h2
  · have h := range_rel 0 _ _ (1 / 48) (32) c0Fast (21981006805952769 / 2 ^ 48)
      (21981006805952769 / 2 ^ 98) (52868315 / 2 ^ 83) (7 / 10 ^ 20) pFast 0 rf_2 pf_2
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (64 : ℝ) with h3 | h3
  · have h := range_rel 0 _ _ (1 / 64) (48) c0Fast (1232209381385464701 / 2 ^ 53)
      (1232209381385464701 / 2 ^ 103) (740921859 / 2 ^ 86) (7 / 10 ^ 20) pFast 0 rf_3 pf_3
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (80 : ℝ) with h4 | h4
  · have h := range_rel 0 _ _ (1 / 80) (64) c0Fast (452632741216901207 / 2 ^ 51)
      (452632741216901207 / 2 ^ 101) (1088663979 / 2 ^ 86) (7 / 10 ^ 20) pFast 0 rf_4 pf_4
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (96 : ℝ) with h5 | h5
  · have h := range_rel 0 _ _ (1 / 96) (80) c0Fast (1212779287035324723 / 2 ^ 52)
      (1212779287035324723 / 2 ^ 102) (1458477265 / 2 ^ 86) (7 / 10 ^ 20) pFast 0 rf_5 pf_5
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (128 : ℝ) with h6 | h6
  · have h := range_rel 0 _ _ (1 / 128) (96) c0Fast (767447286066392057 / 2 ^ 51)
      (767447286066392057 / 2 ^ 101) (1845850157 / 2 ^ 86) (7 / 10 ^ 20) pFast 0 rf_6 pf_6
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (192 : ℝ) with h7 | h7
  · have h := range_rel 0 _ _ (1 / 192) (128) c0Fast (2213759926251127287 / 2 ^ 52)
      (2213759926251127287 / 2 ^ 102) (1331123707 / 2 ^ 85) (7 / 10 ^ 20) pFast 0 rf_7 pf_7
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  rcases le_or_gt x (256 : ℝ) with h8 | h8
  · have h := range_rel 0 _ _ (1 / 256) (192) c0Fast (918430034113330691 / 2 ^ 50)
      (918430034113330691 / 2 ^ 100) (276123887 / 2 ^ 82) (7 / 10 ^ 20) pFast 0 rf_8 pf_8
      (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
    push_cast at h ⊢
    exact h
  have h := range_rel 0 _ _ (0) (256) c0Fast (1307971546427156285 / 2 ^ 50)
    (1307971546427156285 / 2 ^ 100) (393238651 / 2 ^ 82) (7 / 10 ^ 20) pFast 0 rf_9 pf_9
    (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
  push_cast at h ⊢
  exact h

/-- The accurate path's first fit within `2 ^ -63` of `lgamma`, relative, from
`48 - 2 ^ -40` on. -/
theorem asym0_large : ∀ x : ℝ, ((52776558133247 : ℝ) / 2 ^ 40) ≤ x →
    |lgamma x - fit c0Asym0 pAsym0 x| ≤ (1 / 2 ^ 63) * lgamma x := by
  intro x hx
  have h := range_rel 0 _ _ (0) (52776558133247 / 2 ^ 40) c0Asym0 (616104690692716537 / 2 ^ 52)
    (616104690692716537 / 2 ^ 102) (1147584413 / 2 ^ 86) (1 / 2 ^ 63) pAsym0 0 ra_0 pa_0
    (by norm_num) (by norm_num) (x := x) (by push_cast; linarith) (by push_cast; linarith)
  push_cast at h ⊢
  exact h

#print axioms fast_large
#print axioms asym0_large

end Library.Numerics.Float64.Lgamma.LgammaStirLarge
