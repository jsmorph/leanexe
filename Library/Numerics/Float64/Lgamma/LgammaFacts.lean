import Library.Numerics.Float64.Lgamma.LgammaApprox
import Library.Numerics.Float64.Lgamma.LgammaSmallFact
import Library.Numerics.Float64.Lgamma.LgammaPiecesA
import Library.Numerics.Float64.Lgamma.LgammaPiecesB
import Library.Numerics.Float64.Lgamma.LgammaPiecesC
import Library.Numerics.Float64.Lgamma.LgammaPiecesD
import Library.Numerics.Float64.Lgamma.LgammaPiecesE
import Library.Numerics.Float64.Lgamma.LgammaPiece4
import Library.Numerics.Float64.Lgamma.LgammaPiece10
import Library.Numerics.Float64.Lgamma.LgammaStirLarge
import Library.Numerics.Float64.Tgamma.TgammaLogTables
import Library.Numerics.Float64.Lgamma.LgammaSinpiTables
import Library.Numerics.Float64.Lgamma.LgammaAccSmall
import Library.Numerics.Float64.Lgamma.LgammaAccMid
import Library.Numerics.Float64.Lgamma.LgammaAsymMidA
import Library.Numerics.Float64.Lgamma.LgammaAsymMidB
import Library.Numerics.Float64.Lgamma.LgammaAsymMidC
import Library.Numerics.Float64.Lgamma.LgammaAsymLowA
import Library.Numerics.Float64.Lgamma.LgammaAsymLowB
import Library.Numerics.Float64.Lgamma.LgammaAsymLowC
import Library.Numerics.Float64.Lgamma.LgammaAsymLowD
import Library.Numerics.Float64.Lgamma.LgammaAsymLowE
import Library.Numerics.Float64.Lgamma.LgammaAsymLowF
import Library.Numerics.Float64.Lgamma.LgammaAsymLowG
import Library.Numerics.Float64.Lgamma.LgammaAsymLowH
import Library.Numerics.Float64.Lgamma.LgammaLogAcc
import Library.Numerics.Float64.Lgamma.LgammaSinpiAcc
import Library.Numerics.Float64.Lgamma.LgammaRootA
import Library.Numerics.Float64.Lgamma.LgammaRootB
import Library.Numerics.Float64.Lgamma.LgammaRootC
import Library.Numerics.Float64.Lgamma.LgammaRootD
import Library.Numerics.Float64.Lgamma.LgammaRootE
import Library.Numerics.Float64.Lgamma.LgammaRootF
import Library.Numerics.Float64.Lgamma.LgammaZerosA
import Library.Numerics.Float64.Lgamma.LgammaDb
import Library.Numerics.Float64.Lgamma.LgammaCancel

/-!
Proofs of the approximation statements of `LgammaApprox`, which the floating-point proof of
`Lgamma.lgammaR` takes as hypotheses.  Each statement follows from a theorem of the fact modules,
whose coefficient lists equal those of `LgammaApprox` by definition.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaFacts

open Real LeanExe.ProofKit PolyBound GammaBasic LgammaApprox

/-- The copies in `LgammaData`, which the checks of the divided differences read, are the port's
tables. -/
theorem mainTable_eq : LgammaData.mainTable = Lgamma.mainTable := rfl

theorem accurateTable_eq : LgammaData.accurateTable = Lgamma.accurateTable := rfl

theorem smallFact : SmallFact := LgammaSmallFact.small_fact

/-- The pieces other than 4 and 10 carry no factor. -/
theorem pieceApprox_plain (j : ℕ) (h4 : j ≠ 4) (h10 : j ≠ 10) (x : ℝ) :
    pieceApprox j x = eval (LgammaPieceBase.pieceP j) (x - LgammaPieceBase.off j) := by
  rw [pieceApprox, ite_eq_right h4, ite_eq_right h10, one_mul]
  rfl

theorem piece_weak {x : ℝ} {j : ℕ}
    (h : |GammaBasic.lgamma x - eval (LgammaPieceBase.pieceP j) (x - LgammaPieceBase.off j)| ≤
      LgammaPieceBase.εout * |GammaBasic.lgamma x|) (h4 : j ≠ 4) (h10 : j ≠ 10) :
    |GammaBasic.lgamma x - pieceApprox j x| ≤ 12 / 10 ^ 20 * |GammaBasic.lgamma x| := by
  rw [pieceApprox_plain j h4 h10]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  norm_num [LgammaPieceBase.εout]

theorem pieceFact : PieceFact := by
  intro j hj x h1 h2
  interval_cases j
  · exact piece_weak (LgammaPiecesA.piece0 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesA.piece1 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesA.piece2 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesA.piece3 x h1 h2) (by norm_num) (by norm_num)
  · rw [pieceApprox, ite_eq_left rfl]
    exact LgammaPiece4.piece4 x h1 h2
  · exact piece_weak (LgammaPiecesB.piece5 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesB.piece6 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesB.piece7 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesB.piece8 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesC.piece9 x h1 h2) (by norm_num) (by norm_num)
  · rw [pieceApprox, ite_eq_right (show (10 : ℕ) ≠ 4 by norm_num), ite_eq_left rfl]
    exact LgammaPiece10.piece10 x h1 h2
  · exact piece_weak (LgammaPiecesC.piece11 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesC.piece12 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesD.piece13 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesD.piece14 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesD.piece15 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesE.piece16 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesE.piece17 x h1 h2) (by norm_num) (by norm_num)
  · exact piece_weak (LgammaPiecesE.piece18 x h1 h2) (by norm_num) (by norm_num)

theorem stirFast_eq (x : ℝ) :
    GammaFits.fit LgammaStirFast.c0Fast LgammaStirFast.pFast x = stirFast x := by
  rw [GammaFits.fit, stirFast, one_div x, one_div (x ^ 2), inv_pow]
  rfl

theorem stirlingFact : StirlingFact := by
  intro x hx
  have hb : border 19 = 9120899923968 / 2 ^ 40 := by decide +kernel
  rw [hb] at hx
  push_cast at hx
  rw [← stirFast_eq]
  rcases le_or_gt x 16 with h16 | h16
  · exact LgammaStirFast.cover x (by linarith) (by norm_num; linarith)
  · exact LgammaStirLarge.fast_large x h16.le

theorem logFact : LogFact := by
  unfold LogFact
  exact ⟨Library.Numerics.Float64.Tgamma.TgammaLogTables.log_poly, Library.Numerics.Float64.Tgamma.TgammaLogTables.l1_close, Library.Numerics.Float64.Tgamma.TgammaLogTables.l2_close,
    Library.Numerics.Float64.Tgamma.TgammaLogTables.ln2_close⟩

theorem sinpiFact : SinpiFact := by
  unfold SinpiFact
  exact ⟨LgammaSinpiTables.stpi_close, LgammaSinpiTables.sin_kernel_fact,
    LgammaSinpiTables.cos_kernel_fact, LgammaSinpiTables.near_fact⟩

theorem accPolyFact : AccPolyFact := by
  unfold AccPolyFact
  exact ⟨LgammaAccSmall.acc_small, LgammaAccMid.acc_mid⟩

theorem asym_eq (C0 : ℚ) (P : List ℚ) (o n : ℕ) (hC : C0 = q Lgamma.asymTable o +
    q Lgamma.asymTable (o + 1)) (hP : P = ddCoeffs Lgamma.asymTable (o + 2) n) (x : ℝ) :
    GammaFits.fit C0 P x = asymAcc o n x := by
  rw [GammaFits.fit, asymAcc, one_div x, one_div (x ^ 2), inv_pow, hC, hP]

theorem asymFact : AsymFact := by
  unfold AsymFact
  refine ⟨fun x hx => ?_, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · rw [← asym_eq LgammaStirLarge.c0Asym0 LgammaStirLarge.pAsym0 0 7 rfl rfl]
    exact LgammaStirLarge.asym0_large x (by norm_num at hx ⊢; linarith)
  · rw [← asym_eq LgammaAsymMidA.c0Asym LgammaAsymMidA.pAsym 16 11 rfl rfl]
    rcases le_or_gt x (45 / 2 - 1 / 2 ^ 40) with hmid0 | hmid0
    · exact LgammaAsymMidA.cover x (by norm_num at h1 ⊢; linarith)
        (by norm_num at hmid0 ⊢; linarith)
    rcases le_or_gt x (71 / 2 - 1 / 2 ^ 40) with hmid1 | hmid1
    · rw [show LgammaAsymMidA.c0Asym = LgammaAsymMidB.c0Asym from rfl,
        show LgammaAsymMidA.pAsym = LgammaAsymMidB.pAsym from rfl]
      exact LgammaAsymMidB.cover x (by norm_num at hmid0 ⊢; linarith)
          (by norm_num at hmid1 ⊢; linarith)
    rw [show LgammaAsymMidA.c0Asym = LgammaAsymMidC.c0Asym from rfl,
      show LgammaAsymMidA.pAsym = LgammaAsymMidC.pAsym from rfl]
    exact LgammaAsymMidC.cover x (by norm_num at hmid1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  · rw [← asym_eq LgammaAsymLowA.c0Asym LgammaAsymLowA.pAsym 40 27 rfl rfl]
    rcases le_or_gt x (41 / 8 - 1 / 2 ^ 40) with hlow0 | hlow0
    · exact LgammaAsymLowA.cover x (by norm_num at h1 ⊢; linarith)
        (by norm_num at hlow0 ⊢; linarith)
    rcases le_or_gt x (13 / 2 - 1 / 2 ^ 40) with hlow1 | hlow1
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowB.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowB.pAsym from rfl]
      exact LgammaAsymLowB.cover x (by norm_num at hlow0 ⊢; linarith)
          (by norm_num at hlow1 ⊢; linarith)
    rcases le_or_gt x (63 / 8 - 1 / 2 ^ 40) with hlow2 | hlow2
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowC.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowC.pAsym from rfl]
      exact LgammaAsymLowC.cover x (by norm_num at hlow1 ⊢; linarith)
          (by norm_num at hlow2 ⊢; linarith)
    rcases le_or_gt x (37 / 4 - 1 / 2 ^ 40) with hlow3 | hlow3
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowD.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowD.pAsym from rfl]
      exact LgammaAsymLowD.cover x (by norm_num at hlow2 ⊢; linarith)
          (by norm_num at hlow3 ⊢; linarith)
    rcases le_or_gt x (85 / 8 - 1 / 2 ^ 40) with hlow4 | hlow4
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowE.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowE.pAsym from rfl]
      exact LgammaAsymLowE.cover x (by norm_num at hlow3 ⊢; linarith)
          (by norm_num at hlow4 ⊢; linarith)
    rcases le_or_gt x (12 - 1 / 2 ^ 40) with hlow5 | hlow5
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowF.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowF.pAsym from rfl]
      exact LgammaAsymLowF.cover x (by norm_num at hlow4 ⊢; linarith)
          (by norm_num at hlow5 ⊢; linarith)
    rcases le_or_gt x (107 / 8 - 1 / 2 ^ 40) with hlow6 | hlow6
    · rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowG.c0Asym from rfl,
        show LgammaAsymLowA.pAsym = LgammaAsymLowG.pAsym from rfl]
      exact LgammaAsymLowG.cover x (by norm_num at hlow5 ⊢; linarith)
          (by norm_num at hlow6 ⊢; linarith)
    rw [show LgammaAsymLowA.c0Asym = LgammaAsymLowH.c0Asym from rfl,
      show LgammaAsymLowA.pAsym = LgammaAsymLowH.pAsym from rfl]
    exact LgammaAsymLowH.cover x (by norm_num at hlow6 ⊢; linarith) (by norm_num at h2 ⊢; linarith)

theorem logAccFact : LogAccFact := by
  unfold LogAccFact
  exact ⟨LgammaLogAcc.log_kernel_fact, LgammaLogAcc.h1_close, LgammaLogAcc.h2_close,
    LgammaLogAcc.ln2Acc_close⟩

theorem sinpiAccFact : SinpiAccFact := by
  unfold SinpiAccFact
  exact ⟨LgammaSinpiAcc.acc_cos_fact, LgammaSinpiAcc.acc_sin_fact⟩

theorem rootFact : RootFact := by
  intro afh lo hi o n k e hm x h1 h2 h3
  simp only [rootRanges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
  · exact LgammaRootA.range0 x h1 h2 h3
  · exact LgammaRootA.range1 x h1 h2 h3
  · exact LgammaRootA.range2 x h1 h2 h3
  · exact LgammaRootB.range3 x h1 h2 h3
  · exact LgammaRootB.range4 x h1 h2 h3
  · exact LgammaRootB.range5 x h1 h2 h3
  · exact LgammaRootC.range6 x h1 h2 h3
  · exact LgammaRootC.range7 x h1 h2 h3
  · exact LgammaRootC.range8 x h1 h2 h3
  · exact LgammaRootD.range9 x h1 h2 h3
  · exact LgammaRootD.range10 x h1 h2 h3
  · exact LgammaRootD.range11 x h1 h2 h3
  · exact LgammaRootE.range12 x h1 h2 h3
  · exact LgammaRootE.range13 x h1 h2 h3
  · exact LgammaRootE.range14 x h1 h2 h3
  · exact LgammaRootF.range15 x h1 h2 h3
  · exact LgammaRootF.range16 x h1 h2 h3

/-- A bound `B ≥ 2 ^ -60` from `LgammaZerosA` or `LgammaZerosB` on a pole interval that contains
the range. -/
theorem min_of {v B : ℝ} (hB : 1 / 2 ^ 60 ≤ B) (h : B ≤ |GammaBasic.lgamma v|) : 1 / 2 ^ 60 ≤ |GammaBasic.lgamma v| :=
  hB.trans h

theorem rootMinFact : RootMinFact := by
  intro afh lo hi o n k e hm w _ h1 h2
  simp only [rootRanges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  have hw : ratOfWord 0xC004E147AE147AE1 = -5877197513718497 / 2 ^ 51 := by decide +kernel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm <;>
    (try simp only [hw] at h1 h2) <;> push_cast at h1 h2
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound2 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound2 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound3 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound3 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound4 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound4 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound5 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound5 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound6 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound6 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound7 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound7 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound8 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound8 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound9 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosA.bound9 w (by push_cast; linarith) (by push_cast; linarith))
  · exact min_of (by norm_num [min_def])
      (LgammaZerosB.bound10 w (by push_cast; linarith) (by push_cast; linarith))

theorem dbFact : DbFact := LgammaDb.db_fact

theorem cancelFact : CancelFact := by
  intro w _ hv hni
  exact LgammaCancel.cancel_fact w hv hni

theorem allFacts : AllFacts := by
  unfold AllFacts
  exact ⟨smallFact, pieceFact, stirlingFact, logFact, sinpiFact, accPolyFact, asymFact, logAccFact,
    sinpiAccFact, rootFact, rootMinFact, dbFact, cancelFact⟩

#print axioms allFacts

end Library.Numerics.Float64.Lgamma.LgammaFacts
