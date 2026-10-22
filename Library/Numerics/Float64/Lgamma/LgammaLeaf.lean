import Library.Numerics.Float64.Lgamma.LgammaReflWin

/-!
The bounds on the positive leaf `(fh, fl, eps)` that the fast path of `Lgamma.lgammaWith` computes
at `a = |x|` from `1/2` on, and the two uses of the leaf.  `LeafSpec a` is the disjunction of the
form of a piece, from 0.5 to 8.29541 (`leaf_piece`), with the margin `|fh|/2^65` and
`eps = |fh| · 8.7 · 10^-20 + 10^-24`, and the form of Stirling's series, from 8.29541 to `2^800`
(`leaf_stir_a`, `leaf_stir_b`), with the margin `|fh|/2^67` and `eps = |fh| · 4.5 · 10^-20`.
`pos_leaf` gives `FastSpec` at a positive `x` in the absolute form.  `neg_leaf` gives `FastSpec` for
the reflection at a negative non-integer `x` from `-1/2` to `-2^52`: `LgammaReflMid.refl_two` from
-2 to -1/2, `LgammaReflWin.refl_four` from -4 to -2, `LgammaReflMid.refl_six` from -6 to -4, and
`LgammaReflTail.refl_tail` below -6, where a piece has `|fh| ≥ ln 64`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaLeaf
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor LgammaWalk LgammaReflCore LgammaReflTail LgammaReflMid
  LgammaReflWin

set_option exponentiation.threshold 4096

/-- The bounds on a positive leaf `t = (fh, fl, eps)` at `a`: a piece, or Stirling's series. -/
def LeafSpec (a : ℝ) (t : Float × Float × Float) : Prop :=
  Finite t.1.toBits ∧ Finite t.2.1.toBits ∧ Finite t.2.2.toBits ∧
    ((a ≤ 9 ∧ |value t.1.toBits| ≤ 16 ∧ |value t.2.1.toBits| ≤ 1 / 2 ^ 38 ∧
        |value t.1.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value t.2.2.toBits ∧
        value t.2.2.toBits ≤ |value t.1.toBits| / 2 ^ 63 + 1 / 2 ^ 78 ∧
        |GammaBasic.lgamma a - (value t.1.toBits + value t.2.1.toBits)| +
          |value t.1.toBits| / 2 ^ 65 ≤ 2 * value t.2.2.toBits) ∨
      (829 / 100 ≤ a ∧ 8 ≤ value t.1.toBits ∧ value t.1.toBits ≤ 2 ^ 900 ∧
        (a < 2 ^ 52 → value t.1.toBits ≤ 2 ^ 58) ∧
        |value t.2.1.toBits| ≤ value t.1.toBits / 2 ^ 17 ∧
        value t.1.toBits * (448 / 10 ^ 22) ≤ value t.2.2.toBits ∧
        value t.2.2.toBits ≤ value t.1.toBits / 2 ^ 62 ∧
        |GammaBasic.lgamma a - (value t.1.toBits + value t.2.1.toBits)| +
          value t.1.toBits / 2 ^ 67 ≤ 2 * value t.2.2.toBits))

theorem border_le : ∀ k, k < 20 → LgammaApprox.border k ≤ 9 := by decide +kernel

/-- **A piece** from 0.5 to 8.29541 is a leaf. -/
theorem leaf_piece (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hPF : LgammaApprox.PieceFact) (ax : Float)
    (hax : Finite ax.toBits) (k : ℕ) (hk : k < 19) (jj : UInt64) (hjj : jj.toNat = k)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value ax.toBits)
    (hb1 : value ax.toBits ≤ (LgammaApprox.border (k + 1) : ℝ))
    (hv1 : value ax.toBits ≠ 1) (hv2 : value ax.toBits ≠ 2) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (ax - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - ax) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (ax - 2.0) Q.1 Q.2 else (Q.1, Q.2)) :
    LeafSpec (value ax.toBits)
      (R.1, R.2, R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7) := by
  obtain ⟨hr1, hr2, hef, hr1b, hr2b, helo, hehi, hpos⟩ :=
    piece_iface hF hPF ax hax k hk jj hjj hb0 hb1 hv1 hv2 P Q R hP hQ hR
  have h9 := qcast_le (border_le (k + 1) (by omega))
  push_cast at h9
  exact ⟨hr1, hr2, hef, Or.inl ⟨hb1.trans h9, hr1b, hr2b, helo, hehi, hpos⟩⟩

/-- Stirling's series is a leaf, given the conclusion of `LgammaStir.stir_a` or `stir_b`. -/
theorem leaf_stir (a : ℝ) (ha : 829 / 100 ≤ a) (R : Float × Float) (hr1 : Finite R.1.toBits)
    (hr2 : Finite R.2.toBits) (hR1lo : 8 ≤ value R.1.toBits)
    (hR2r : |value R.2.toBits| ≤ value R.1.toBits / 2 ^ 17) (hR1hi : value R.1.toBits ≤ 2 ^ 900)
    (hsmall : a < 2 ^ 52 → value R.1.toBits ≤ 2 ^ 58)
    (hmain : |GammaBasic.lgamma a - (value R.1.toBits + value R.2.toBits)| +
        value R.1.toBits / 2 ^ 67 ≤
      2 * (value R.1.toBits * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) -
        value R.1.toBits / 2 ^ 100) :
    LeafSpec a (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  have hR1a : |value R.1.toBits| = value R.1.toBits := abs_of_pos (by linarith)
  obtain ⟨hef, hev⟩ := LgammaFastPos.eps5_value R.1 hr1 (by rw [hR1a]; exact hR1hi)
  rw [hR1a] at hev
  have hc5 := qcast_le LgammaStir.c5_bounds.1
  have hc5' := qcast_le LgammaStir.c5_bounds.2
  push_cast at hc5 hc5'
  set c := ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) with hcdef
  set r := value R.1.toBits with hrdef
  have hp1 : r * (449 / 10 ^ 22) ≤ r * c := mul_le_mul_of_nonneg_left hc5 (by linarith)
  have hp2 : r * c ≤ r * (1 / 2 ^ 64) := mul_le_mul_of_nonneg_left hc5' (by linarith)
  have hp3 : r * c / 2 ^ 53 ≤ r * (1 / 2 ^ 64) / 2 ^ 53 :=
    div_le_div_of_nonneg_right hp2 (by norm_num)
  have hev' := abs_le.mp hev
  have hk : 1 / 2 ^ 1075 ≤ r / 2 ^ 1000 := by
    have : (8 : ℝ) / 2 ^ 1000 ≤ r / 2 ^ 1000 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 8 / 2 ^ 1000)]
  refine ⟨hr1, hr2, hef, Or.inr ⟨ha, hR1lo, hR1hi, hsmall, hR2r, ?_, ?_, ?_⟩⟩
  · show r * (448 / 10 ^ 22) ≤ value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits
    linarith
  · show value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits ≤ r / 2 ^ 62
    linarith
  · show |GammaBasic.lgamma a - (r + value R.2.toBits)| + r / 2 ^ 67 ≤
      2 * value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits
    linarith

/-- **Stirling's series from 8.29541 to `2^52`** is a leaf. -/
theorem leaf_stir_a (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (ax : Float) (hax : Finite ax.toBits)
    (hb : (LgammaApprox.border 19 : ℝ) ≤ value ax.toBits) (h52 : value ax.toBits < 2 ^ 52)
    (L0 M N E T R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax)
    (hM : M = mulDDD (ax - 0.5) (L0.1 - 1.0) L0.2)
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hE : E = fastTwoSum (entry Lgamma.mainTable 399)
      (Library.Numerics.Float64.Tgamma.TgammaExpr.evalF LgammaStirSeries.sE ((1.0 / ax) * (1.0 / ax))))
    (hT : T = mulDD E.1 (E.2 + entry Lgamma.mainTable 400) (1.0 / ax)
      (Library.Numerics.Arithmetic.Fma.fma (1.0 / ax) (-ax) 1.0 * (1.0 / ax)))
    (hR : R = fastSum N.1 N.2 T.1 T.2) :
    LeafSpec (value ax.toBits) (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  obtain ⟨hr1, hr2, hR1lo, hR2r, hR1hi, hmain⟩ :=
    LgammaStir.stir_a hF hL hSF ax hax hb h52 L0 M N E T R hL0 hM hN hE hT hR
  have hb19 := qcast_le LgammaStir.border19
  push_cast at hb19
  exact leaf_stir _ (by linarith) R hr1 hr2 hR1lo hR2r
    (hR1hi.trans (by norm_num)) (fun _ => hR1hi) hmain

/-- **Stirling's series from `2^52` to `2^800`** is a leaf. -/
theorem leaf_stir_b (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (ax : Float) (hax : Finite ax.toBits)
    (h52 : 2 ^ 52 ≤ value ax.toBits) (h800 : value ax.toBits ≤ 2 ^ 800)
    (L0 M N T R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax)
    (hM : M = mulDDD ax (L0.1 - 1.0) L0.2)
    (hN : N = fastSum M.1 (M.2 - (L0.1 - 1.0) * 0.5) (entry Lgamma.mainTable 397)
      (entry Lgamma.mainTable 398))
    (hT1 : Finite T.1.toBits) (hT2 : Finite T.2.toBits)
    (hTe : |value T.1.toBits + value T.2.toBits - LgammaStir.Tx (value ax.toBits)| ≤ 1 / 2 ^ 65)
    (hT1b : |value T.1.toBits| ≤ 1 / 64) (hT2b : |value T.2.toBits| ≤ 1 / 2 ^ 50)
    (hR : R = fastSum N.1 N.2 T.1 T.2) :
    LeafSpec (value ax.toBits) (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  obtain ⟨hr1, hr2, hR1lo, hR2r, hR1hi, hmain⟩ :=
    LgammaStir.stir_b hF hL hSF ax hax h52 h800 L0 M N T R hL0 hM hN hT1 hT2 hTe hT1b hT2b hR
  exact leaf_stir _ (by linarith [(by norm_num : (829 / 100 : ℝ) ≤ 2 ^ 52)]) R hr1 hr2 hR1lo hR2r
    hR1hi (fun h => absurd h (not_lt.mpr h52)) hmain

/-- **The leaf at a positive `x`** gives `FastSpec` in the absolute form. -/
theorem pos_leaf (x : Float) (t : Float × Float × Float) (hl : LeafSpec (value x.toBits) t)
    (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits))) (t.1, t.2.1, t.2.2, sign) := by
  obtain ⟨h1, h2, h3, hc⟩ := hl
  unfold FastSpec
  dsimp only
  rw [show Real.log (Real.Gamma (value x.toBits)) = GammaBasic.lgamma (value x.toBits) from rfl]
  rcases hc with ⟨-, hfb, hlb, helo, hehi, hpos⟩ | ⟨-, h8, h900, -, hlb, helo, hehi, hpos⟩
  · have h0 := mul_nonneg (abs_nonneg (value t.1.toBits)) (by norm_num : (0 : ℝ) ≤ 869 / 10 ^ 22)
    have : 0 ≤ |value t.1.toBits| / 2 ^ 65 := by positivity
    refine ⟨h1, h2, h3, by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 98 / 10 ^ 26)],
      Or.inl ⟨?_, ?_, by linarith⟩⟩
    · linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 ≤ 2 ^ 48 * (98 / 10 ^ 26))]
    · linarith [(by norm_num : (16 : ℝ) + 2 ^ 49 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≤ 2 ^ 1020)]
  · have hfa : |value t.1.toBits| = value t.1.toBits := abs_of_pos (by linarith)
    have : 0 ≤ value t.1.toBits / 2 ^ 67 := by positivity
    refine ⟨h1, h2, h3, by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 8 * (448 / 10 ^ 22))],
      Or.inl ⟨?_, ?_, by linarith⟩⟩
    · linarith
    · rw [hfa]
      linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 49 * (2 ^ 900 / 2 ^ 62) ≤ 2 ^ 1020)]

set_option maxHeartbeats 1000000 in
/-- **The reflection of a leaf**: `FastSpec` at a negative non-integer `x` from `-1/2` to `-2^52`,
from the leaf at `|x|`. -/
theorem neg_leaf (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (hneg : value x.toBits ≤ -1 / 2) (h52 : -2 ^ 52 < value x.toBits)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (t : Float × Float × Float)
    (hl : LeafSpec (-value x.toBits) t) (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD t.1 t.2.1 C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, t.2.2 + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨hr1, hr2, hef, hc⟩ := hl
  set v := value x.toBits with hvdef
  rcases hc with ⟨h9, hr1b, hr2b, helo, hehi, hpos⟩ | ⟨ha, h8, h900, hsmall, hlb, helo, hehi, hpos⟩
  · have hm2 : v ≠ -2 := by have := hint (-2); push_cast at this; exact this
    have hm4 : v ≠ -4 := by have := hint (-4); push_cast at this; exact this
    have hm6 : v ≠ -6 := by have := hint (-6); push_cast at this; exact this
    rcases lt_or_gt_of_ne hm2 with h2 | h2
    · rcases lt_or_gt_of_ne hm4 with h4 | h4
      · rcases lt_or_gt_of_ne hm6 with h6 | h6
        · -- below -6
          have hlg : (4158 / 1000 : ℝ) ≤ GammaBasic.lgamma (-v) :=
            log_bounds.2.2.trans (lgamma_six.trans
              (GammaThresholds.lgamma_mono (by norm_num) (by linarith)))
          have hF4 : 4 ≤ |value t.1.toBits| := by
            have h1 : GammaBasic.lgamma (-v) - (value t.1.toBits + value t.2.1.toBits) ≤
                2 * value t.2.2.toBits := by
              have := le_abs_self (GammaBasic.lgamma (-v) - (value t.1.toBits + value t.2.1.toBits))
              have : 0 ≤ |value t.1.toBits| / 2 ^ 65 := by positivity
              linarith
            have h3 : |value t.1.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 :=
              div_le_div_of_nonneg_right hr1b (by norm_num)
            have h4 := le_abs_self (value t.1.toBits)
            have h5 := le_abs_self (value t.2.1.toBits)
            linarith [(by norm_num : (4158 : ℝ) / 1000 - 1 / 2 ^ 38 -
              2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≥ 4)]
          refine refl_tail hF hL hS x hx (by linarith) h52 hint t.1 t.2.1 t.2.2 hr1 hr2 hef hF4
            (by linarith [(by norm_num : (16 : ℝ) ≤ 2 ^ 60)])
            (by have : 0 ≤ |value t.1.toBits| / 2 ^ 17 := by positivity
                linarith)
            (by have := mul_le_mul_of_nonneg_left
                  (by norm_num : (448 : ℝ) / 10 ^ 22 ≤ 869 / 10 ^ 22) (abs_nonneg (value t.1.toBits))
                linarith)
            (by have : |value t.1.toBits| / 2 ^ 63 ≤ |value t.1.toBits| / 2 ^ 62 :=
                  div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
                linarith)
            (by have : |value t.1.toBits| / 2 ^ 67 ≤ |value t.1.toBits| / 2 ^ 65 :=
                  div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
                linarith)
            A B C D hA hB hC hD sign
        · exact refl_six hF hL hS x hx h6 h4 hint t.1 t.2.1 t.2.2 hr1 hr2 hef hr1b hr2b helo hehi
            hpos A B C D hA hB hC hD sign
      · exact refl_four hF hL hS x hx h4 h2 hint t.1 t.2.1 t.2.2 hr1 hr2 hef hr1b hr2b helo hehi
          hpos A B C D hA hB hC hD sign
    · exact refl_two hF hL hS x hx h2 hneg hint t.1 t.2.1 t.2.2 hr1 hr2 hef hr1b hr2b helo hehi
        hpos A B C D hA hB hC hD sign
  · have hfa : |value t.1.toBits| = value t.1.toBits := abs_of_pos (by linarith)
    have hF58 := hsmall (by linarith)
    refine refl_tail hF hL hS x hx (by linarith) h52 hint t.1 t.2.1 t.2.2 hr1 hr2 hef
      (by rw [hfa]; linarith) (by rw [hfa]; linarith [(by norm_num : (2 : ℝ) ^ 58 ≤ 2 ^ 60)])
      (by rw [hfa]; have : 0 ≤ 1 / (2 : ℝ) ^ 38 := by norm_num
          linarith) (by rw [hfa]; linarith) (by rw [hfa]; linarith) (by rw [hfa]; linarith)
      A B C D hA hB hC hD sign

#print axioms leaf_piece
#print axioms leaf_stir_a
#print axioms leaf_stir_b
#print axioms pos_leaf
#print axioms neg_leaf

end Library.Numerics.Float64.Lgamma.LgammaLeaf
