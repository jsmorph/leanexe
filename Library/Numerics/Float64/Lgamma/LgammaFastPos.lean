import Library.Numerics.Float64.Lgamma.LgammaStir

/-!
`FastSpec` for the fast path at positive `x` from 0.5 on: the pieces up to 8.29541
(`LgammaFastPiece.piece_leaf`) with the code's `eps = |fh| · 8.7 · 10^-20 + 10^-24`
(`pos_piece_spec`), and Stirling's series from 8.29541 to `2 ^ 800` (`LgammaStir.stir_a`,
`stir_b`) with `eps = |fh| · 4.5 · 10^-20` (`pos_stir_spec`).  Both use the absolute form of
`FastSpec`: the computed `eps` lies within `2 ^ -105` or `|fh|/2^115` of its exact value, which the
leaves' bounds leave room for.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaFastPos
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaPiecePoly
  LgammaFastSmall LgammaFastPiece LgammaWalk

set_option exponentiation.threshold 4096

/-- **The pieces at positive `x`** from 0.5 to 8.29541 satisfy `FastSpec`. -/
theorem pos_piece_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hPF : LgammaApprox.PieceFact) (x : Float)
    (hx : Finite x.toBits) (k : ℕ) (hk : k < 19) (jj : UInt64) (hjj : jj.toNat = k)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value x.toBits)
    (hb1 : value x.toBits ≤ (LgammaApprox.border (k + 1) : ℝ))
    (hv1 : value x.toBits ≠ 1) (hv2 : value x.toBits ≠ 2) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (x - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - x) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (x - 2.0) Q.1 Q.2 else (Q.1, Q.2)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (R.1, R.2, R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7,
        sign) := by
  obtain ⟨hr1, hr2, hr2b, hr1b, hmain⟩ :=
    piece_leaf hF hPF x hx k hk jj hjj hb0 hb1 hv1 hv2 P Q R hP hQ hR
  obtain ⟨hef, hev⟩ := eps_value R.1 hr1 hr1b
  have hc2 := qcast_le c2_bounds.1
  have hc1 := qcast_le c1_bounds.1
  have hc1' := qcast_le c1_bounds.2
  have hc2' := qcast_le c2_bounds.2
  push_cast at hc1 hc2 hc1' hc2'
  set e := R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7 with hedef
  have hp0 : 0 ≤ |value R.1.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ) :=
    mul_nonneg (abs_nonneg _) (by linarith)
  have hp1 : |value R.1.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ) ≤
      16 * (1 / 2 ^ 63) := mul_le_mul hr1b hc1' (by linarith) (by norm_num)
  have hev' := abs_le.mp hev
  have he0 : 1 / 2 ^ 80 ≤ value e.toBits := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 80 + 1 / 2 ^ 105 ≤ 99 / 10 ^ 26)]
  have he1 : value e.toBits ≤ 1 / 2 ^ 58 := by
    linarith [(by norm_num : (16 : ℝ) * (1 / 2 ^ 63) + 1 / 2 ^ 79 + 1 / 2 ^ 105 ≤ 1 / 2 ^ 58)]
  unfold FastSpec
  dsimp only
  rw [show Real.log (Real.Gamma (value x.toBits)) = GammaBasic.lgamma (value x.toBits) from rfl]
  refine ⟨hr1, hr2, hef, le_trans (by norm_num) he0, Or.inl ⟨?_, ?_, ?_⟩⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 ≤ 2 ^ 48 * (1 / 2 ^ 80))]
  · linarith [(by norm_num : (16 : ℝ) + 2 ^ 49 * (1 / 2 ^ 58) ≤ 2 ^ 1020)]
  · have : 0 ≤ |value R.1.toBits| / 2 ^ 65 := by positivity
    linarith

/-- The code's `eps = |fh| c5` within `|fh| c5/2^53 + 2 ^ -1075` of `|fh| c5`. -/
theorem eps5_value (r : Float) (hr : Finite r.toBits) (hrb : |value r.toBits| ≤ 2 ^ 900) :
    Finite (r.abs * Float.ofBits 0x3BEA90352E248A68).toBits ∧
      |value (r.abs * Float.ofBits 0x3BEA90352E248A68).toBits -
        |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)| ≤
        |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) / 2 ^ 53 +
          1 / 2 ^ 1075 := by
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float r hr
  have hw : Wasm.IEEE64.isFinite 0x3BEA90352E248A68 = true := by decide
  have hc5 := qcast_le LgammaStir.c5_bounds.1
  have hc5' := qcast_le LgammaStir.c5_bounds.2
  push_cast at hc5 hc5'
  have ha := fapprox_self r.abs haf
  have hb := fapprox_self (Float.ofBits 0x3BEA90352E248A68) (ofBits_finite _ hw)
  rw [hav] at ha
  rw [ofBits_value _ hw] at hb
  have hca : |((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)| =
      ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) := abs_of_pos (by linarith)
  have hm := fapprox_mul ha hb (|value r.toBits|) ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)
    (by rw [abs_abs]) (le_of_eq hca)
    (|value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) (by simp)
    (by
      have : |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) ≤
          2 ^ 900 * (1 / 2 ^ 64) := mul_le_mul hrb hc5' (by linarith) (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 900 * (1 / 2 ^ 64) < 2 ^ 1022)])
  refine ⟨hm.1, hm.2.trans (le_of_eq ?_)⟩
  ring

/-- **Stirling's series at positive `x`** from 8.29541 to `2 ^ 800` satisfies `FastSpec`, given a
leaf of `LgammaStir`. -/
theorem pos_stir_spec (x : Float) (R : Float × Float) (hr1 : Finite R.1.toBits)
    (hr2 : Finite R.2.toBits) (hR1lo : 8 ≤ value R.1.toBits)
    (hR2r : |value R.2.toBits| ≤ value R.1.toBits / 2 ^ 17) (hR1hi : value R.1.toBits ≤ 2 ^ 900)
    (hmain : |GammaBasic.lgamma (value x.toBits) - (value R.1.toBits + value R.2.toBits)| +
        value R.1.toBits / 2 ^ 67 ≤
      2 * (value R.1.toBits * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) -
        value R.1.toBits / 2 ^ 100) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68, sign) := by
  have hR1a : |value R.1.toBits| = value R.1.toBits := abs_of_pos (by linarith)
  obtain ⟨hef, hev⟩ := eps5_value R.1 hr1 (by rw [hR1a]; exact hR1hi)
  rw [hR1a] at hev
  have hc5 := qcast_le LgammaStir.c5_bounds.1
  have hc5' := qcast_le LgammaStir.c5_bounds.2
  push_cast at hc5 hc5'
  set c := ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) with hcdef
  set r := value R.1.toBits with hrdef
  have hp1 : r * (449 / 10 ^ 22) ≤ r * c := mul_le_mul_of_nonneg_left hc5 (by linarith)
  have hp2 : r * c ≤ r * (1 / 2 ^ 64) := mul_le_mul_of_nonneg_left hc5' (by linarith)
  have hev' := abs_le.mp hev
  set e := R.1.abs * Float.ofBits 0x3BEA90352E248A68 with hedef
  have hk : 1 / 2 ^ 1075 ≤ r / 2 ^ 1000 := by
    have : (8 : ℝ) / 2 ^ 1000 ≤ r / 2 ^ 1000 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 8 / 2 ^ 1000)]
  have he0 : r * (448 / 10 ^ 22) ≤ value e.toBits := by
    have : r * c / 2 ^ 53 ≤ r * (1 / 2 ^ 64) / 2 ^ 53 := div_le_div_of_nonneg_right hp2 (by norm_num)
    linarith
  unfold FastSpec
  dsimp only
  rw [show Real.log (Real.Gamma (value x.toBits)) = GammaBasic.lgamma (value x.toBits) from rfl]
  refine ⟨hr1, hr2, hef, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 8 * (448 / 10 ^ 22))]
  · have : r / 2 ^ 17 ≤ 2 ^ 48 * (r * (448 / 10 ^ 22)) := by linarith
    linarith
  · have : r * c / 2 ^ 53 ≤ r * (1 / 2 ^ 64) / 2 ^ 53 := div_le_div_of_nonneg_right hp2 (by norm_num)
    rw [hR1a]
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 49 * (2 ^ 900 * (1 / 2 ^ 64) +
      2 ^ 900 * (1 / 2 ^ 64) / 2 ^ 53 + 2 ^ 900 / 2 ^ 1000) ≤ 2 ^ 1020)]
  · have : r * c / 2 ^ 53 ≤ r * (1 / 2 ^ 64) / 2 ^ 53 := div_le_div_of_nonneg_right hp2 (by norm_num)
    have : 0 ≤ r / 2 ^ 67 := by positivity
    linarith

#print axioms pos_piece_spec
#print axioms pos_stir_spec

end Library.Numerics.Float64.Lgamma.LgammaFastPos
