import Library.Numerics.Float64.Lgamma.LgammaPiecePoly
import Library.Numerics.Float64.Lgamma.LgammaPieceIdx
import Library.Numerics.Float64.Lgamma.LgammaSpecial
import LeanExe.ProofKit.F64Sterbenz

/-!
The fast path's pieces from 0.5 to 8.29541 at a double `a` of piece `k`: `z = a - offs k`, exact by
Sterbenz's lemma, the double-double polynomial of the piece at `z` (`LgammaPiecePoly.piece_poly`),
multiplied by `1 - a` on piece 4 and by `a - 2` on piece 10 (`mulDDD`), and the code's error bound
`eps = |fh| · 8.7 · 10^-20 + 10^-24`.  With `PieceFact`, the result `fh + fl` lies within
`2 eps - |fh|/2^65` of `ln |Γ a|` (`piece_leaf`).  The margin `|fh|/2^65` leaves room for the
logarithm and the sine of the reflection when `a = |x|` for a negative `x`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaFastPiece
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaExpr Library.Numerics.Float64.Tgamma.TgammaWords
  LgammaPiecePoly LgammaFastSmall

set_option exponentiation.threshold 4096

/-- The exact difference of two doubles within a factor 2 of each other. -/
theorem sub_float (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hab : |value a.toBits - value b.toBits| ≤ |value a.toBits|)
    (hba : |value a.toBits - value b.toBits| ≤ |value b.toBits|)
    (hbig : |value b.toBits| < 2 ^ 1021) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  rw [F64Bits.toBits_sub]
  exact F64Sterbenz.sub_exact _ _ ha hb hab hba hbig

/-- The offsets and the borders of the pieces. -/
theorem offs_ok : ∀ k < 19, Wasm.IEEE64.isFinite (wq (20 + k)) = true ∧
    1 / 2 ≤ LgammaApprox.border k ∧ LgammaApprox.border k ≤ LgammaApprox.offs k ∧
    LgammaApprox.offs k ≤ LgammaApprox.border (k + 1) ∧
    LgammaApprox.border (k + 1) ≤ 2 * LgammaApprox.border k ∧ LgammaApprox.border (k + 1) ≤ 9 ∧
    LgammaApprox.offs k - LgammaApprox.border k + 1 / 2 ^ 50 ≤ pX k ∧
    LgammaApprox.border (k + 1) - LgammaApprox.offs k + 1 / 2 ^ 50 ≤ pX k := by
  decide +kernel

/-- The pieces with the factors `1 - a` and `a - 2`. -/
theorem zero_pieces : 4 / 5 ≤ LgammaApprox.border 4 ∧ LgammaApprox.border 5 ≤ 11 / 10 ∧
    19 / 10 ≤ LgammaApprox.border 10 ∧ LgammaApprox.border 11 ≤ 23 / 10 ∧
    2 / 5 ≤ pLow 4 ∧ 2 / 5 ≤ pLow 10 := by
  decide +kernel

theorem c1_bounds : (869 / 10 ^ 22 : ℚ) ≤ PolyBound.ratOfWord 0x3BF9AD88BDABDB20 ∧
    PolyBound.ratOfWord 0x3BF9AD88BDABDB20 ≤ 1 / 2 ^ 63 := by
  decide +kernel

theorem c2_bounds : (99 / 10 ^ 26 : ℚ) ≤ PolyBound.ratOfWord 0x3AF357C299A88EA7 ∧
    PolyBound.ratOfWord 0x3AF357C299A88EA7 ≤ 1 / 2 ^ 79 := by
  decide +kernel

/-- The indices of the code for piece `k`. -/
theorem idx (jj : UInt64) (k : ℕ) (hjj : jj.toNat = k) (hk : k < 19) :
    (20 + jj).toNat = 20 + k ∧ (191 + 10 * jj).toNat = 191 + 10 * k ∧
    (39 + 8 * jj).toNat = 39 + 8 * k ∧ (39 + 8 * jj + 1).toNat = 39 + 8 * k + 1 ∧
    (39 + 8 * jj + 2).toNat = 39 + 8 * k + 2 ∧ (39 + 8 * jj + 3).toNat = 39 + 8 * k + 3 ∧
    (39 + 8 * jj + 4).toNat = 39 + 8 * k + 4 ∧ (39 + 8 * jj + 5).toNat = 39 + 8 * k + 5 ∧
    (39 + 8 * jj + 6).toNat = 39 + 8 * k + 6 ∧ (39 + 8 * jj + 7).toNat = 39 + 8 * k + 7 := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, hjj, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `Lgamma.piecePoly` is `polyDDDFst` with the tail `tE k`. -/
theorem piecePoly_eq (jj : UInt64) (k : ℕ) (hjj : jj.toNat = k) (hk : k < 19) (z : Float) :
    Lgamma.piecePoly Lgamma.mainTable jj z =
      Lgamma.polyDDDFst Lgamma.mainTable (191 + 10 * jj) 5 z (evalF (tE k) z) := by
  obtain ⟨-, -, h0, h1, h2, h3, h4, h5, h6, h7⟩ := idx jj k hjj hk
  simp only [Lgamma.piecePoly, evalF, tE, lin, x2E, x4E]
  rw [entry_eq _ _ _ h0, entry_eq _ _ _ h1, entry_eq _ _ _ h2, entry_eq _ _ _ h3,
    entry_eq _ _ _ h4, entry_eq _ _ _ h5, entry_eq _ _ _ h6, entry_eq _ _ _ h7]

/-- The code's `eps` within `2 ^ -105` of `|r| c1 + c2`. -/
theorem eps_value (r : Float) (hr : Finite r.toBits) (hrb : |value r.toBits| ≤ 16) :
    Finite (r.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7).toBits ∧
      |value (r.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7).toBits -
        (|value r.toBits| * (PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℝ) +
          (PolyBound.ratOfWord 0x3AF357C299A88EA7 : ℝ))| ≤ 1 / 2 ^ 105 := by
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float r hr
  have hw1 : Wasm.IEEE64.isFinite 0x3BF9AD88BDABDB20 = true := by decide
  have hw2 : Wasm.IEEE64.isFinite 0x3AF357C299A88EA7 = true := by decide
  have hc1 := qcast_le c1_bounds.1
  have hc1' := qcast_le c1_bounds.2
  have hc2 := qcast_le c2_bounds.1
  have hc2' := qcast_le c2_bounds.2
  push_cast at hc1 hc1' hc2 hc2'
  have hv1 := ofBits_value _ hw1
  have hv2 := ofBits_value _ hw2
  have ha := fapprox_self r.abs haf
  have hb := fapprox_self (Float.ofBits 0x3BF9AD88BDABDB20) (ofBits_finite _ hw1)
  have hc := fapprox_self (Float.ofBits 0x3AF357C299A88EA7) (ofBits_finite _ hw2)
  rw [hav] at ha
  rw [hv1] at hb
  rw [hv2] at hc
  have hc1a : |((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ)| ≤ 1 / 2 ^ 63 := by
    rw [abs_of_nonneg (by linarith)]; exact hc1'
  have hm := fapprox_mul ha hb 16 (1 / 2 ^ 63) (by rw [abs_abs]; exact hrb) hc1a (16 * (1 / 2 ^ 63))
    (by norm_num) (by norm_num)
  have hpr : |(|value r.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ))| ≤
      16 * (1 / 2 ^ 63) := by
    rw [abs_mul, abs_abs]
    exact mul_le_mul hrb hc1a (abs_nonneg _) (by norm_num)
  have hc2a : |((PolyBound.ratOfWord 0x3AF357C299A88EA7 : ℚ) : ℝ)| ≤ 1 / 2 ^ 79 := by
    rw [abs_of_nonneg (by linarith)]; exact hc2'
  have hs := fapprox_add hm hc (1 / 2 ^ 58)
    (by
      linarith [abs_add_le (|value r.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ))
        ((PolyBound.ratOfWord 0x3AF357C299A88EA7 : ℚ) : ℝ)])
    (by norm_num)
  refine ⟨hs.1, hs.2.trans ?_⟩
  norm_num

/-- The bounds of the result before the factor of pieces 4 and 10, against the piece's
approximation `pA`. -/
theorem piece_key (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (ax : Float) (hax : Finite ax.toBits) (k : ℕ)
    (hk : k < 19) (jj : UInt64) (hjj : jj.toNat = k)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value ax.toBits)
    (hb1 : value ax.toBits ≤ (LgammaApprox.border (k + 1) : ℝ))
    (hv1 : value ax.toBits ≠ 1) (hv2 : value ax.toBits ≠ 2) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (ax - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - ax) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (ax - 2.0) Q.1 Q.2 else (Q.1, Q.2)) :
    Finite R.1.toBits ∧ Finite R.2.toBits ∧ |value R.2.toBits| ≤ 1 / 2 ^ 38 ∧
      |value R.1.toBits + value R.2.toBits - LgammaApprox.pieceApprox k (value ax.toBits)| ≤
        |LgammaApprox.pieceApprox k (value ax.toBits)| * (1 / 2 ^ 66 + 1 / 2 ^ 89) +
          1 / 2 ^ 1072 ∧
      |LgammaApprox.pieceApprox k (value ax.toBits)| ≤ 10 := by
  obtain ⟨hw, hhalf, hbo, hob, hb2, hb9, hpx1, hpx2⟩ := offs_ok k hk
  have hhalf' := qcast_le hhalf
  have hbo' := qcast_le hbo
  have hob' := qcast_le hob
  have hb2' := qcast_le hb2
  have hb9' := qcast_le hb9
  have hpx1' := qcast_le hpx1
  have hpx2' := qcast_le hpx2
  push_cast at hhalf' hbo' hob' hb2' hb9' hpx1' hpx2'
  have hent : entry Lgamma.mainTable (20 + jj) = Float.ofBits (wq (20 + k)) :=
    entry_eq _ _ _ (idx jj k hjj hk).1
  have hof := ofBits_finite _ hw
  have hov : value (Float.ofBits (wq (20 + k))).toBits = (LgammaApprox.offs k : ℝ) :=
    ofBits_value _ hw
  set v := value ax.toBits with hvdef
  set off : ℝ := (LgammaApprox.offs k : ℝ) with hoffdef
  -- `z = a - offs k`, exact
  have hvpos : 0 < v := by linarith
  have hd : |v - off| ≤ (LgammaApprox.border (k + 1) : ℝ) - (LgammaApprox.border k : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hzf, hzv⟩ := sub_float ax (Float.ofBits (wq (20 + k))) hax hof
    (by rw [hov, abs_of_pos hvpos]; linarith)
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < off)]; linarith)
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < off)]; linarith)
  rw [hov] at hzv
  set z := ax - Float.ofBits (wq (20 + k)) with hzdef
  have hzX : |value z.toBits| ≤ (pX k : ℝ) := by
    rw [hzv, abs_le]; constructor <;> linarith
  -- the polynomial
  have hP' : P = Lgamma.polyDDDFst Lgamma.mainTable (191 + 10 * jj) 5 z (evalF (tE k) z) := by
    simp only [hP, hent, piecePoly_eq jj k hjj hk, hzdef]
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ :=
    piece_poly hF k hk (191 + 10 * jj) (idx jj k hjj hk).2.1 z hzf hzX P hP'
  set pp := LgammaApprox.piecePoly k (value z.toBits) with hppdef
  have hlow := qcast_le (low_ok k hk).2
  have hlow0 : (0 : ℝ) < (pLow k : ℝ) := by exact_mod_cast (low_ok k hk).1
  push_cast at hlow
  have hpE : (pE k : ℝ) ≤ |pp| / 2 ^ 66 := by
    have : (pLow k : ℝ) / 2 ^ 66 ≤ |pp| / 2 ^ 66 := div_le_div_of_nonneg_right hp5 (by norm_num)
    linarith
  have hP1b : |value P.1.toBits| ≤ 11 := by
    have h1 := LgammaFastSmall.abs_le_three (value P.1.toBits) (value P.2.toBits) pp
    have : |pp| / 2 ^ 66 ≤ 10 / 2 ^ 66 := div_le_div_of_nonneg_right hp6 (by norm_num)
    linarith [(by norm_num : (10 : ℝ) / 2 ^ 66 + 10 + 1 / 2 ^ 40 ≤ 11)]
  have hpa : LgammaApprox.pieceApprox k v =
      (if k = 4 then 1 - v else if k = 10 then v - 2 else 1) * pp := by
    rw [hppdef, hzv]
    rfl
  -- the three cases
  have hne : ∀ m : ℕ, m < 19 → k ≠ m → ¬ (jj == UInt64.ofNat m) = true := by
    intro m hm hkm h
    rw [beq_iff_eq, ← UInt64.toNat_inj, hjj, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (lt_of_lt_of_le hm (by norm_num))] at h
    exact hkm h
  have heq : ∀ m : ℕ, m < 19 → k = m → (jj == UInt64.ofNat m) = true := by
    intro m hm hkm
    rw [beq_iff_eq, ← UInt64.toNat_inj, hjj, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (lt_of_lt_of_le hm (by norm_num))]
    exact hkm
  by_cases hk4 : k = 4
  · -- the factor `1 - a`
    have hk10 : k ≠ 10 := by omega
    rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, ite_eq_left (heq 4 (by norm_num) hk4)] at hQ
    rw [show (10 : UInt64) = UInt64.ofNat 10 from rfl, ite_eq_right (hne 10 (by norm_num) hk10)] at hR
    subst hk4
    have hz4 := zero_pieces
    have h40 := qcast_le hz4.1
    have h51 := qcast_le hz4.2.1
    have hpl := qcast_le hz4.2.2.2.2.1
    push_cast at h40 h51 hpl
    have hv1' : |1 - v| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
    obtain ⟨hdf, hdv⟩ := sub_float 1.0 ax LgammaSpecial.one_finite hax
      (by rw [LgammaSpecial.one_value]; norm_num; linarith [abs_le.mp hv1'])
      (by rw [LgammaSpecial.one_value, abs_of_pos hvpos]; linarith [abs_le.mp hv1'])
      (by rw [abs_of_pos hvpos]; linarith)
    rw [LgammaSpecial.one_value] at hdv
    obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := mulDDD_spec hF (1.0 - ax) P.1 P.2 hdf hp1 hp2
      (11 * |1 - v|) (1 / 2 ^ 40 * |1 - v|)
      (by rw [hdv]; exact mul_le_mul_of_nonneg_right hP1b (abs_nonneg _))
      (by rw [hdv]; exact mul_le_mul_of_nonneg_right hp4 (abs_nonneg _))
      (by linarith [abs_nonneg (1 - v)]) (by linarith [abs_nonneg (1 - v)])
    rw [hdv] at hm3
    rw [hR, hQ]
    simp only
    have hpa' : LgammaApprox.pieceApprox 4 v = (1 - v) * pp := by rw [hpa]; simp
    rw [hpa', abs_mul]
    have hA : |(1 - v) * (value P.1.toBits + value P.2.toBits) - (1 - v) * pp| ≤
        |1 - v| * (|pp| / 2 ^ 66) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hp3.trans hpE) (abs_nonneg _)
    have hB : |1 - v| * ((3 / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53) ≤ |1 - v| * (|pp| / 2 ^ 89) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have : (2 / 5 : ℝ) / 2 ^ 89 ≤ |pp| / 2 ^ 89 :=
        div_le_div_of_nonneg_right (hpl.trans hp5) (by norm_num)
      linarith [(by norm_num : ((3 : ℝ) / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53 ≤ 2 / 5 / 2 ^ 89)]
    have hC : |1 - v| * |pp| ≤ 1 / 4 * 10 := mul_le_mul hv1' hp6 (abs_nonneg _) (by norm_num)
    refine ⟨hm1, hm2, ?_, ?_, by linarith⟩
    · have : 1 / 2 ^ 40 * |1 - v| * (1 + 1 / 2 ^ 51) + 11 * |1 - v| / 2 ^ 52 + 1 / 2 ^ 1071 ≤
          1 / 2 ^ 38 := by
        linarith [abs_nonneg (1 - v)]
      linarith
    · have h1 := abs_sub_le (value (mulDDD (1.0 - ax) P.1 P.2).1.toBits +
        value (mulDDD (1.0 - ax) P.1 P.2).2.toBits) ((1 - v) * (value P.1.toBits +
        value P.2.toBits)) ((1 - v) * pp)
      have h2 : (3 * (1 / 2 ^ 40 * |1 - v|) + 11 * |1 - v| / 2 ^ 51) / 2 ^ 53 =
          |1 - v| * ((3 / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53) := by ring
      have h3 : |1 - v| * (|pp| / 2 ^ 66) + |1 - v| * (|pp| / 2 ^ 89) =
          |1 - v| * |pp| * (1 / 2 ^ 66 + 1 / 2 ^ 89) := by ring
      linarith
  by_cases hk10 : k = 10
  · -- the factor `a - 2`
    rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, ite_eq_right (hne 4 (by norm_num) hk4)] at hQ
    rw [show (10 : UInt64) = UInt64.ofNat 10 from rfl, ite_eq_left (heq 10 (by norm_num) hk10)] at hR
    subst hk10
    have hz4 := zero_pieces
    have h10 := qcast_le hz4.2.2.1
    have h11 := qcast_le hz4.2.2.2.1
    have hpl := qcast_le hz4.2.2.2.2.2
    push_cast at h10 h11 hpl
    have hv2' : |v - 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    obtain ⟨hdf, hdv⟩ := sub_float ax 2.0 hax LgammaSpecial.two_finite
      (by rw [LgammaSpecial.two_value, abs_of_pos hvpos]; linarith [abs_le.mp hv2'])
      (by rw [LgammaSpecial.two_value]; norm_num; linarith [abs_le.mp hv2'])
      (by rw [LgammaSpecial.two_value]; norm_num)
    rw [LgammaSpecial.two_value] at hdv
    obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := mulDDD_spec hF (ax - 2.0) Q.1 Q.2 hdf
      (by rw [hQ]; exact hp1) (by rw [hQ]; exact hp2)
      (11 * |v - 2|) (1 / 2 ^ 40 * |v - 2|)
      (by rw [hdv, hQ]; exact mul_le_mul_of_nonneg_right hP1b (abs_nonneg _))
      (by rw [hdv, hQ]; exact mul_le_mul_of_nonneg_right hp4 (abs_nonneg _))
      (by linarith [abs_nonneg (v - 2)]) (by linarith [abs_nonneg (v - 2)])
    rw [hdv, hQ] at hm3
    rw [hQ] at hm1 hm2 hm4
    rw [hR, hQ]
    simp only at hm1 hm2 hm3 hm4 ⊢
    have hpa' : LgammaApprox.pieceApprox 10 v = (v - 2) * pp := by rw [hpa]; simp
    rw [hpa', abs_mul]
    have hA : |(v - 2) * (value P.1.toBits + value P.2.toBits) - (v - 2) * pp| ≤
        |v - 2| * (|pp| / 2 ^ 66) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hp3.trans hpE) (abs_nonneg _)
    have hB : |v - 2| * ((3 / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53) ≤ |v - 2| * (|pp| / 2 ^ 89) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have : (2 / 5 : ℝ) / 2 ^ 89 ≤ |pp| / 2 ^ 89 :=
        div_le_div_of_nonneg_right (hpl.trans hp5) (by norm_num)
      linarith [(by norm_num : ((3 : ℝ) / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53 ≤ 2 / 5 / 2 ^ 89)]
    have hC : |v - 2| * |pp| ≤ 1 / 2 * 10 := mul_le_mul hv2' hp6 (abs_nonneg _) (by norm_num)
    refine ⟨hm1, hm2, ?_, ?_, by linarith⟩
    · have : 1 / 2 ^ 40 * |v - 2| * (1 + 1 / 2 ^ 51) + 11 * |v - 2| / 2 ^ 52 + 1 / 2 ^ 1071 ≤
          1 / 2 ^ 38 := by
        linarith [abs_nonneg (v - 2)]
      linarith
    · have h1 := abs_sub_le (value (mulDDD (ax - 2.0) P.1 P.2).1.toBits +
        value (mulDDD (ax - 2.0) P.1 P.2).2.toBits) ((v - 2) * (value P.1.toBits +
        value P.2.toBits)) ((v - 2) * pp)
      have h2 : (3 * (1 / 2 ^ 40 * |v - 2|) + 11 * |v - 2| / 2 ^ 51) / 2 ^ 53 =
          |v - 2| * ((3 / 2 ^ 40 + 11 / 2 ^ 51) / 2 ^ 53) := by ring
      have h3 : |v - 2| * (|pp| / 2 ^ 66) + |v - 2| * (|pp| / 2 ^ 89) =
          |v - 2| * |pp| * (1 / 2 ^ 66 + 1 / 2 ^ 89) := by ring
      linarith
  -- no factor
  rw [show (4 : UInt64) = UInt64.ofNat 4 from rfl, ite_eq_right (hne 4 (by norm_num) hk4)] at hQ
  rw [show (10 : UInt64) = UInt64.ofNat 10 from rfl, ite_eq_right (hne 10 (by norm_num) hk10)] at hR
  rw [hR, hQ]
  simp only
  have hpa' : LgammaApprox.pieceApprox k v = pp := by rw [hpa]; simp [hk4, hk10]
  rw [hpa']
  refine ⟨hp1, hp2, by linarith, ?_, hp6⟩
  have : 0 ≤ |pp| / 2 ^ 89 := div_nonneg (abs_nonneg _) (by norm_num)
  have h3 : |pp| / 2 ^ 66 + |pp| / 2 ^ 89 = |pp| * (1 / 2 ^ 66 + 1 / 2 ^ 89) := by ring
  linarith

/-- **The pieces of the fast path**: `fh + fl` within `2 eps - |fh|/2^65` of `ln |Γ a|`, with
`eps` the exact `|fh| c1 + c2` less `2 ^ -100`. -/
theorem piece_leaf (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hPF : LgammaApprox.PieceFact) (ax : Float)
    (hax : Finite ax.toBits) (k : ℕ) (hk : k < 19) (jj : UInt64) (hjj : jj.toNat = k)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value ax.toBits)
    (hb1 : value ax.toBits ≤ (LgammaApprox.border (k + 1) : ℝ))
    (hv1 : value ax.toBits ≠ 1) (hv2 : value ax.toBits ≠ 2) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (ax - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - ax) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (ax - 2.0) Q.1 Q.2 else (Q.1, Q.2)) :
    Finite R.1.toBits ∧ Finite R.2.toBits ∧ |value R.2.toBits| ≤ 1 / 2 ^ 38 ∧
      |value R.1.toBits| ≤ 16 ∧
      |GammaBasic.lgamma (value ax.toBits) - (value R.1.toBits + value R.2.toBits)| +
          |value R.1.toBits| / 2 ^ 65 ≤
        2 * (|value R.1.toBits| * (PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℝ) +
          (PolyBound.ratOfWord 0x3AF357C299A88EA7 : ℝ)) - 1 / 2 ^ 100 := by
  obtain ⟨hr1, hr2, hr2b, herr, hpab⟩ :=
    piece_key hF ax hax k hk jj hjj hb0 hb1 hv1 hv2 P Q R hP hQ hR
  have hpf := hPF k hk (value ax.toBits) (by linarith) (by linarith)
  set L := GammaBasic.lgamma (value ax.toBits) with hLdef
  set pA := LgammaApprox.pieceApprox k (value ax.toBits) with hpAdef
  set r1 := value R.1.toBits
  set r2 := value R.2.toBits
  have hc1 := qcast_le c1_bounds.1
  have hc2 := qcast_le c2_bounds.1
  push_cast at hc1 hc2
  have hr1c : |r1| * (869 / 10 ^ 22) ≤ |r1| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
  -- `|L| ≤ |pA| (1 + 1.3 · 10^-19)`, `|pA| ≤ (|r1| + 2^-38 + 2^-1072)(1 + 2^-65)`
  have hL1 : |L| ≤ |pA| + 12 / 10 ^ 20 * |L| := by
    have := abs_sub_abs_le_abs_sub L pA
    linarith
  have hpA1 : |pA| ≤ |r1| + |r2| + (|pA| * (1 / 2 ^ 66 + 1 / 2 ^ 89) + 1 / 2 ^ 1072) := by
    have h1 := abs_sub_abs_le_abs_sub pA (r1 + r2)
    have h2 := abs_add_le r1 r2
    rw [abs_sub_comm] at h1
    linarith
  have hpA2 : |pA| ≤ 15 := by linarith
  have hr1b : |r1| ≤ 16 := by
    have h1 := abs_sub_abs_le_abs_sub (r1 + r2) pA
    have h2 := abs_sub_abs_le_abs_sub r1 (-r2)
    rw [sub_neg_eq_add, abs_neg] at h2
    linarith
  refine ⟨hr1, hr2, hr2b, hr1b, ?_⟩
  have hmain : |L - (r1 + r2)| ≤ 12 / 10 ^ 20 * |L| +
      (|pA| * (1 / 2 ^ 66 + 1 / 2 ^ 89) + 1 / 2 ^ 1072) := by
    have h1 := abs_sub_le L pA (r1 + r2)
    rw [abs_sub_comm pA] at h1
    linarith
  linarith [abs_nonneg r1]

#print axioms piece_key
#print axioms piece_leaf
#print axioms eps_value

end Library.Numerics.Float64.Lgamma.LgammaFastPiece
