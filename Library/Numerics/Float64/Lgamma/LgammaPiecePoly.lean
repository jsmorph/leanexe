import Library.Numerics.Float64.Lgamma.LgammaFastSmall

/-!
The double-double polynomial of the fast path's 19 pieces, `Lgamma.piecePoly`.  Piece `j` evaluates
the tail of degree 7, with the words `39 + 8 j` to `46 + 8 j`, in plain double arithmetic (`tE j`,
bounded by `TgammaExpr`), adds it to the top of the double-double Horner scheme of degree 4 with
the pairs at word `191 + 10 j` (`Lgamma.polyDDDFst`), and so approximates `LgammaApprox.piecePoly j`
at `z`.  For `|z| ≤ pX j`, which covers the piece widened by `2 ^ -50` about its offset, kernel
checks bound the Horner values (`hbQ`) and check that each coefficient dominates the product before
it, as `LgammaPolyFst.polyFst_damped_core` requires.  The error is at most `pE j`, which the kernel
checks against `2 ^ -66` of the smallest value `pLow j` of the polynomial on the piece
(`piece_poly`); the largest ratio, on piece 5, is `6.1 · 10 ^ -21`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiecePoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaExpr
  TgammaWords LgammaPolyFst LgammaFastSmall

set_option exponentiation.threshold 4096

/-- Word `i` of `Lgamma.mainTable`. -/
abbrev wq (i : ℕ) : UInt64 := Lgamma.mainTable[i]!

/-- The tail of piece `j`: `z ((q0 + z² q2) + z⁴ (q4 + z² q6))` with `qi = t i + z t (i + 1)` and
`t i` word `39 + 8 j + i`. -/
def tE (j : ℕ) : FE :=
  .mul .var (.add (.add (lin (wq (39 + 8 * j)) (wq (39 + 8 * j + 1)))
      (.mul x2E (lin (wq (39 + 8 * j + 2)) (wq (39 + 8 * j + 3)))))
    (.mul x4E (.add (lin (wq (39 + 8 * j + 4)) (wq (39 + 8 * j + 5)))
      (.mul x2E (lin (wq (39 + 8 * j + 6)) (wq (39 + 8 * j + 7)))))))

/-- The bound on `|z|` on piece `j`: the larger distance from the offset to a border, plus
`2 ^ -50`, rounded up to a multiple of `2 ^ -16`. -/
def pX (j : ℕ) : ℚ :=
  [2615 / 65536, 2953 / 65536, 3293 / 65536, 1799 / 32768, 4715 / 65536, 4329 / 65536,
    5259 / 65536, 191 / 2048, 3467 / 32768, 7475 / 65536, 10731 / 65536, 2783 / 16384,
    13653 / 65536, 8319 / 32768, 5061 / 16384, 24637 / 65536, 14987 / 32768, 2283 / 4096,
    11167 / 16384].getD j 0

/-- The exact values of the high and the low word of coefficient `k` of piece `j`. -/
abbrev hiQ (j k : ℕ) : ℚ := PolyBound.ratOfWord (wq (191 + 10 * j + 2 * k))
abbrev loQ (j k : ℕ) : ℚ := PolyBound.ratOfWord (wq (191 + 10 * j + 2 * k + 1))

/-- The bound on the Horner value of step `m`: `|c 4| + |tail|`, then `|c (3 - m)| + X` times the
bound of the step before. -/
def hbQ (j : ℕ) : ℕ → ℚ
  | 0 => PolyBound.qabs (hiQ j 4 + loQ j 4) + (bnd (tE j) (pX j)).1
  | m + 1 => PolyBound.qabs (hiQ j (3 - m) + loQ j (3 - m)) + pX j * hbQ j m

/-- `polyLow` and `polyEps` with `M = 10`, `Ch = 8`, `Cl = 2 ^ -50`, and `Λ = 2 ^ -40`. -/
def polyLowQ (X : ℚ) : ℚ :=
  1 / 2 ^ 50 + 1 / 2 ^ 40 * X * (1 + 1 / 2 ^ 51) + (10 + 1) * X / 2 ^ 52 + 1 / 2 ^ 1071

def polyEpsQ (X : ℚ) : ℚ :=
  (3 * (1 / 2 ^ 40 * X) + (10 + 1) * X / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 +
    (3 * polyLowQ X + 2 * (8 + 10 + 1) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53

/-- The error bound of piece `j`. -/
def pE (j : ℕ) : ℚ :=
  pX j ^ 4 * ((bnd (tE j) (pX j)).2 + (1 / 2 ^ 48 + 1 / 2 ^ 50) / 2 ^ 53) + 4 * polyEpsQ (pX j)

/-- The smallest value of the polynomial of piece `j` on `|z| ≤ pX j`, from `|c 0| - X` times the
bound of step 3. -/
def pLow (j : ℕ) : ℚ := PolyBound.qabs (hiQ j 0 + loQ j 0) - pX j * hbQ j 3

theorem fin_ok : ∀ j < 19, ∀ k < 5, Wasm.IEEE64.isFinite (wq (191 + 10 * j + 2 * k)) = true ∧
    Wasm.IEEE64.isFinite (wq (191 + 10 * j + 2 * k + 1)) = true := by
  decide +kernel

theorem ok_all : ∀ j < 19, ok (tE j) (pX j) = true := by decide +kernel

theorem pX_ok : ∀ j < 19, 0 ≤ pX j ∧ pX j ≤ 1 := by decide +kernel

theorem top_ok : ∀ j < 19, (bnd (tE j) (pX j)).1 + (bnd (tE j) (pX j)).2 ≤
    PolyBound.qabs (hiQ j 4) ∧ (bnd (tE j) (pX j)).1 + (bnd (tE j) (pX j)).2 ≤ 1 := by
  decide +kernel

theorem ch_ok : ∀ j < 19, ∀ k < 5,
    PolyBound.qabs (hiQ j k) ≤ 8 ∧ PolyBound.qabs (loQ j k) ≤ 1 / 2 ^ 50 := by
  decide +kernel

theorem hb_ok : ∀ j < 19, ∀ m < 5, hbQ j m ≤ 10 := by decide +kernel

theorem dom_ok : ∀ j < 19, ∀ m < 4, (hbQ j m + 1 / 2 ^ 39) * pX j * (1 + 1 / 2 ^ 53) +
    1 / 2 ^ 1075 ≤ PolyBound.qabs (hiQ j (3 - m)) := by
  decide +kernel

theorem delta_ok : ∀ j < 19, (bnd (tE j) (pX j)).2 + (1 / 2 ^ 48 + 1 / 2 ^ 50) / 2 ^ 53 +
    4 * polyEpsQ (pX j) + 1 / 2 ^ 40 ≤ 1 / 2 ^ 39 := by
  decide +kernel

theorem low_ok : ∀ j < 19, 0 < pLow j ∧ pE j ≤ pLow j / 2 ^ 66 := by decide +kernel

theorem polyEps_cast (X : ℚ) :
    polyEps (X : ℝ) 10 8 (1 / 2 ^ 50) (1 / 2 ^ 40) = (polyEpsQ X : ℝ) := by
  simp only [polyEps, polyLow, polyEpsQ, polyLowQ]
  push_cast
  ring

theorem qcast_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

/-- Coefficient `k` of piece `j` as a rational. -/
theorem cDD_eq (j : ℕ) (o : UInt64) (ho : o.toNat = 191 + 10 * j) (k : ℕ)
    (h1 : Wasm.IEEE64.isFinite (wq (191 + 10 * j + 2 * k)) = true)
    (h2 : Wasm.IEEE64.isFinite (wq (191 + 10 * j + 2 * k + 1)) = true) :
    cDD Lgamma.mainTable o k = ((hiQ j k + loQ j k : ℚ) : ℝ) := by
  rw [cDD_rat Lgamma.mainTable o k (by rw [ho]; exact h1) (by rw [ho]; exact h2), ho]

/-- `evalR (tE j) x = x Q(x)` with `Q` the coefficients at word `39 + 8 j`. -/
theorem tE_eval (j : ℕ) (x : ℝ) :
    evalR (tE j) x = x * PolyBound.eval (Library.Numerics.Float64.Tgamma.TgammaApprox.coeffs Lgamma.mainTable (39 + 8 * j) 1 8) x := by
  rw [eval_coeffs]
  simp only [evalR, tE, lin, x2E, x4E, wq, Library.Numerics.Float64.Tgamma.TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, one_mul, add_zero, zero_add, pow_zero, pow_one, mul_one]
  ring

/-- The exact Horner value of piece `j` is `LgammaApprox.piecePoly j`. -/
theorem horner_piece (j : ℕ) (hj : j < 19) (o : UInt64) (ho : o.toNat = 191 + 10 * j) (x : ℝ) :
    horner (cDD Lgamma.mainTable o) 5 (evalR (tE j) x) x 4 = LgammaApprox.piecePoly j x := by
  rw [show (4 : ℕ) = 5 - 1 from rfl, horner_eval _ 5 (by norm_num)]
  have hs : LgammaApprox.piecePoly j x = PolyBound.eval
      (Library.Numerics.Float64.Tgamma.TgammaApprox.ddCoeffs Lgamma.mainTable (191 + 10 * j) 5 ++
        Library.Numerics.Float64.Tgamma.TgammaApprox.coeffs Lgamma.mainTable (39 + 8 * j) 1 8) x := rfl
  rw [hs, eval_append, eval_ddCoeffs, tE_eval]
  have hc : ∀ k ∈ Finset.range 5, cDD Lgamma.mainTable o k * x ^ k =
      ((Library.Numerics.Float64.Tgamma.TgammaApprox.q Lgamma.mainTable (191 + 10 * j + 2 * k) +
        Library.Numerics.Float64.Tgamma.TgammaApprox.q Lgamma.mainTable (191 + 10 * j + 2 * k + 1) : ℚ) : ℝ) * x ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cDD_eq j o ho k (fin_ok j hj k hk).1 (fin_ok j hj k hk).2]
    rfl
  rw [Finset.sum_congr rfl hc]
  simp only [Library.Numerics.Float64.Tgamma.TgammaApprox.ddCoeffs, List.length_map, List.length_range]
  ring

/-- The Horner values of piece `j` are bounded by `hbQ j`. -/
theorem horner_le (j : ℕ) (hj : j < 19) (o : UInt64) (ho : o.toNat = 191 + 10 * j) (L x : ℝ)
    (hx : |x| ≤ (pX j : ℝ)) (hL : |L| ≤ ((bnd (tE j) (pX j)).1 : ℝ)) :
    ∀ m ≤ 4, |horner (cDD Lgamma.mainTable o) 5 L x m| ≤ (hbQ j m : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [show horner (cDD Lgamma.mainTable o) 5 L x 0 = cDD Lgamma.mainTable o 4 + L from rfl,
      cDD_eq j o ho 4 (fin_ok j hj 4 (by norm_num)).1 (fin_ok j hj 4 (by norm_num)).2, hbQ]
    push_cast
    rw [qabs_cast]
    push_cast
    have := abs_add_le ((hiQ j 4 : ℝ) + (loQ j 4 : ℝ)) L
    linarith
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [show horner (cDD Lgamma.mainTable o) 5 L x (m + 1) =
        cDD Lgamma.mainTable o (5 - 2 - m) + x * horner (cDD Lgamma.mainTable o) 5 L x m from rfl,
      show 5 - 2 - m = 3 - m by omega,
      cDD_eq j o ho (3 - m) (fin_ok j hj (3 - m) (by omega)).1 (fin_ok j hj (3 - m) (by omega)).2,
      hbQ]
    push_cast
    rw [qabs_cast]
    push_cast
    have h2 := abs_add_le ((hiQ j (3 - m) : ℝ) + (loQ j (3 - m) : ℝ))
      (x * horner (cDD Lgamma.mainTable o) 5 L x m)
    have h3 : |x * horner (cDD Lgamma.mainTable o) 5 L x m| ≤ (pX j : ℝ) * (hbQ j m : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hx h1 (abs_nonneg _) (by exact_mod_cast (pX_ok j hj).1)
    linarith

/-- **The polynomial of piece `j`** at a double `|z| ≤ pX j`: within `pE j` of
`LgammaApprox.piecePoly j z`, with a low part below `2 ^ -40`, and the polynomial between `pLow j`
and 10 in magnitude. -/
theorem piece_poly (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (j : ℕ) (hj : j < 19) (o : UInt64)
    (ho : o.toNat = 191 + 10 * j) (z : Float) (hz : Finite z.toBits)
    (hX : |value z.toBits| ≤ (pX j : ℝ)) (P : Float × Float)
    (hP : P = Lgamma.polyDDDFst Lgamma.mainTable o 5 z (evalF (tE j) z)) :
    Finite P.1.toBits ∧ Finite P.2.toBits ∧
      |value P.1.toBits + value P.2.toBits - LgammaApprox.piecePoly j (value z.toBits)| ≤
        (pE j : ℝ) ∧
      |value P.2.toBits| ≤ 1 / 2 ^ 40 ∧
      (pLow j : ℝ) ≤ |LgammaApprox.piecePoly j (value z.toBits)| ∧
      |LgammaApprox.piecePoly j (value z.toBits)| ≤ 10 := by
  obtain ⟨hl, hLm⟩ := evalF_approx (tE j) (pX j) z hz hX (ok_all j hj)
  set vz := value z.toBits with hvz
  set L := evalR (tE j) vz with hLdef
  have hel : |value (evalF (tE j) z).toBits - L| ≤ ((bnd (tE j) (pX j)).2 : ℝ) := hl.2
  have hlb : |value (evalF (tE j) z).toBits| ≤
      ((bnd (tE j) (pX j)).1 : ℝ) + ((bnd (tE j) (pX j)).2 : ℝ) := by
    have := abs_sub_abs_le_abs_sub (value (evalF (tE j) z).toBits) L
    linarith
  have hX0 : (0 : ℝ) ≤ (pX j : ℝ) := by exact_mod_cast (pX_ok j hj).1
  have hX1 : (pX j : ℝ) ≤ 1 := by exact_mod_cast (pX_ok j hj).2
  have hTB1 : ((bnd (tE j) (pX j)).1 : ℝ) + ((bnd (tE j) (pX j)).2 : ℝ) ≤ 1 := by
    have := qcast_le (top_ok j hj).2
    push_cast at this
    linarith
  have h5 : (5 : UInt64).toNat = 5 := rfl
  have hfh : ∀ k < (5 : UInt64).toNat,
      Finite (Float.ofBits Lgamma.mainTable[o.toNat + 2 * k]!).toBits := by
    intro k hk
    rw [ho]
    exact ofBits_finite _ (fin_ok j hj k (by rw [h5] at hk; exact hk)).1
  have hfl : ∀ k < (5 : UInt64).toNat,
      Finite (Float.ofBits Lgamma.mainTable[o.toNat + 2 * k + 1]!).toBits := by
    intro k hk
    rw [ho]
    exact ofBits_finite _ (fin_ok j hj k (by rw [h5] at hk; exact hk)).2
  have hCh : ∀ k < (5 : UInt64).toNat,
      |value (Float.ofBits Lgamma.mainTable[o.toNat + 2 * k]!).toBits| ≤ 8 := by
    intro k hk
    rw [h5] at hk
    rw [ho, ofBits_value _ (fin_ok j hj k hk).1]
    have := abs_rat_le _ _ (ch_ok j hj k hk).1
    push_cast at this
    exact this
  have hCl : ∀ k < (5 : UInt64).toNat,
      |value (Float.ofBits Lgamma.mainTable[o.toNat + 2 * k + 1]!).toBits| ≤ 1 / 2 ^ 50 := by
    intro k hk
    rw [h5] at hk
    rw [ho, ofBits_value _ (fin_ok j hj k hk).2]
    have := abs_rat_le _ _ (ch_ok j hj k hk).2
    push_cast at this
    exact this
  have htop : |value (evalF (tE j) z).toBits| ≤
      |value (Float.ofBits Lgamma.mainTable[o.toNat + 2 * ((5 : UInt64).toNat - 1)]!).toBits| := by
    rw [show o.toNat + 2 * ((5 : UInt64).toNat - 1) = 191 + 10 * j + 2 * 4 by rw [ho]; rfl,
      ofBits_value _ (fin_ok j hj 4 (by norm_num)).1, ← qabs_cast]
    have := qcast_le (top_ok j hj).1
    push_cast at this
    exact hlb.trans this
  have hHb := horner_le j hj o ho L vz hX hLm
  have hM : ∀ m, m + 1 ≤ (5 : UInt64).toNat →
      |horner (cDD Lgamma.mainTable o) (5 : UInt64).toNat L vz m| ≤ 10 := by
    intro m hm
    rw [h5] at hm ⊢
    have := qcast_le (hb_ok j hj m (by omega))
    push_cast at this
    exact (hHb m (by omega)).trans this
  have hδ : ((bnd (tE j) (pX j)).2 : ℝ) + (1 / 2 ^ 48 + 1 / 2 ^ 50) / 2 ^ 53 +
      ((5 : UInt64).toNat - 1 : ℕ) * polyEps (pX j : ℝ) 10 8 (1 / 2 ^ 50) (1 / 2 ^ 40) +
      1 / 2 ^ 40 ≤ 1 / 2 ^ 39 := by
    rw [h5, polyEps_cast]
    have := qcast_le (delta_ok j hj)
    push_cast at this ⊢
    linarith
  have hdom : ∀ m, m + 2 ≤ (5 : UInt64).toNat →
      (|horner (cDD Lgamma.mainTable o) (5 : UInt64).toNat L vz m| + 1 / 2 ^ 39) * (pX j : ℝ) *
          (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |value (Float.ofBits Lgamma.mainTable[o.toNat + 2 * ((5 : UInt64).toNat - 2 - m)]!).toBits| := by
    intro m hm
    rw [h5] at hm ⊢
    rw [show o.toNat + 2 * (5 - 2 - m) = 191 + 10 * j + 2 * (3 - m) by omega,
      ofBits_value _ (fin_ok j hj (3 - m) (by omega)).1, ← qabs_cast]
    have h1 : ((((hbQ j m + 1 / 2 ^ 39) * pX j * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 : ℚ)) : ℝ) ≤
        ((PolyBound.qabs (PolyBound.ratOfWord (wq (191 + 10 * j + 2 * (3 - m)))) : ℚ) : ℝ) :=
      qcast_le (dom_ok j hj m (by omega))
    push_cast at h1
    have h2 := hHb m (by omega)
    have h3 : (|horner (cDD Lgamma.mainTable o) 5 L vz m| + 1 / 2 ^ 39) * (pX j : ℝ) *
        (1 + 1 / 2 ^ 53) ≤ ((hbQ j m : ℝ) + 1 / 2 ^ 39) * (pX j : ℝ) * (1 + 1 / 2 ^ 53) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hX0) (by positivity)
    linarith
  have htBh : polyT 8 (((bnd (tE j) (pX j)).1 : ℝ) + ((bnd (tE j) (pX j)).2 : ℝ)) ≤ 1 / 2 ^ 48 := by
    rw [polyT]
    have h1 : ((8 + (((bnd (tE j) (pX j)).1 : ℝ) + ((bnd (tE j) (pX j)).2 : ℝ))) *
        (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 ≤
        ((8 + 1) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 := by
      gcongr
    linarith [(by norm_num : ((8 + 1 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 +
      1 / 2 ^ 1074 ≤ 1 / 2 ^ 48)]
  obtain ⟨h1, h2, h3, h4⟩ := polyFst_damped_core hF Lgamma.mainTable o 5 z (evalF (tE j) z)
    (by rw [h5]; norm_num) (by rw [ho, h5]; omega) hfh hfl (pX j : ℝ) 10 8 (1 / 2 ^ 50)
    (1 / 2 ^ 40) L ((bnd (tE j) (pX j)).2 : ℝ)
    (((bnd (tE j) (pX j)).1 : ℝ) + ((bnd (tE j) (pX j)).2 : ℝ)) (1 / 2 ^ 48) hz hX hX1 hCh hCl hl.1 hel hlb htop hM (Or.inr htBh)
    (by norm_num) (by norm_num)
    (by rw [h5]; simp only [polyGrow]; norm_num)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 39 ≤ 1)])
    (by norm_num) (by linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 50 ≤ 2 ^ 797)]) (by norm_num)
    (1 / 2 ^ 39) hδ (by norm_num) hdom
  rw [← hP] at h1 h2 h3 h4
  have hh : horner (cDD Lgamma.mainTable o) 5 L vz 4 = LgammaApprox.piecePoly j vz :=
    horner_piece j hj o ho vz
  rw [h5, show 5 - 1 = 4 from rfl, hh] at h3
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · refine h3.trans (le_of_eq ?_)
    rw [polyEps_cast, pE]
    push_cast
    ring
  · -- `|c 0 + z h 3| ≥ |c 0| - X h 3`
    rw [← hh, show horner (cDD Lgamma.mainTable o) 5 L vz 4 = cDD Lgamma.mainTable o 0 +
        vz * horner (cDD Lgamma.mainTable o) 5 L vz 3 from rfl,
      cDD_eq j o ho 0 (fin_ok j hj 0 (by norm_num)).1 (fin_ok j hj 0 (by norm_num)).2, pLow]
    push_cast
    rw [qabs_cast]
    push_cast
    have h5' := abs_sub_abs_le_abs_sub ((hiQ j 0 : ℝ) + (loQ j 0 : ℝ))
      (-(vz * horner (cDD Lgamma.mainTable o) 5 L vz 3))
    rw [sub_neg_eq_add, abs_neg] at h5'
    have h6 : |vz * horner (cDD Lgamma.mainTable o) 5 L vz 3| ≤ (pX j : ℝ) * (hbQ j 3 : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hX (hHb 3 (by norm_num)) (abs_nonneg _) hX0
    linarith
  · rw [← hh]
    have := qcast_le (hb_ok j hj 4 (by norm_num))
    push_cast at this
    exact (hHb 4 le_rfl).trans this

#print axioms piece_poly

end Library.Numerics.Float64.Lgamma.LgammaPiecePoly
