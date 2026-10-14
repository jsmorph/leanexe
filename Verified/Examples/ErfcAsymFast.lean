import Verified.Examples.ErfcAsymZ
import Verified.Examples.ErfcAsymRowsT
import Verified.Examples.ErfcAsymIdx
import Verified.Examples.ErfcRecip
import Verified.Examples.ErfcRel
import Verified.Examples.ErfcExp1
import Verified.Examples.ErfcCast

/-!
`erfc_asympt_fast` of `Erfc` for `0x1.713786d9c7c09p+1 < x < 0x1.9db1bb14e15cap+4`.  The code
computes `exp (-x²)` as `(eh, el)` by `exp_1` (`ErfcExp1.exp1_err`), `1/x` as `(yh, yl)` and
`1/x²` as `(uh, ul)` (`ErfcRecip`), the polynomial of the row that `yh` selects at `U = uh + ul`
(`ErfcAsymZ.z_row`, with the row's interval of `x` from `ErfcAsymIdx`), and two products by
`Erfc.dMul` (`ErfcRel.pr_dMul_rel`).  `fast_eq` writes the code as `asymFastHL` followed by the
choice of the error bound (`fin`), and `asym_fast_err` bounds `h + l` within `2^-57 erfc x`.
-/

namespace Verified.Examples.ErfcAsymFast

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcOps ErfcTrack ErfcRound ErfcAsymPoly
  ErfcAsymPlan ErfcAsymZ ErfcAsymIdx ErfcRecip ErfcRel ErfcExp1 FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- The last step of `erfc_asympt_fast`: the error bound from the size of `h`. -/
def fin (c1 c2 c3 : Float) (p : Float × Float) : Float × Float × Float :=
  let (h, l) := p
  if h ≥ c1 then (h, l, c2 * h) else (h, l, c3)

theorem fin_fst (c1 c2 c3 : Float) (p : Float × Float) : (fin c1 c2 c3 p).1 = p.1 := by
  obtain ⟨h, l⟩ := p
  simp only [fin]
  split <;> rfl

theorem fin_snd (c1 c2 c3 : Float) (p : Float × Float) : (fin c1 c2 c3 p).2.1 = p.2 := by
  obtain ⟨h, l⟩ := p
  simp only [fin]
  split <;> rfl

theorem fin_err (c1 c2 c3 : Float) (p : Float × Float) :
    (fin c1 c2 c3 p).2.2 = c2 * p.1 ∨ (fin c1 c2 c3 p).2.2 = c3 := by
  obtain ⟨h, l⟩ := p
  simp only [fin]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `(zh, zl)`: the polynomial of the row at `U = uh + ul`. -/
def zPair (aT : Array UInt64) (one two x : Float) : Float × Float :=
  asymCore aT (13 * Erfc.asymptIndex (one / x)) (Erfc.aMul (one / x) (one / x)).1
    (Fma.fma (two * (one / x)) ((one / x) * Fma.fma (-x) (one / x) one)
      (Erfc.aMul (one / x) (one / x)).2)

/-- The product of the polynomial and `1/x`. -/
def p1Pair (aT : Array UInt64) (one two x : Float) : Float × Float :=
  Erfc.dMul (zPair aT one two x).1 (zPair aT one two x).2 (one / x)
    ((one / x) * Fma.fma (-x) (one / x) one)

/-- `exp (-x²)` from `exp_1`. -/
def ePair (eT : Array UInt64) (x : Float) : Float × Float :=
  Erfc.exp1 eT (-(Erfc.aMul x x).1) (-(Erfc.aMul x x).2)

/-- `(h, l)` of `erfc_asympt_fast` below its last threshold. -/
def asymFastHL (eT aT : Array UInt64) (one two x : Float) : Float × Float :=
  Erfc.dMul (p1Pair aT one two x).1 (p1Pair aT one two x).2 (ePair eT x).1 (ePair eT x).2

theorem fast_eq (x : Float) : Erfc.erfcAsymptFast Erfc.expTable Erfc.asymTable x =
    if x ≥ Float.ofBits 0x4039DB1BB14E15CA then (0.0, 0.0, 1.0)
    else fin (Float.ofBits 0x044151B9A3FDD5C9) (Float.ofBits 0x3BBD900000000000)
      (Float.ofBits 0x0010000000000000) (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x) := by
  unfold Erfc.erfcAsymptFast
  rfl

/-- The rows of `T` by index. -/
theorem rowsT (i : ℕ) (hi : i < 6) : ∀ y ∈ Icc ((loT.getD i 0 : ℚ) : ℝ) (hiT.getD i 0),
    |eval (fastZ (tq i)) (y ^ 2)⁻¹ - y * erfcx y| ≤ (rhoA : ℝ) * (y * erfcx y) := by
  interval_cases i
  exacts [ErfcAsymRowsT.row0, ErfcAsymRowsT.row1, ErfcAsymRowsT.row2, ErfcAsymRowsT.row3,
    ErfcAsymRowsT.row4, ErfcAsymRowsT.row5]

theorem rowT0 : RowT 0 (muT.getD 0 0) := by decide +kernel
theorem rowT1 : RowT 1 (muT.getD 1 0) := by decide +kernel
theorem rowT2 : RowT 2 (muT.getD 2 0) := by decide +kernel
theorem rowT3 : RowT 3 (muT.getD 3 0) := by decide +kernel
theorem rowT4 : RowT 4 (muT.getD 4 0) := by decide +kernel
theorem rowT5 : RowT 5 (muT.getD 5 0) := by decide +kernel

theorem rowT_ok (i : ℕ) (hi : i < 6) : RowT i (muT.getD i 0) := by
  interval_cases i
  exacts [rowT0, rowT1, rowT2, rowT3, rowT4, rowT5]

/-- The intervals of `x` of the rows of `T` contain the arguments that select them. -/
def DomT (i : ℕ) : Prop :=
  (i < 5 → loT.getD i 0 * (ratOfWord (thrT.getD i 0) + 1 / 2 ^ 1075) ≤ 1 - 1 / 2 ^ 53 ∧
      0 ≤ ratOfWord (thrT.getD i 0)) ∧
    (0 < i → 1 + 1 / 2 ^ 53 ≤ hiT.getD i 0 * (ratOfWord (thrT.getD (i - 1) 0) - 1 / 2 ^ 1075) ∧
      1 / 2 ^ 1075 < ratOfWord (thrT.getD (i - 1) 0)) ∧
    (i = 5 → loT.getD 5 0 ≤ ratOfWord 0x400713786D9C7C09) ∧
    (i = 0 → ratOfWord 0x4039DB1BB14E15CA ≤ hiT.getD 0 0)

instance (i : ℕ) : Decidable (DomT i) := by unfold DomT; infer_instance

theorem domT_ok : ∀ i < 6, DomT i := by decide +kernel

theorem exp_lower2 (X : ℝ) (hX : -670 ≤ X) : 1 / 2 ^ 967 ≤ Real.exp X := by
  have h2 : (1 : ℝ) / 2 ^ 967 = Real.exp (-(967 * Real.log 2)) := by
    rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
    norm_num
  rw [h2]
  apply Real.exp_le_exp.mpr
  have := Real.log_two_gt_d9
  linarith

/-- `erfc_asympt_fast`'s `h + l` within `2^-57 erfc x`. -/
theorem asym_fast_err (hF : FmaNearest) (x : Float) (hx : ff x)
    (hlo : (ratOfWord 0x400713786D9C7C09 : ℝ) < fv x) (hhi : fv x < ratOfWord 0x4039DB1BB14E15CA) :
    ff (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).1 ∧
      ff (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).2 ∧
      |fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).1 +
        fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).2 - erfc (fv x)| ≤
          erfc (fv x) / 2 ^ 57 ∧
      |fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).1| ≤ 1 ∧
      |fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).2| ≤ 1 := by
  -- the range of `x`
  have k1 : (2884 / 1000 : ℚ) ≤ ratOfWord 0x400713786D9C7C09 := by decide +kernel
  have k2 : ratOfWord 0x4039DB1BB14E15CA ≤ (2586 / 100 : ℚ) := by decide +kernel
  have q1 : (2884 / 1000 : ℝ) < fv x := lt_of_le_of_lt (by qc k1) hlo
  have q2 : fv x < 2586 / 100 := lt_of_lt_of_le hhi (by qc k2)
  have hX0 : 0 < fv x := by linarith
  have hXX : 0 < fv x * fv x := mul_pos hX0 hX0
  have hXX1 : 83 / 10 ≤ fv x * fv x := by nlinarith
  have hXX2 : fv x * fv x ≤ 669 := by nlinarith
  -- `x²` by `Erfc.aMul`
  obtain ⟨a1, a2, ae1, ae2⟩ := aMul_f hF x x hx hx
    (by rw [abs_of_pos hXX]; linarith [show (669 : ℝ) ≤ 2 ^ 1020 by norm_num])
  rw [abs_of_pos hXX] at ae1 ae2
  have hu0 : 8 ≤ fv (Erfc.aMul x x).1 ∧ fv (Erfc.aMul x x).1 ≤ 6691 / 10 := by
    have h1 := (abs_le.mp ae1).1
    have h2 := (abs_le.mp ae1).2
    have : u * (fv x * fv x) ≤ u * 669 := by gcongr
    have : u * 669 + η ≤ 1 / 10 := by norm_num
    constructor <;> linarith
  have hul0 : |fv (Erfc.aMul x x).2| ≤ 1 / 2 ^ 41 := by
    have e : fv (Erfc.aMul x x).2 = (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2 - fv x * fv x) -
        (fv (Erfc.aMul x x).1 - fv x * fv x) := by ring
    rw [e]
    refine (abs_sub_le' _ _).trans ?_
    have : u * (fv x * fv x) ≤ u * 669 := by gcongr
    have : u * u * (fv x * fv x) ≤ u * u * 669 := by gcongr
    have : u * u * 669 + 2 * η + (u * 669 + η) ≤ 1 / 2 ^ 41 := by norm_num
    linarith
  have hδ : |fv x * fv x - (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2)| ≤ 1 / 2 ^ 95 := by
    rw [abs_sub_comm]
    refine ae2.trans ?_
    have : u * u * (fv x * fv x) ≤ u * u * 669 := by gcongr
    have : u * u * 669 + 2 * η ≤ 1 / 2 ^ 95 := by norm_num
    linarith
  -- `exp (-x²)` by `exp_1`
  obtain ⟨n1f, n1v⟩ := neg_f _ a1
  obtain ⟨n2f, n2v⟩ := neg_f _ a2
  obtain ⟨ef1, ef2, ee, el⟩ := exp1_err hF _ _ n1f n2f (by rw [n1v]; linarith [hu0.2])
    (by rw [n1v]; linarith [hu0.1]) (by rw [n2v, abs_neg]; exact hul0.trans (by norm_num))
  rw [n1v, n2v] at ee el
  set EX := Real.exp (-fv (Erfc.aMul x x).1 + -fv (Erfc.aMul x x).2) with hEX
  have hEX0 : 0 < EX := Real.exp_pos _
  have hEX1 : EX ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu0.1, (abs_le.mp hul0).1])
  have hEXlo : 1 / 2 ^ 967 ≤ EX := exp_lower2 _ (by linarith [hu0.2, (abs_le.mp hul0).2])
  have pE : Pr (ePair Erfc.expTable x).1 (ePair Erfc.expTable x).2 EX EX (EX / 2 ^ 30)
      (EX / 2 ^ 60) :=
    ⟨ef1, ef2, ee.trans (le_of_eq (by ring)), le_of_eq (abs_of_pos hEX0),
      el.trans (le_of_eq (by ring))⟩
  -- `1/x` and `1/x²`
  obtain ⟨df, lf, hY, hyl, hy⟩ := recip_pr hF x hx (by linarith) (by linarith)
  obtain ⟨uf, ulf, hU, hUL⟩ := usq_pr hF x hx (by linarith) (by linarith)
  have pY : Pr (1.0 / x) ((1.0 / x) * Fma.fma (-x) (1.0 / x) 1.0) (1 / fv x) (1 / fv x)
      (11 / 10 * u * (1 / fv x)) (4 * u * u * (1 / fv x)) :=
    ⟨df, lf, hY.trans (le_of_eq (by ring)), le_of_eq (abs_of_pos (one_div_pos.mpr hX0)),
      hyl.trans (le_of_eq (by ring))⟩
  -- the row
  obtain ⟨i, hi6, hidx, hle, hgt⟩ := fast_index (1.0 / x) df
  obtain ⟨d1, d2, d3, d4⟩ := domT_ok i hi6
  have hxlo : ((loT.getD i 0 : ℚ) : ℝ) ≤ fv x := by
    rcases (show i < 5 ∨ i = 5 by omega) with h5 | h5
    · obtain ⟨c1, c2⟩ := d1 h5
      exact dom_lo hX0 hy _ _ (hle h5) c1 c2
    · have := d3 h5
      subst h5
      have : ((loT.getD 5 0 : ℚ) : ℝ) ≤ ratOfWord 0x400713786D9C7C09 := by qc this
      linarith
  have hxhi : fv x ≤ ((hiT.getD i 0 : ℚ) : ℝ) := by
    rcases (show i = 0 ∨ 0 < i by omega) with h0 | h0
    · have := d4 h0
      subst h0
      have : (ratOfWord 0x4039DB1BB14E15CA : ℝ) ≤ ((hiT.getD 0 0 : ℚ) : ℝ) := by qc this
      linarith
    · obtain ⟨c1, c2⟩ := d2 h0
      exact dom_hi hX0 hy _ _ (hgt h0) c1 c2
  obtain ⟨M, pZ, hM1, hM2, hZG⟩ := z_row hF i (muT.getD i 0) (rowT_ok i hi6) (rowsT i hi6)
    (fv x) hxlo hxhi _ _ uf ulf hU hUL
  rw [← hidx] at pZ
  -- the product with `1/x`
  have p1 := pr_dMul_rel hF pZ pY (1 / 2 ^ 67) (1 / 2 ^ 51) (4 * u * u) (11 / 10 * u)
    (le_of_eq (by ring)) (le_of_eq (by ring)) le_rfl le_rfl (by norm_num) (by norm_num)
    (by
      have : 1 / 2 * (1 / (2586 / 100)) ≤ M * (1 / fv x) := by
        apply mul_le_mul hM1 _ (by norm_num) (by linarith)
        exact one_div_le_one_div_of_le hX0 q2.le
      linarith [show (1 : ℝ) / 2 ^ 980 ≤ 1 / 2 * (1 / (2586 / 100)) by norm_num])
    (by linarith) (by
      have : 1 / fv x ≤ 1 := by rw [div_le_one hX0]; linarith
      linarith)
  -- the product with `exp (-x²)`
  have p2 := pr_dMul_rel hF p1 pE _ _ (1 / 2 ^ 60) (1 / 2 ^ 30) le_rfl le_rfl
    (le_of_eq (by ring)) (le_of_eq (by ring)) (by norm_num) (by norm_num)
    (by
      have h1 : 1 / 2 * (1 / (2586 / 100)) ≤ M * (1 / fv x) := by
        apply mul_le_mul hM1 _ (by norm_num) (by linarith)
        exact one_div_le_one_div_of_le hX0 q2.le
      have h2 : 1 / 2 * (1 / (2586 / 100)) * (1 / 2 ^ 967) ≤ M * (1 / fv x) * EX :=
        mul_le_mul h1 hEXlo (by norm_num) (mul_nonneg (by linarith) (one_div_nonneg.mpr hX0.le))
      linarith [show (1 : ℝ) / 2 ^ 980 ≤ 1 / 2 * (1 / (2586 / 100)) * (1 / 2 ^ 967) by norm_num])
    (by
      have h1 : 1 / fv x ≤ 1 := by rw [div_le_one hX0]; linarith
      have : M * (1 / fv x) ≤ 1 * 1 := mul_le_mul hM2 h1 (one_div_nonneg.mpr hX0.le) (by norm_num)
      linarith)
    (by linarith)
  -- the result as `asymFastHL`
  have p2' : Pr (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).1
      (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).2 _ _ _ _ := p2
  have hM0 : 0 ≤ M := by linarith
  have hxi : 1 / fv x ≤ 1 / 2 := by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith
  have hP0 : 0 ≤ M * (1 / fv x) * EX :=
    mul_nonneg (mul_nonneg hM0 (one_div_nonneg.mpr hX0.le)) hEX0.le
  have hPle : M * (1 / fv x) * EX ≤ 1 / 2 :=
    (mul_le_mul (mul_le_mul hM2 hxi (one_div_nonneg.mpr hX0.le) (by norm_num)) hEX1 hEX0.le
      (by norm_num)).trans (le_of_eq (by norm_num))
  have hh := Pr.h_le p2'
  have hl := p2'.2.2.2.2
  have hf1 := p2'.1
  have hf2 := p2'.2.1
  have herr := p2'.2.2.1
  -- `erfc x` from `x erfcx x`
  have hG := G_bounds (fv x) (by linarith)
  have hG1 : 49 / 100 ≤ fv x * erfcx (fv x) := hG.1
  have hXne : fv x ≠ 0 := hX0.ne'
  set G := fv x * erfcx (fv x) with hGdef
  set E0 := Real.exp (-(fv x) ^ 2) with hE0
  have hE00 : 0 < E0 := Real.exp_pos _
  have herfc : erfc (fv x) = E0 / fv x * G := by
    rw [erfc_eq, hGdef, hE0]
    field_simp
  set δ := fv x * fv x - (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2) with hδdef
  have hEXd : EX = E0 * Real.exp δ := by
    rw [hEX, hE0, hδdef, ← Real.exp_add]
    congr 1
    ring
  have hδ1 : |Real.exp δ - 1| ≤ 1 / 2 ^ 94 := by
    have := Real.abs_exp_sub_one_le (hδ.trans (by norm_num))
    linarith
  have hed : Real.exp δ ≤ 1 + 1 / 2 ^ 94 := by linarith [(abs_le.mp hδ1).2]
  have hed0 : 0 < Real.exp δ := Real.exp_pos _
  set w := E0 / fv x with hw
  have hw0 : 0 < w := div_pos hE00 hX0
  have hMX : M * (1 / fv x) * EX = M * w * Real.exp δ := by
    rw [hEXd, hw]; ring
  set Z := eval (fastZ (tq i)) (fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 +
      fv (Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) * Fma.fma (-x) (1.0 / x) 1.0)
        (Erfc.aMul (1.0 / x) (1.0 / x)).2)) with hZ
  have hV : Z * (1 / fv x) * EX = Z * w * Real.exp δ := by
    rw [hEXd, hw]; ring
  rw [hV, hMX] at herr
  have hMe : M * Real.exp δ ≤ 1 + 1 / 2 ^ 94 :=
    (mul_le_mul hM2 hed hed0.le (by norm_num)).trans (le_of_eq (one_mul _))
  have hZe : |Z * Real.exp δ - G| ≤ G / 2 ^ 60 * (1 + 1 / 2 ^ 94) + G * (1 / 2 ^ 94) := by
    have e : Z * Real.exp δ - G = (Z - G) * Real.exp δ + G * (Real.exp δ - 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hed0, abs_of_pos (by linarith : (0 : ℝ) < G)]
    have t1 : |Z - G| * Real.exp δ ≤ G / 2 ^ 60 * (1 + 1 / 2 ^ 94) :=
      mul_le_mul hZG hed hed0.le (by linarith)
    have t2 : G * |Real.exp δ - 1| ≤ G * (1 / 2 ^ 94) :=
      mul_le_mul_of_nonneg_left hδ1 (by linarith)
    linarith
  refine ⟨hf1, hf2, ?_, ?_, ?_⟩
  · rw [herfc]
    have t := abs_sub_le (fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).1 +
      fv (asymFastHL Erfc.expTable Erfc.asymTable 1.0 2.0 x).2) (Z * w * Real.exp δ) (w * G)
    have t2 : |Z * w * Real.exp δ - w * G| = w * |Z * Real.exp δ - G| := by
      rw [show Z * w * Real.exp δ - w * G = w * (Z * Real.exp δ - G) by ring, abs_mul,
        abs_of_pos hw0]
    have t4 : w * |Z * Real.exp δ - G| ≤ w * (G / 2 ^ 60 * (1 + 1 / 2 ^ 94) + G * (1 / 2 ^ 94)) :=
      mul_le_mul_of_nonneg_left hZe hw0.le
    have hw49 : w * (49 / 100) ≤ w * G := mul_le_mul_of_nonneg_left hG.1 hw0.le
    have hwMe : w * (M * Real.exp δ) ≤ w * (1 + 1 / 2 ^ 94) := mul_le_mul_of_nonneg_left hMe hw0.le
    have hwG0 : 0 ≤ w * G := mul_nonneg hw0.le (by linarith)
    linarith only [t, t2, t4, hw49, hwMe, hwG0, herr, hw0]
  · linarith only [hh, hPle, hP0]
  · linarith only [hl, hPle, hP0]

#print axioms asym_fast_err

end Verified.Examples.ErfcAsymFast
