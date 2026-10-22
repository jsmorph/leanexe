import Library.Numerics.Float64.Erfc.ErfcTaccData
import Library.Numerics.Float64.Erfc.ErfcAsymRowsA0
import Library.Numerics.Float64.Erfc.ErfcAsymRowsA1
import Library.Numerics.Float64.Erfc.ErfcAsymZ
import Library.Numerics.Float64.Erfc.ErfcAsymIdx
import Library.Numerics.Float64.Erfc.ErfcRecip
import Library.Numerics.Float64.Erfc.ErfcRel
import Library.Numerics.Float64.Erfc.ErfcEAcc
import LeanExe.ProofKit.TaylorRemainder
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`erfc_asympt_accurate` of `Erfc` before its final scaling, for
`0x1.b59ffb450828cp+0 < x < 0x1.b39dc41e48bfdp+4`.  The code computes `exp (-x²)` as
`(eh + el) 2^K` by `exp_accurate` (`ErfcEAcc.expAcc_err`), `1/x` and `1/x²` as double-doubles
(`ErfcRecip`), the polynomial of the row of `Tacc` that `yh` selects at `U = uh + ul`
(`ErfcTaccLoop.loopA`, `loopB`, with the row's data from `ErfcTaccData` and its certificate from
`ErfcAsymRowsA0` and `ErfcAsymRowsA1`), and two products by `Erfc.dMul` with a renormalization
between them.  `asymAcc_eq` writes the code as `aaHL`, which returns `(h, l, K)`, followed by the
scaling `finA`, and `aa_hl` bounds `(h + l) 2^K` within `2^-56 erfc x`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcAsymAccHL

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcEft2 ErfcOps ErfcTrack ErfcTrack5 ErfcRound ErfcTaccLoop
  ErfcTaccRows ErfcAsymPlan ErfcAsymZ ErfcAsymIdx ErfcRecip ErfcRel ErfcEAcc ErfcAccMain FmaSpec
  PolyBound PolyCalculus RealErf

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- The final scaling of `erfc_asympt_accurate`, with the correction of a subnormal result. -/
def finA (t : Float × Float × Float) : Float :=
  let (h, l, e) := t
  let res := Erfc.ldexp (h + l) e
  if res < Float.ofBits 0x0010000000000000 then
    let corr := h - Erfc.ldexp res (-e)
    let corr := corr + l
    res + Erfc.ldexp corr e
  else res

/-- `(uh, ul)`, the double-double `1/x²`. -/
def uPair (one two x : Float) : Float × Float :=
  ((Erfc.aMul (one / x) (one / x)).1,
    Library.Numerics.Arithmetic.Fma.Fma.fma (two * (one / x)) ((one / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (one / x) one)
      (Erfc.aMul (one / x) (one / x)).2)

/-- The polynomial of the row of `Tacc` at `U`, after the two loops. -/
def zA (tab : Array UInt64) (one two x : Float) : Float × Float :=
  LeanExe.loop 6
    (LeanExe.loop (8 + Erfc.asymptAccIndex (one / x))
      (Erfc.entry tab (30 * Erfc.asymptAccIndex (one / x) + 20 + Erfc.asymptAccIndex (one / x)),
        (0.0 : Float)) fun j s =>
      tStep (uPair one two x).1 (uPair one two x).2
        (Erfc.entry tab (30 * Erfc.asymptAccIndex (one / x) + 19 + Erfc.asymptAccIndex (one / x) -
          j)) s)
    fun j s => tStepB (uPair one two x).1 (uPair one two x).2
      (Erfc.entry tab (30 * Erfc.asymptAccIndex (one / x) + 10 - 2 * j))
      (Erfc.entry tab (30 * Erfc.asymptAccIndex (one / x) + 11 - 2 * j)) s

/-- The product with `1/x`, renormalized. -/
def p1A (tab : Array UInt64) (one two x : Float) : Float × Float :=
  Erfc.fastTwoSum (Erfc.dMul (zA tab one two x).1 (zA tab one two x).2 (one / x)
      ((one / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (one / x) one)).1
    (Erfc.dMul (zA tab one two x).1 (zA tab one two x).2 (one / x)
      ((one / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (one / x) one)).2

/-- `exp (-x²)` as `(eh, el, K)` from `exp_accurate`. -/
def eA (eT : Array UInt64) (x : Float) : Float × Float × Float :=
  Erfc.expAccurate eT (-(Erfc.aMul x x).1) (-(Erfc.aMul x x).2)

/-- `(h, l, K)` of `erfc_asympt_accurate` before the scaling. -/
def aaHL (eT tab : Array UInt64) (one two x : Float) : Float × Float × Float :=
  ((Erfc.dMul (p1A tab one two x).1 (p1A tab one two x).2 (eA eT x).1 (eA eT x).2.1).1,
    (Erfc.dMul (p1A tab one two x).1 (p1A tab one two x).2 (eA eT x).1 (eA eT x).2.1).2,
    (eA eT x).2.2)

theorem asymAcc_eq (x : Float) :
    Erfc.asymptAccurate Erfc.expAccTable Erfc.asymAccTable x =
      finA (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x) := by
  unfold Erfc.asymptAccurate
  rfl

/-- `x erfcx x` for `x ≥ 3/2`. -/
theorem G_bounds2 (x : ℝ) (hx : 3 / 2 ≤ x) : 43 / 100 ≤ x * erfcx x ∧ x * erfcx x ≤ 57 / 100 := by
  have hx0 : 0 < x := by linarith
  have e1 : asymSum 1 x = x⁻¹ := by
    norm_num [asymSum, Finset.sum_range_succ, asymCoeff]
  have e2 : asymSum 2 x = x⁻¹ - x⁻¹ ^ 3 / 2 := by
    norm_num [asymSum, Finset.sum_range_succ, asymCoeff]
    ring
  have h1 := erfcx_asym 1 hx0
  have h2 := erfcx_asym 2 hx0
  rw [e1, pow_one, neg_one_mul] at h1
  rw [e2, neg_one_sq, one_mul] at h2
  have hsl := ErfcSeries.scale_lo
  have hsh := ErfcSeries.scale_hi
  have hs0 := scale_pos
  have qsl : (112 / 100 : ℝ) ≤ ErfcSeries.sLo := by
    have : (112 / 100 : ℚ) ≤ ErfcSeries.sLo := by decide +kernel
    qc this
  have qsh : (ErfcSeries.sHi : ℝ) ≤ 113 / 100 := by
    have : ErfcSeries.sHi ≤ (113 / 100 : ℚ) := by decide +kernel
    qc this
  have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  have ht0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have ht1 : x⁻¹ ≤ 2 / 3 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hup : erfcx x ≤ scale / 2 * x⁻¹ := by linarith
  have hlow : scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2) ≤ erfcx x := by linarith
  constructor
  · have k := mul_le_mul_of_nonneg_left hlow hx0.le
    have e3 : x * x⁻¹ ^ 3 = x⁻¹ ^ 2 := by
      calc x * x⁻¹ ^ 3 = (x * x⁻¹) * x⁻¹ ^ 2 := by ring
        _ = x⁻¹ ^ 2 := by rw [hxi, one_mul]
    have e : x * (scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2)) = scale / 2 * (1 - x⁻¹ ^ 2 / 2) := by
      calc x * (scale / 2 * (x⁻¹ - x⁻¹ ^ 3 / 2)) = scale / 2 * (x * x⁻¹ - x * x⁻¹ ^ 3 / 2) := by
            ring
        _ = scale / 2 * (1 - x⁻¹ ^ 2 / 2) := by rw [hxi, e3]
    rw [e] at k
    have ht2 : x⁻¹ ^ 2 ≤ 4 / 9 := by nlinarith
    have k2 : scale / 2 * (7 / 9) ≤ scale / 2 * (1 - x⁻¹ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · have k := mul_le_mul_of_nonneg_left hup hx0.le
    have e : x * (scale / 2 * x⁻¹) = scale / 2 := by
      calc x * (scale / 2 * x⁻¹) = scale / 2 * (x * x⁻¹) := by ring
        _ = scale / 2 := by rw [hxi, mul_one]
    rw [e] at k
    linarith

/-- The rows of `Tacc` by index. -/
theorem rowsA (i : ℕ) (hi : i < 10) : ∀ y ∈ Icc ((loA.getD i 0 : ℚ) : ℝ) (hiA.getD i 0),
    |eval (accZ (taq i) i) (y ^ 2)⁻¹ - y * erfcx y| ≤ (rhoA : ℝ) * (y * erfcx y) := by
  interval_cases i
  exacts [ErfcAsymRowsA0.row0, ErfcAsymRowsA0.row1, ErfcAsymRowsA0.row2, ErfcAsymRowsA0.row3,
    ErfcAsymRowsA0.row4, ErfcAsymRowsA1.row5, ErfcAsymRowsA1.row6, ErfcAsymRowsA1.row7,
    ErfcAsymRowsA1.row8, ErfcAsymRowsA1.row9]

/-- The intervals of `x` of the rows of `Tacc` contain the arguments that select them. -/
def DomA (i : ℕ) : Prop :=
  (i < 9 → loA.getD i 0 * (ratOfWord (thrA.getD i 0) + 1 / 2 ^ 1075) ≤ 1 - 1 / 2 ^ 53 ∧
      0 ≤ ratOfWord (thrA.getD i 0)) ∧
    (0 < i → 1 + 1 / 2 ^ 53 ≤ hiA.getD i 0 * (ratOfWord (thrA.getD (i - 1) 0) - 1 / 2 ^ 1075) ∧
      1 / 2 ^ 1075 < ratOfWord (thrA.getD (i - 1) 0)) ∧
    (i = 9 → loA.getD 9 0 ≤ ratOfWord 0x3FFB59FFB450828C) ∧
    (i = 0 → ratOfWord 0x403B39DC41E48BFD ≤ hiA.getD 0 0)

instance (i : ℕ) : Decidable (DomA i) := by unfold DomA; infer_instance

theorem domA_ok : ∀ i < 10, DomA i := by decide +kernel

/-- Horner's rule from the top of `a 0, ..., a m`. -/
theorem hornerA_sum (a : ℕ → ℝ) (U : ℝ) (m : ℕ) : ∀ n ≤ m,
    hornerA (fun j => a (m - 1 - j)) U (a m) n =
      ∑ k ∈ Finset.range (n + 1), a (m - n + k) * U ^ k
  | 0, _ => by simp [hornerA]
  | n + 1, hn => by
    have ih := hornerA_sum a U m n (by omega)
    rw [hornerA, ih, Finset.sum_range_succ' _ (n + 1), Finset.sum_mul]
    rw [show m - (n + 1) + 0 = m - 1 - n by omega, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show m - (n + 1) + (k + 1) = m - n + k by omega, pow_succ, mul_assoc]

/-- Horner's rule with double-double coefficients from the top. -/
theorem hornerB_sum (b d : ℕ → ℝ) (U W : ℝ) (m : ℕ) : ∀ n ≤ m,
    hornerB (fun j => b (m - 1 - j)) (fun j => d (m - 1 - j)) U W n =
      ∑ k ∈ Finset.range n, (b (m - n + k) + d (m - n + k)) * U ^ k + U ^ n * W
  | 0, _ => by simp [hornerB]
  | n + 1, hn => by
    have ih := hornerB_sum b d U W m n (by omega)
    rw [hornerB, ih, Finset.sum_range_succ', add_mul, Finset.sum_mul]
    rw [show m - (n + 1) + 0 = m - 1 - n by omega, pow_zero, mul_one]
    have hs : ∑ k ∈ Finset.range n, (b (m - n + k) + d (m - n + k)) * U ^ k * U =
        ∑ k ∈ Finset.range n, (b (m - (n + 1) + (k + 1)) + d (m - (n + 1) + (k + 1))) *
          U ^ (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show m - (n + 1) + (k + 1) = m - n + k by omega, pow_succ, mul_assoc]
    rw [hs, pow_succ]
    beta_reduce
    ring

/-- The polynomial of row `i` at `U` from its coefficients. -/
theorem accZ_eval (q : List ℚ) (i : ℕ) (U : ℝ) :
    eval (accZ q i) U = ∑ k ∈ Finset.range 6, ((q.getD (2 * k) 0 : ℝ) + q.getD (2 * k + 1) 0) *
      U ^ k + U ^ 6 * ∑ k ∈ Finset.range (9 + i), (q.getD (12 + k) 0 : ℝ) * U ^ k := by
  rw [accZ, TaylorRemainder.eval_append, TaylorRemainder.eval_map_range,
    TaylorRemainder.eval_map_range, List.length_map, List.length_range]
  push_cast
  ring


theorem hornerA_congr (c c' : ℕ → ℝ) (U V : ℝ) :
    ∀ n, (∀ j < n, c j = c' j) → hornerA c U V n = hornerA c' U V n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [hornerA]
    rw [hornerA_congr c c' U V n (fun j hj => h j (by omega)), h n (by omega)]

theorem hornerB_congr (c c' d d' : ℕ → ℝ) (U V : ℝ) :
    ∀ n, (∀ j < n, c j = c' j ∧ d j = d' j) → hornerB c d U V n = hornerB c' d' U V n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [hornerB]
    rw [hornerB_congr c c' d d' U V n (fun j hj => h j (by omega)), (h n (by omega)).1,
      (h n (by omega)).2]

/-- The value of the two loops for row `i`. -/
theorem loops_val (i : ℕ) (q : ℕ → ℝ) (U : ℝ) :
    hornerB (fun j => q (10 - 2 * j)) (fun j => q (11 - 2 * j)) U
      (hornerA (fun j => q (19 + i - j)) U (q (20 + i)) (8 + i)) 6 =
      ∑ k ∈ Finset.range 6, (q (2 * k) + q (2 * k + 1)) * U ^ k +
        U ^ 6 * ∑ k ∈ Finset.range (9 + i), q (12 + k) * U ^ k := by
  have hS := hornerA_sum (fun k => q (12 + k)) U (8 + i) (8 + i) le_rfl
  beta_reduce at hS
  rw [show 20 + i = 12 + (8 + i) by omega,
    hornerA_congr (fun j => q (19 + i - j)) (fun j => q (12 + (8 + i - 1 - j))) U _ (8 + i)
      (fun j hj => show q (19 + i - j) = q (12 + (8 + i - 1 - j)) by congr 1; omega), hS]
  have hT := hornerB_sum (fun k => q (2 * k)) (fun k => q (2 * k + 1)) U
    (∑ k ∈ Finset.range (8 + i + 1), q (12 + (8 + i - (8 + i) + k)) * U ^ k) 6 6 le_rfl
  beta_reduce at hT
  rw [hornerB_congr (fun j => q (10 - 2 * j)) (fun j => q (2 * (6 - 1 - j)))
      (fun j => q (11 - 2 * j)) (fun j => q (2 * (6 - 1 - j) + 1)) U _ 6
      (fun j hj => ⟨show q (10 - 2 * j) = q (2 * (6 - 1 - j)) by congr 1; omega,
        show q (11 - 2 * j) = q (2 * (6 - 1 - j) + 1) by congr 1; omega⟩), hT]
  simp only [Nat.sub_self, zero_add, show 8 + i + 1 = 9 + i by omega]

theorem zero_ff : ff (0.0 : Float) ∧ fv (0.0 : Float) = 0 := by
  have h : (0.0 : Float).toBits = 0 := rfl
  unfold ff fv
  rw [h]
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  rw [← ratOfWord_cast, show ratOfWord 0 = 0 by decide +kernel]
  norm_num

/-- The pair `U = uh + ul` as a `Pr` with the bound `MU` of a row whose interval starts at `lo`. -/
theorem u_pr {uh ul : Float} (huh : ff uh) (hul : ff ul) (x : ℝ) (lo MU : ℚ) (hx0 : 0 < x)
    (hlo : (lo : ℝ) ≤ x) (hlo0 : 0 ≤ (lo : ℝ)) (hmu : 1 + 1 / 2 ^ 50 ≤ (MU : ℝ) * lo ^ 2)
    (hU : |fv uh + fv ul - (1 / x) ^ 2| ≤ 14 * u * u * (1 / x) ^ 2)
    (hL : |fv ul| ≤ 4 * u * (1 / x) ^ 2) :
    Pr uh ul (fv uh + fv ul) MU (MU / 2 ^ 50 : ℚ) 0 ∧ (1 / x) ^ 2 ≤ MU := by
  have hk : (1 / x) ^ 2 * (lo : ℝ) ^ 2 ≤ 1 := by
    rw [← mul_pow, one_div_mul_eq_div]
    have : (lo : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hlo
    have h0 : (0 : ℝ) ≤ lo / x := div_nonneg hlo0 hx0.le
    calc ((lo : ℝ) / x) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 1 := one_pow 2
  have ht0 : 0 ≤ (1 / x) ^ 2 := by positivity
  have hMU0 : (0 : ℝ) ≤ MU := by
    by_contra hn
    push Not at hn
    have : (MU : ℝ) * lo ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn.le (by positivity)
    linarith [show (0 : ℝ) < 1 + 1 / 2 ^ 50 by positivity]
  have hMUt : (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) ≤ MU := by
    calc (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) ≤ (1 / x) ^ 2 * ((MU : ℝ) * lo ^ 2) :=
          mul_le_mul_of_nonneg_left hmu ht0
      _ = ((1 / x) ^ 2 * (lo : ℝ) ^ 2) * MU := by ring
      _ ≤ 1 * MU := mul_le_mul_of_nonneg_right hk hMU0
      _ = MU := one_mul _
  have hUabs : |fv uh + fv ul| ≤ (MU : ℝ) := by
    have := abs_sub_abs_le_abs_sub (fv uh + fv ul) ((1 / x) ^ 2)
    rw [abs_of_nonneg ht0] at this
    have : 14 * u * u * (1 / x) ^ 2 ≤ (1 / x) ^ 2 * (1 / 2 ^ 50) := by
      rw [mul_comm ((1 / x) ^ 2)]; gcongr; norm_num
    linarith
  have hLabs : |fv ul| ≤ ((MU / 2 ^ 50 : ℚ) : ℝ) := by
    push_cast
    refine hL.trans ?_
    have : 4 * u * (1 / x) ^ 2 ≤ (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) / 2 ^ 50 := by
      have : 4 * u ≤ (1 + 1 / 2 ^ 50) / 2 ^ 50 := by norm_num
      calc 4 * u * (1 / x) ^ 2 ≤ (1 + 1 / 2 ^ 50) / 2 ^ 50 * (1 / x) ^ 2 :=
            mul_le_mul_of_nonneg_right this ht0
        _ = (1 / x) ^ 2 * (1 + 1 / 2 ^ 50) / 2 ^ 50 := by ring
    exact this.trans (div_le_div_of_nonneg_right hMUt (by norm_num))
  refine ⟨⟨huh, hul, by simp, hUabs, hLabs⟩, ?_⟩
  linarith

/-- A row's polynomial at `U` within `2^-60` of `x erfcx x`, from its certificate on the row's
interval and the bound `Lip ≤ 128` on its derivative. -/
theorem zg_bound (P : List ℚ) (lo hi MU Lip : ℚ) (x U : ℝ) (hx : 3 / 2 ≤ x)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi)
    (hrow : ∀ y ∈ Icc (lo : ℝ) hi, |eval P (y ^ 2)⁻¹ - y * erfcx y| ≤ (rhoA : ℝ) * (y * erfcx y))
    (hMU : (1 / x) ^ 2 ≤ MU) (hUM : |U| ≤ MU) (hLip : absSum MU (derivP P) ≤ Lip)
    (hLip2 : (Lip : ℝ) ≤ 128) (hUx : |U - (1 / x) ^ 2| ≤ 14 * u * u * (1 / x) ^ 2) :
    |eval P U - x * erfcx x| ≤ x * erfcx x / 2 ^ 60 := by
  have hx0 : 0 < x := by linarith
  have hr := hrow x ⟨hlo, hhi⟩
  have hxi : (1 / x) ^ 2 = (x ^ 2)⁻¹ := by rw [one_div, inv_pow]
  have ht0 : 0 ≤ (1 / x) ^ 2 := by positivity
  have hMU0 : (0 : ℝ) ≤ MU := ht0.trans hMU
  have hxa : |(x ^ 2)⁻¹| ≤ (MU : ℝ) := by rw [← hxi, abs_of_nonneg ht0]; exact hMU
  have hzl := z_lip P MU Lip (by qc hMU0) hLip hUM hxa
  rw [← hxi] at hzl hr
  have hG := G_bounds2 x hx
  have hρ : (rhoA : ℝ) = 1 / 2 ^ 61 := by unfold rhoA; norm_num
  rw [hρ] at hr
  have ht4 : (1 / x) ^ 2 ≤ 4 / 9 := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have k1 : (Lip : ℝ) * |U - (1 / x) ^ 2| ≤ 128 * (14 * u * u * (4 / 9)) := by
    have : |U - (1 / x) ^ 2| ≤ 14 * u * u * (4 / 9) := by
      refine hUx.trans ?_
      have : (0 : ℝ) ≤ 14 * u * u := by norm_num
      nlinarith
    exact mul_le_mul hLip2 this (abs_nonneg _) (by norm_num)
  have t := abs_sub_le (eval P U) (eval P ((1 / x) ^ 2)) (x * erfcx x)
  have : 128 * (14 * u * u * (4 / 9)) ≤ x * erfcx x / 2 ^ 61 := by
    have : 128 * (14 * u * u * (4 / 9) : ℝ) ≤ 43 / 100 / 2 ^ 61 := by norm_num
    linarith [hG.1]
  linarith

set_option maxHeartbeats 8000000 in
/-- `erfc_asympt_accurate` before the scaling: `(h + l) 2^K` within `2^-56 erfc x`. -/
theorem aa_hl (hF : FmaNearest) (x : Float) (hx : ff x)
    (hlo : (ratOfWord 0x3FFB59FFB450828C : ℝ) < fv x)
    (hhi : fv x < ratOfWord 0x403B39DC41E48BFD) :
    ∃ K : ℤ, -1072 ≤ K ∧ K ≤ -2 ∧
      ff (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.2 ∧
      fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.2 = K ∧
      ff (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 ∧
      ff (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1 ∧
      |(fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 +
        fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1) * (2 : ℝ) ^ K -
          erfc (fv x)| ≤ erfc (fv x) / 2 ^ 56 ∧
      |fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1| ≤
        |fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1| / 2 ^ 40 ∧
      1 / 200 ≤ fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 ∧
      fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 ≤ 8 := by
  -- the range of `x`
  have k1 : (17 / 10 : ℚ) ≤ ratOfWord 0x3FFB59FFB450828C := by decide +kernel
  have k2 : ratOfWord 0x403B39DC41E48BFD ≤ (2723 / 100 : ℚ) := by decide +kernel
  have q1 : (17 / 10 : ℝ) < fv x := lt_of_le_of_lt (by qc k1) hlo
  have q2 : fv x < 2723 / 100 := lt_of_lt_of_le hhi (by qc k2)
  have hX0 : 0 < fv x := by linarith
  have hXX : 0 < fv x * fv x := mul_pos hX0 hX0
  have hXX1 : 289 / 100 ≤ fv x * fv x := by nlinarith
  have hXX2 : fv x * fv x ≤ 7415 / 10 := by nlinarith
  -- `x²`
  obtain ⟨a1, a2, ae1, ae2⟩ := aMul_f hF x x hx hx
    (by rw [abs_of_pos hXX]; linarith [show (7415 / 10 : ℝ) ≤ 2 ^ 1020 by norm_num])
  rw [abs_of_pos hXX] at ae1 ae2
  have hu0 : 2 ≤ fv (Erfc.aMul x x).1 ∧ fv (Erfc.aMul x x).1 ≤ 742 := by
    have h1 := (abs_le.mp ae1).1
    have h2 := (abs_le.mp ae1).2
    have : u * (fv x * fv x) ≤ u * (7415 / 10) := by gcongr
    have : u * (7415 / 10) + η ≤ 1 / 10 := by norm_num
    constructor <;> linarith
  have hul0 : |fv (Erfc.aMul x x).2| ≤ 1 / 2 ^ 41 := by
    have e : fv (Erfc.aMul x x).2 = (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2 - fv x * fv x) -
        (fv (Erfc.aMul x x).1 - fv x * fv x) := by ring
    rw [e]
    refine (abs_sub_le' _ _).trans ?_
    have : u * (fv x * fv x) ≤ u * (7415 / 10) := by gcongr
    have : u * u * (fv x * fv x) ≤ u * u * (7415 / 10) := by gcongr
    have : u * u * (7415 / 10) + 2 * η + (u * (7415 / 10) + η) ≤ 1 / 2 ^ 41 := by norm_num
    linarith
  have hδ : |fv x * fv x - (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2)| ≤ 1 / 2 ^ 95 := by
    rw [abs_sub_comm]
    refine ae2.trans ?_
    have : u * u * (fv x * fv x) ≤ u * u * (7415 / 10) := by gcongr
    have : u * u * (7415 / 10) + 2 * η ≤ 1 / 2 ^ 95 := by norm_num
    linarith
  -- `exp (-x²)` by `exp_accurate`
  obtain ⟨n1f, n1v⟩ := neg_f _ a1
  obtain ⟨n2f, n2v⟩ := neg_f _ a2
  obtain ⟨K, hK1, hK2, kf, kv, ef1, ef2, eerr, elb, hE1, hE2⟩ := expAcc_err hF _ _ n1f n2f
    (by rw [n1v]; linarith [hu0.2]) (by rw [n1v]; linarith [hu0.1])
    (by rw [n2v, abs_neg]; exact hul0.trans (by norm_num))
  rw [n1v, n2v] at eerr hE1 hE2
  set EK := Real.exp (-fv (Erfc.aMul x x).1 + -fv (Erfc.aMul x x).2 - K * Real.log 2) with hEK
  have hEK0 : 0 < EK := Real.exp_pos _
  have pE : Pr (eA Erfc.expAccTable x).1 (eA Erfc.expAccTable x).2.1 EK EK (1 / 2 ^ 47 * EK)
      (1 / 2 ^ 76 * EK) :=
    ⟨ef1, ef2, eerr, le_of_eq (abs_of_pos hEK0), elb.trans (by nlinarith)⟩
  -- `1/x` and `1/x²`
  obtain ⟨df, lf, hY, hyl, hy⟩ := recip_pr hF x hx (by linarith) (by linarith)
  obtain ⟨uf, ulf, hU, hUL⟩ := usq_pr hF x hx (by linarith) (by linarith)
  have pY : Pr (1.0 / x) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (1 / fv x) (1 / fv x)
      (11 / 10 * u * (1 / fv x)) (4 * u * u * (1 / fv x)) :=
    ⟨df, lf, hY.trans (le_of_eq (by ring)), le_of_eq (abs_of_pos (one_div_pos.mpr hX0)),
      hyl.trans (le_of_eq (by ring))⟩
  -- the row
  obtain ⟨i, hi10, hidx, hle, hgt⟩ := acc_index (1.0 / x) df
  obtain ⟨d1, d2, d3, d4⟩ := domA_ok i hi10
  have hxlo : ((loA.getD i 0 : ℚ) : ℝ) ≤ fv x := by
    rcases (show i < 9 ∨ i = 9 by omega) with h9 | h9
    · obtain ⟨c1, c2⟩ := d1 h9
      exact dom_lo hX0 hy _ _ (hle h9) c1 c2
    · have := d3 h9
      subst h9
      have : ((loA.getD 9 0 : ℚ) : ℝ) ≤ ratOfWord 0x3FFB59FFB450828C := by qc this
      linarith
  have hxhi : fv x ≤ ((hiA.getD i 0 : ℚ) : ℝ) := by
    rcases (show i = 0 ∨ 0 < i by omega) with h0 | h0
    · have := d4 h0
      subst h0
      have : (ratOfWord 0x403B39DC41E48BFD : ℝ) ≤ ((hiA.getD 0 0 : ℚ) : ℝ) := by
        qc this
      linarith
    · obtain ⟨c1, c2⟩ := d2 h0
      exact dom_hi hX0 hy _ _ (hgt h0) c1 c2
  obtain ⟨hcA, htopf, htopv, htopm, hb0L, hb0e, hcB, hchkA, hbB0, hchkB, hcnt, hmu, hlo1, hlip,
    hlipb, hfe, hfL, hfM1, hfM2⟩ := tRow_ok i hi10
  set MU := muA.getD i 0 with hMUdef
  have qlo1 : (1 : ℝ) ≤ ((loA.getD i 0 : ℚ) : ℝ) := by qc hlo1
  have qmu : 1 + 1 / 2 ^ 50 ≤ (MU : ℝ) * ((loA.getD i 0 : ℚ) : ℝ) ^ 2 := by qc hmu
  obtain ⟨pU, hMUx⟩ := u_pr uf ulf (fv x) (loA.getD i 0) MU hX0 hxlo (by linarith) qmu hU hUL
  -- the first loop
  set q : ℕ → ℝ := fun k => (((taq i).getD k 0 : ℚ) : ℝ) with hq
  have hcsA : ∀ j < 8 + i, ff (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 19 +
      UInt64.ofNat i - UInt64.ofNat j)) ∧ |fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i +
        19 + UInt64.ofNat i - UInt64.ofNat j))| ≤ (((mcAL.getD i []).getD j 0 : ℚ) : ℝ) ∧
      fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 19 + UInt64.ofNat i -
        UInt64.ofNat j)) = q (19 + i - j) := by
    intro j hj
    obtain ⟨c1, c2, c3⟩ := hcA j hj
    obtain ⟨ef, ev⟩ := ent_of_q _ _ _ ⟨c1, c2⟩
    refine ⟨ef, ?_, ev⟩
    rw [ev, ← qabs_cast]
    qc c3
  obtain ⟨tf, tv⟩ := ent_of_q Erfc.asymAccTable (30 * UInt64.ofNat i + 20 + UInt64.ofNat i) _
    ⟨htopf, htopv⟩
  obtain ⟨zf, zv⟩ := zero_ff
  have h0A : Pr (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 20 + UInt64.ofNat i),
      (0.0 : Float)).1 (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 20 + UInt64.ofNat i),
      (0.0 : Float)).2 (q (20 + i)) ((bsAL.getD i []).getD 0 0).1 ((bsAL.getD i []).getD 0 0).2.1
      ((bsAL.getD i []).getD 0 0).2.2 := by
    refine ⟨tf, zf, ?_, ?_, ?_⟩
    · show |fv _ + fv (0.0 : Float) - q (20 + i)| ≤ _
      rw [zv, tv, hb0e]; simp [hq]
    · show |q (20 + i)| ≤ _
      rw [hq]; simp only []; rw [← qabs_cast]; qc htopm
    · show |fv (0.0 : Float)| ≤ _
      rw [zv, hb0L]; simp
  have lA := loopA hF pU (fun j => Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 19 +
      UInt64.ofNat i - UInt64.ofNat j)) (mcAL.getD i []) (bsAL.getD i []) _ (q (20 + i)) h0A
    (8 + i) (fun j hj => ⟨(hcsA j hj).1, (hcsA j hj).2.1⟩) hchkA
  -- the second loop
  have hcsB : ∀ j < 6, ff (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 -
      2 * UInt64.ofNat j)) ∧ |fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 -
        2 * UInt64.ofNat j))| ≤ (((mcBL.getD i []).getD j 0 : ℚ) : ℝ) ∧
      ff (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 - 2 * UInt64.ofNat j)) ∧
      |fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 - 2 * UInt64.ofNat j))| ≤
        (((mdBL.getD i []).getD j 0 : ℚ) : ℝ) ∧
      fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 - 2 * UInt64.ofNat j)) =
        q (10 - 2 * j) ∧
      fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 - 2 * UInt64.ofNat j)) =
        q (11 - 2 * j) := by
    intro j hj
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcB j hj
    obtain ⟨ef, ev⟩ := ent_of_q _ _ _ ⟨c1, c2⟩
    obtain ⟨ef', ev'⟩ := ent_of_q _ _ _ ⟨c4, c5⟩
    refine ⟨ef, ?_, ef', ?_, ev, ev'⟩
    · rw [ev, ← qabs_cast]; qc c3
    · rw [ev', ← qabs_cast]; qc c6
  rw [← hbB0] at lA
  have lB := loopB hF pU (fun j => Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 -
      2 * UInt64.ofNat j)) (fun j => Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 -
      2 * UInt64.ofNat j)) (mcBL.getD i []) (mdBL.getD i []) (bsBL.getD i []) _ _ lA 6
    (fun j hj => ⟨(hcsB j hj).1, (hcsB j hj).2.1, (hcsB j hj).2.2.1, (hcsB j hj).2.2.2.1⟩)
    hchkB
  -- the loops as `zA`, and their value
  have hzA : zA Erfc.asymAccTable 1.0 2.0 x = Nat.fold 6 (fun j _ s => tStepB
      (Erfc.aMul (1.0 / x) (1.0 / x)).1 (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) *
        Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (Erfc.aMul (1.0 / x) (1.0 / x)).2)
      (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 - 2 * UInt64.ofNat j))
      (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 - 2 * UInt64.ofNat j)) s)
      (Nat.fold (8 + i) (fun j _ s => tStep (Erfc.aMul (1.0 / x) (1.0 / x)).1
        (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)
          (Erfc.aMul (1.0 / x) (1.0 / x)).2)
        (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 19 + UInt64.ofNat i -
          UInt64.ofNat j)) s)
        (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 20 + UInt64.ofNat i),
          (0.0 : Float))) := by
    unfold zA uPair
    rw [hidx]
    simp only [LeanExe.loop, UInt64.reduceToNat]
    rw [hcnt]
  have hval : hornerB (fun j => fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 10 -
      2 * UInt64.ofNat j))) (fun j => fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 11 -
      2 * UInt64.ofNat j))) (fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x))
      ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (Erfc.aMul (1.0 / x) (1.0 / x)).2))
      (hornerA (fun j => fv (Erfc.entry Erfc.asymAccTable (30 * UInt64.ofNat i + 19 +
        UInt64.ofNat i - UInt64.ofNat j))) (fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 +
        fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)
          (Erfc.aMul (1.0 / x) (1.0 / x)).2)) (q (20 + i)) (8 + i)) 6 =
      eval (accZ (taq i) i) (fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x))
        ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (Erfc.aMul (1.0 / x) (1.0 / x)).2)) := by
    rw [hornerA_congr _ (fun j => q (19 + i - j)) _ _ (8 + i) (fun j hj => (hcsA j hj).2.2),
      hornerB_congr _ (fun j => q (10 - 2 * j)) _ (fun j => q (11 - 2 * j)) _ _ 6
        (fun j hj => ⟨(hcsB j hj).2.2.2.2.1, (hcsB j hj).2.2.2.2.2⟩),
      loops_val, accZ_eval]
  rw [hval, ← hzA] at lB
  set U := fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x))
    ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (Erfc.aMul (1.0 / x) (1.0 / x)).2) with hUdef
  set Z := eval (accZ (taq i) i) U with hZdef
  -- the polynomial against `x erfcx x`
  have hG := G_bounds2 (fv x) (by linarith)
  have hZG := zg_bound (accZ (taq i) i) (loA.getD i 0) (hiA.getD i 0) MU (lipA.getD i 0) (fv x) U
    (by linarith) hxlo hxhi (rowsA i hi10) hMUx pU.2.2.2.1 hlip (by qc hlipb) hU
  set G := fv x * erfcx (fv x) with hGdef
  -- the bounds of the polynomial's double-double
  set B := (bsBL.getD i []).getD 6 0 with hBdef
  have qfM1 : (1 / 2 : ℝ) ≤ B.1 := by qc hfM1
  have qfM2 : (B.1 : ℝ) ≤ 4 := by qc hfM2
  have qfe : (B.2.2 : ℝ) ≤ 1 / 2 ^ 90 * B.1 := by
    have : (B.2.2 : ℝ) ≤ B.1 / 2 ^ 90 := by qc hfe
    linarith
  have qfL : (B.2.1 : ℝ) ≤ 1 / 2 ^ 44 * B.1 := by
    have : (B.2.1 : ℝ) ≤ B.1 / 2 ^ 44 := by qc hfL
    linarith
  -- the product with `1/x`
  have hxi1 : 1 / fv x ≤ 1 := by rw [div_le_one hX0]; linarith
  have hxi0 : 0 < 1 / fv x := one_div_pos.mpr hX0
  have p1 := pr_dMul_rel hF lB pY (1 / 2 ^ 90) (1 / 2 ^ 44) (4 * u * u) (11 / 10 * u) qfe qfL
    (le_of_eq (by ring)) (le_of_eq (by ring)) (by norm_num) (by norm_num)
    (by
      have : 1 / 2 * (1 / (2723 / 100)) ≤ (B.1 : ℝ) * (1 / fv x) :=
        mul_le_mul qfM1 (one_div_le_one_div_of_le hX0 q2.le) (by norm_num) (by linarith)
      linarith [show (1 : ℝ) / 2 ^ 980 ≤ 1 / 2 * (1 / (2723 / 100)) by norm_num])
    (by linarith) (by linarith)
  -- the renormalization
  have hV1 : (2 / 5 : ℝ) * (1 / fv x) ≤ |Z * (1 / fv x)| := by
    rw [abs_mul, abs_of_pos hxi0]
    have : (2 / 5 : ℝ) ≤ |Z| := by
      have := abs_sub_abs_le_abs_sub G Z
      rw [abs_sub_comm] at this
      rw [abs_of_pos (by linarith [hG.1] : (0 : ℝ) < G)] at this
      have : G / 2 ^ 60 ≤ 1 / 2 ^ 60 := by linarith [hG.2]
      linarith [hG.1]
    exact mul_le_mul_of_nonneg_right this hxi0.le
  have hh1 := p1.h_ge
  have hl1 := p1.2.2.2.2
  have hBx : (B.1 : ℝ) * (1 / fv x) ≤ 4 * (1 / fv x) := mul_le_mul_of_nonneg_right qfM2 hxi0.le
  have hBx0 : 0 ≤ (B.1 : ℝ) * (1 / fv x) := by nlinarith
  have hlh : |fv (Erfc.dMul (zA Erfc.asymAccTable 1.0 2.0 x).1 (zA Erfc.asymAccTable 1.0 2.0 x).2
      (1.0 / x) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)).2| ≤
      |fv (Erfc.dMul (zA Erfc.asymAccTable 1.0 2.0 x).1 (zA Erfc.asymAccTable 1.0 2.0 x).2
        (1.0 / x) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)).1| := by
    have c1 : ((1 + 1 / 2 ^ 18) * (1 / 2 ^ 44 + 11 / 10 * u) + 2 * u) * 4 ≤ 1 / 10 := by norm_num
    have c2 : (1 / 2 ^ 90 + 4 * u * u + 1 / 2 ^ 90 * (4 * u * u) + 1 / 2 ^ 44 * (11 / 10 * u) +
        3 * u * (1 / 2 ^ 44 + 11 / 10 * u) + 4 * u * u + 1 / 2 ^ 92) * 4 ≤ 1 / 10 := by norm_num
    nlinarith
  have p1' := pr_renorm p1 hlh _ le_rfl (by
    have c3 : (1 + (1 / 2 ^ 90 + 4 * u * u + 1 / 2 ^ 90 * (4 * u * u) + 1 / 2 ^ 44 * (11 / 10 * u) +
        3 * u * (1 / 2 ^ 44 + 11 / 10 * u) + 4 * u * u + 1 / 2 ^ 92) +
        2 * ((1 + 1 / 2 ^ 18) * (1 / 2 ^ 44 + 11 / 10 * u) + 2 * u)) * 4 ≤ 2 ^ 999 := by norm_num
    nlinarith)
  -- the product with `exp (-x²) 2^-K`
  have hM1lo : 1 / 2 * (1 / (2723 / 100)) ≤ (B.1 : ℝ) * (1 / fv x) :=
    mul_le_mul qfM1 (one_div_le_one_div_of_le hX0 q2.le) (by norm_num) (by linarith)
  have p2 := pr_dMul_rel hF p1' pE _ (u * (1 + (1 / 2 ^ 90 + 4 * u * u + 1 / 2 ^ 90 * (4 * u * u) + 1 / 2 ^ 44 * (11 / 10 * u) + 3 * u * (1 / 2 ^ 44 + 11 / 10 * u) + 4 * u * u + 1 / 2 ^ 92) + 2 * ((1 + 1 / 2 ^ 18) * (1 / 2 ^ 44 + 11 / 10 * u) + 2 * u))) (1 / 2 ^ 76) (1 / 2 ^ 47) le_rfl
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring)) (by norm_num) (by norm_num)
    (by
      have h2 : 1 / 2 * (1 / (2723 / 100)) * (3 / 5) ≤ (B.1 : ℝ) * (1 / fv x) * EK :=
        mul_le_mul hM1lo hE1 (by norm_num) hBx0
      linarith [show (1 : ℝ) / 2 ^ 980 ≤ 1 / 2 * (1 / (2723 / 100)) * (3 / 5) by norm_num])
    (by linarith) (by linarith)
  have p2' : Pr (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1
      (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1 _ _ _ _ := p2
  have hh2 := Pr.h_le p2'
  have hh2' := Pr.h_ge p2'
  have hl2 := p2'.2.2.2.2
  have herr := p2'.2.2.1
  have hf1 := p2'.1
  have hf2 := p2'.2.1
  -- `erfc x` from `x erfcx x`
  have hG1 : 43 / 100 ≤ G := hG.1
  have hG2 : G ≤ 57 / 100 := hG.2
  have hXne : fv x ≠ 0 := hX0.ne'
  set E0 := Real.exp (-(fv x) ^ 2) with hE0
  have hE00 : 0 < E0 := Real.exp_pos _
  have herfc : erfc (fv x) = E0 / fv x * G := by
    rw [erfc_eq, hGdef, hE0]
    field_simp
  set δ := fv x * fv x - (fv (Erfc.aMul x x).1 + fv (Erfc.aMul x x).2) with hδdef
  have h2K : (2 : ℝ) ^ K = Real.exp (K * Real.log 2) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hEK2 : EK * (2 : ℝ) ^ K = E0 * Real.exp δ := by
    rw [h2K, hEK, hE0, hδdef, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hδ1 : |Real.exp δ - 1| ≤ 1 / 2 ^ 94 := by
    have := Real.abs_exp_sub_one_le (hδ.trans (by norm_num))
    linarith
  have hed : Real.exp δ ≤ 1 + 1 / 2 ^ 94 := by linarith [(abs_le.mp hδ1).2]
  have hed0 : 0 < Real.exp δ := Real.exp_pos _
  set w := E0 / fv x with hw
  have hw0 : 0 < w := div_pos hE00 hX0
  have h2K0 : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hZG' : |Z * Real.exp δ - G| ≤ G / 2 ^ 60 * (1 + 1 / 2 ^ 94) + G * (1 / 2 ^ 94) := by
    have e : Z * Real.exp δ - G = (Z - G) * Real.exp δ + G * (Real.exp δ - 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hed0, abs_of_pos (by linarith : (0 : ℝ) < G)]
    have t1 : |Z - G| * Real.exp δ ≤ G / 2 ^ 60 * (1 + 1 / 2 ^ 94) :=
      mul_le_mul hZG hed hed0.le (by linarith)
    have t2 : G * |Real.exp δ - 1| ≤ G * (1 / 2 ^ 94) :=
      mul_le_mul_of_nonneg_left hδ1 (by linarith)
    linarith
  have hZpos : 2 / 5 ≤ Z ∧ Z ≤ 3 / 5 := by
    have := abs_le.mp hZG
    constructor <;> nlinarith [this.1, this.2]
  have hMEK : (B.1 : ℝ) * (1 / fv x) * EK * (2 : ℝ) ^ K = B.1 * w * Real.exp δ := by
    rw [mul_assoc, hEK2, hw]; field_simp
  have hV2 : Z * (1 / fv x) * EK * (2 : ℝ) ^ K = Z * w * Real.exp δ := by
    rw [mul_assoc, hEK2, hw]; field_simp
  refine ⟨K, hK1, hK2, kf, kv, hf1, hf2, ?_, ?_, ?_, ?_⟩
  · -- the error of `(h + l) 2^K`
    rw [herfc]
    have t0 : |(fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 +
        fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1) * (2 : ℝ) ^ K -
          Z * (1 / fv x) * EK * (2 : ℝ) ^ K| ≤
        |fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 +
          fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1 - Z * (1 / fv x) * EK| *
          (2 : ℝ) ^ K := by
      rw [← sub_mul, abs_mul, abs_of_pos h2K0]
    replace t0 := t0.trans (mul_le_mul_of_nonneg_right herr h2K0.le)
    rw [hV2] at t0
    rw [mul_assoc _ _ ((2 : ℝ) ^ K), hMEK] at t0
    have t := abs_sub_le ((fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).1 +
        fv (aaHL Erfc.expAccTable Erfc.asymAccTable 1.0 2.0 x).2.1) * (2 : ℝ) ^ K)
      (Z * w * Real.exp δ) (w * G)
    have t2 : |Z * w * Real.exp δ - w * G| = w * |Z * Real.exp δ - G| := by
      rw [show Z * w * Real.exp δ - w * G = w * (Z * Real.exp δ - G) by ring, abs_mul,
        abs_of_pos hw0]
    have t4 : w * |Z * Real.exp δ - G| ≤ w * (G / 2 ^ 60 * (1 + 1 / 2 ^ 94) + G * (1 / 2 ^ 94)) :=
      mul_le_mul_of_nonneg_left hZG' hw0.le
    have hw43 : w * (43 / 100) ≤ w * G := mul_le_mul_of_nonneg_left hG1 hw0.le
    have hBe : (B.1 : ℝ) * Real.exp δ ≤ 4 * (1 + 1 / 2 ^ 94) :=
      mul_le_mul qfM2 hed hed0.le (by norm_num)
    have hwBe : w * ((B.1 : ℝ) * Real.exp δ) ≤ w * (4 * (1 + 1 / 2 ^ 94)) :=
      mul_le_mul_of_nonneg_left hBe hw0.le
    have hwG0 : 0 ≤ w * G := mul_nonneg hw0.le (by linarith)
    linarith
  · -- the low part against the high part
    have hV2abs : 2 / 5 * (1 / fv x) * EK ≤ |Z * (1 / fv x) * EK| := by
      rw [abs_mul, abs_mul, abs_of_pos hxi0, abs_of_pos hEK0, abs_of_pos (by linarith : (0 : ℝ) < Z)]
      have := mul_le_mul_of_nonneg_right hZpos.1 hxi0.le
      exact mul_le_mul_of_nonneg_right this hEK0.le
    have hB4 : (B.1 : ℝ) * (1 / fv x) * EK ≤ 4 * (1 / fv x) * EK :=
      mul_le_mul_of_nonneg_right hBx hEK0.le
    have hpos : 0 ≤ (1 / fv x) * EK := mul_nonneg hxi0.le hEK0.le
    have hBpos : 0 ≤ (B.1 : ℝ) * (1 / fv x) * EK := mul_nonneg hBx0 hEK0.le
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · -- the high part from below
    have hpos : 0 ≤ (1 / fv x) * EK := mul_nonneg hxi0.le hEK0.le
    have hB4 : (B.1 : ℝ) * (1 / fv x) * EK ≤ 4 * (1 / fv x) * EK :=
      mul_le_mul_of_nonneg_right hBx hEK0.le
    have hBpos : 0 ≤ (B.1 : ℝ) * (1 / fv x) * EK := mul_nonneg hBx0 hEK0.le
    have hxEK : (1 / (2723 / 100)) * (3 / 5) ≤ (1 / fv x) * EK :=
      mul_le_mul (one_div_le_one_div_of_le hX0 q2.le) hE1 (by norm_num) hxi0.le
    have hV : Z * (1 / fv x) * EK = Z * ((1 / fv x) * EK) := by ring
    have hle := (abs_le.mp herr).1
    have hlb := (abs_le.mp hl2).2
    nlinarith
  · -- the high part from above
    have hpos : 0 ≤ (1 / fv x) * EK := mul_nonneg hxi0.le hEK0.le
    have hxEK : (1 / fv x) * EK ≤ 1 * (8 / 5) := mul_le_mul hxi1 hE2 hEK0.le (by norm_num)
    have hB4 : (B.1 : ℝ) * (1 / fv x) * EK ≤ 4 * (1 / fv x) * EK :=
      mul_le_mul_of_nonneg_right hBx hEK0.le
    have hBpos : 0 ≤ (B.1 : ℝ) * (1 / fv x) * EK := mul_nonneg hBx0 hEK0.le
    have hle := (abs_le.mp herr).2
    have hlb := (abs_le.mp hl2).1
    nlinarith

#print axioms asymAcc_eq
#print axioms G_bounds2
#print axioms hornerA_sum
#print axioms hornerB_sum
#print axioms accZ_eval
#print axioms loops_val
#print axioms aa_hl

end Library.Numerics.Float64.Erfc.ErfcAsymAccHL
