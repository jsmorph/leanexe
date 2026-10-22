import Library.Numerics.Float64.Erf.ErfTailKernel
import Library.Numerics.Float64.Erf.ErfTailSplit
import Library.Numerics.Float64.Exp.ExpTightFloat

/-!
The rounding error of `s_erf.c`'s tail, `erfc x = exp (-z² - 0.5625) exp ((z - x)(z + x) + R/S)/x`
for `x` from 1.25 to 28.  `tail_s` bounds the computed `s = 1/(x x)`.  For an interval `[xlo, xhi]`
of `x` with the range `[slo, shi]` of `s`, `tail_arg2` bounds the computed argument of the second
exponential against `(z - x)(z + x) + R/S (1/x²)` by `tailDelta`, from `F64Horner.hornerW_approx`,
`F64DivApprox.div_approx`, the change of `R/S` between `s` and `1/x²`, and the exact split of
`ErfTailSplit`.  `tail_compose` combines both exponentials' relative errors, the product, and the
quotient by `x` with `x erfc x = exp (-z² - 9/16) exp ((z - x)(z + x) + R/S - tailF)`, which
follows from the definition of `tailF`, into the relative error `tailEps k d` of the quotient.
-/

namespace Library.Numerics.Float64.Erf.ErfTailEval
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks PolyCalculus F64ErrorTrack F64Horner
  RealErf ErfTailBase ErfTailCoeffs ErfTailSplit ErfSmallBase

set_option exponentiation.threshold 4096

/-- The words of `ra0, ..., ra7`. -/
def raW : List UInt64 :=
  [0xBF843412600D6435, 0xBFE63416E4BA7360, 0xC0251E0441B0E726, 0xC04F300AE4CBA38D,
    0xC0644CB184282266, 0xC067135CEBCCABB2, 0xC054526557E4D2F2, 0xC023A0EFC69AC25C]

/-- The words of `1, sa1, ..., sa8`. -/
def saW : List UInt64 :=
  [0x3FF0000000000000, 0x4033A6B9BD707687, 0x4061350C526AE721, 0x407B290DD58A1A71,
    0x40842B1921EC2868, 0x407AD02157700314, 0x405B28A3EE48AE2C, 0x401A47EF8E484A93,
    0xBFAEEFF2EE749A62]

/-- The words of `rb0, ..., rb6`. -/
def rbW : List UInt64 :=
  [0xBF84341239E86F4A, 0xBFE993BA70C285DE, 0xC031C209555F995A, 0xC064145D43C5ED98,
    0xC083EC881375F228, 0xC09004616A2E5992, 0xC07E384E9BDC383F]

/-- The words of `1, sb1, ..., sb7`. -/
def sbW : List UInt64 :=
  [0x3FF0000000000000, 0x403E568B261D5190, 0x40745CAE221B9F0A, 0x409802EB189D5118,
    0x40A8FFB7688C246A, 0x40A3F219CEDF3BE6, 0x407DA874E79FE763, 0xC03670E242712D62]

theorem erfTail_bits (s : Float) (near : Bool) :
    (Erf.erfTail s near).1.toBits = hornerW (if near then raW else rbW) s.toBits ∧
      (Erf.erfTail s near).2.toBits = hornerW (if near then saW else sbW) s.toBits := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have a0 : Wasm.IEEE64.isNaN 0xBF843412600D6435 = false := by decide
  have a1 : Wasm.IEEE64.isNaN 0xBFE63416E4BA7360 = false := by decide
  have a2 : Wasm.IEEE64.isNaN 0xC0251E0441B0E726 = false := by decide
  have a3 : Wasm.IEEE64.isNaN 0xC04F300AE4CBA38D = false := by decide
  have a4 : Wasm.IEEE64.isNaN 0xC0644CB184282266 = false := by decide
  have a5 : Wasm.IEEE64.isNaN 0xC067135CEBCCABB2 = false := by decide
  have a6 : Wasm.IEEE64.isNaN 0xC054526557E4D2F2 = false := by decide
  have a7 : Wasm.IEEE64.isNaN 0xC023A0EFC69AC25C = false := by decide
  have b1 : Wasm.IEEE64.isNaN 0x4033A6B9BD707687 = false := by decide
  have b2 : Wasm.IEEE64.isNaN 0x4061350C526AE721 = false := by decide
  have b3 : Wasm.IEEE64.isNaN 0x407B290DD58A1A71 = false := by decide
  have b4 : Wasm.IEEE64.isNaN 0x40842B1921EC2868 = false := by decide
  have b5 : Wasm.IEEE64.isNaN 0x407AD02157700314 = false := by decide
  have b6 : Wasm.IEEE64.isNaN 0x405B28A3EE48AE2C = false := by decide
  have b7 : Wasm.IEEE64.isNaN 0x401A47EF8E484A93 = false := by decide
  have b8 : Wasm.IEEE64.isNaN 0xBFAEEFF2EE749A62 = false := by decide
  have c0 : Wasm.IEEE64.isNaN 0xBF84341239E86F4A = false := by decide
  have c1 : Wasm.IEEE64.isNaN 0xBFE993BA70C285DE = false := by decide
  have c2 : Wasm.IEEE64.isNaN 0xC031C209555F995A = false := by decide
  have c3 : Wasm.IEEE64.isNaN 0xC064145D43C5ED98 = false := by decide
  have c4 : Wasm.IEEE64.isNaN 0xC083EC881375F228 = false := by decide
  have c5 : Wasm.IEEE64.isNaN 0xC09004616A2E5992 = false := by decide
  have c6 : Wasm.IEEE64.isNaN 0xC07E384E9BDC383F = false := by decide
  have d1 : Wasm.IEEE64.isNaN 0x403E568B261D5190 = false := by decide
  have d2 : Wasm.IEEE64.isNaN 0x40745CAE221B9F0A = false := by decide
  have d3 : Wasm.IEEE64.isNaN 0x409802EB189D5118 = false := by decide
  have d4 : Wasm.IEEE64.isNaN 0x40A8FFB7688C246A = false := by decide
  have d5 : Wasm.IEEE64.isNaN 0x40A3F219CEDF3BE6 = false := by decide
  have d6 : Wasm.IEEE64.isNaN 0x407DA874E79FE763 = false := by decide
  have d7 : Wasm.IEEE64.isNaN 0xC03670E242712D62 = false := by decide
  cases near <;> constructor <;>
  simp only [Erf.erfTail, raW, saW, rbW, sbW, hornerW, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, hone, a0, a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7, b8,
    c0, c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, d7, Bool.false_eq_true, ↓reduceIte]

theorem ra_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    raW tailRA := by
  simp only [raW, tailRA, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast]
  unfold CodeLib.IEEE64.Finite
  decide

theorem sa_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    saW tailSA := by
  simp only [saW, tailSA, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast,
    Rat.cast_one, one_value]
  unfold CodeLib.IEEE64.Finite
  decide

theorem rb_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    rbW tailRB := by
  simp only [rbW, tailRB, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast]
  unfold CodeLib.IEEE64.Finite
  decide

theorem sb_rel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ))
    sbW tailSB := by
  simp only [sbW, tailSB, List.forall₂_cons, List.Forall₂.nil, and_true, ratOfWord_cast,
    Rat.cast_one, one_value]
  unfold CodeLib.IEEE64.Finite
  decide

/-- The bound on `|s - 1/x²|` for `x ≥ xlo ≥ 1`. -/
def tailSErr (xlo : ℚ) : ℚ :=
  uQ / (xlo ^ 2 * (1 - uQ) - etaQ) + etaQ + (uQ + etaQ / xlo ^ 2) / (xlo ^ 2 * (1 - uQ) - etaQ)

theorem one_finite : Finite (0x3FF0000000000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

/-- The computed `s = 1/(x x)` for `x` in `[xlo, xhi]`, `1 ≤ xlo`, `xhi < 32`. -/
theorem tail_s (xlo xhi : ℚ) (h1 : 1 ≤ xlo) (h32 : xhi < 32) (X : UInt64) (hX : Finite X)
    (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi) :
    Finite (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)) ∧
      (((1 - uQ) / (xhi ^ 2 * (1 + uQ) + etaQ) - etaQ : ℚ) : ℝ) ≤
        value (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)) ∧
      value (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)) ≤
        (((1 + uQ) / (xlo ^ 2 * (1 - uQ) - etaQ) + etaQ : ℚ) : ℝ) ∧
      |value (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)) - (value X ^ 2)⁻¹| ≤
        tailSErr xlo := by
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  have hu0 : (uQ : ℝ) = 1 / 2 ^ 53 := by simp [uQ]
  have he0 : (etaQ : ℝ) = 1 / 2 ^ 1075 := by simp [etaQ]
  set x := value X with hxdef
  have h1' : (1 : ℝ) ≤ xlo := by exact_mod_cast h1
  have h32' : (xhi : ℝ) < 32 := by exact_mod_cast h32
  have hx1 : 1 ≤ x := h1'.trans hxl
  have hx2l : (xlo : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hxl 2
  have hx2h : x ^ 2 ≤ (xhi : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hxh 2
  have hsq : |x * x| < (2 : ℝ) ^ 1022 := by
    rw [abs_mul, ← sq, sq_abs]
    have : x ^ 2 ≤ 1024 := by nlinarith
    linarith [show (1024 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hxxf, hxxe⟩ := F64MulBounds.mul_real_mixed X X hX hX hsq
  set xx := value (Wasm.IEEE64.mul X X)
  have hxx2 : x * x = x ^ 2 := by ring
  rw [hxx2, abs_of_nonneg (sq_nonneg x), hu, he] at hxxe
  have hxl2 := (abs_le.mp hxxe).1
  have hxh2 := (abs_le.mp hxxe).2
  set m : ℝ := (xlo : ℝ) ^ 2 * (1 - uQ) - etaQ with hm
  have hm0 : 0 < m := by rw [hm, hu0, he0]; nlinarith
  have hxxm : m ≤ xx := by
    have : (xlo : ℝ) ^ 2 * (1 - uQ) ≤ x ^ 2 * (1 - uQ) :=
      mul_le_mul_of_nonneg_right hx2l (by rw [hu0]; norm_num)
    rw [hm]
    nlinarith
  have hxxM : xx ≤ (xhi : ℝ) ^ 2 * (1 + uQ) + etaQ := by
    have : x ^ 2 * (1 + uQ) ≤ (xhi : ℝ) ^ 2 * (1 + uQ) :=
      mul_le_mul_of_nonneg_right hx2h (by rw [hu0]; norm_num)
    nlinarith
  have hxx0 : 0 < xx := lt_of_lt_of_le hm0 hxxm
  have hxxs : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul X X) ≠ 0 := by
    intro h0
    have : xx = 0 := by
      simp only [xx, value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    linarith
  have hq : |value (0x3FF0000000000000 : UInt64) / xx| < (2 : ℝ) ^ 1022 := by
    rw [one_value, abs_of_pos (by positivity)]
    have : 1 / xx ≤ 1 / m := one_div_le_one_div_of_le hm0 hxxm
    have h2 : 1 / m ≤ 2 := by
      rw [div_le_iff₀ hm0]
      rw [hm, hu0, he0]
      nlinarith
    linarith [show (2 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hsf, hse⟩ := F64DivBounds.div_real_mixed _ _ one_finite hxxf hxxs hq
  rw [one_value, abs_of_pos (by positivity : (0 : ℝ) < 1 / xx), hu, he] at hse
  set s := value (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))
  have hsl := (abs_le.mp hse).1
  have hsh := (abs_le.mp hse).2
  refine ⟨hsf, ?_, ?_, ?_⟩
  · push_cast
    have h1x : (1 - (uQ : ℝ)) / ((xhi : ℝ) ^ 2 * (1 + uQ) + etaQ) ≤ (1 - uQ) / xx :=
      div_le_div_of_nonneg_left (by rw [hu0]; norm_num) hxx0 hxxM
    have h2x : (1 - (uQ : ℝ)) / xx = 1 / xx - uQ * (1 / xx) := by ring
    linarith
  · push_cast
    have h1x : (1 + (uQ : ℝ)) / xx ≤ (1 + uQ) / ((xlo : ℝ) ^ 2 * (1 - uQ) - etaQ) :=
      div_le_div_of_nonneg_left (by rw [hu0]; norm_num) hm0 hxxm
    have h2x : (1 + (uQ : ℝ)) / xx = 1 / xx + uQ * (1 / xx) := by ring
    linarith
  · have hx20 : 0 < x ^ 2 := by positivity
    have hdiff : |1 / xx - (x ^ 2)⁻¹| ≤ (uQ + etaQ / (xlo : ℝ) ^ 2) / m := by
      have heq : 1 / xx - (x ^ 2)⁻¹ = (x ^ 2 - xx) / (xx * x ^ 2) := by field_simp
      rw [heq, abs_div, abs_of_pos (mul_pos hxx0 hx20), abs_sub_comm]
      rw [div_le_div_iff₀ (by positivity) hm0]
      have h3 : |xx - x ^ 2| * m ≤ (uQ * x ^ 2 + etaQ) * m :=
        mul_le_mul_of_nonneg_right hxxe hm0.le
      have h4 : (uQ * x ^ 2 + etaQ) * m ≤ ((uQ : ℝ) + etaQ / (xlo : ℝ) ^ 2) * (xx * x ^ 2) := by
        have hxl0 : (0 : ℝ) < (xlo : ℝ) ^ 2 := by positivity
        have h5 : (etaQ : ℝ) ≤ etaQ / (xlo : ℝ) ^ 2 * x ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hxl0]
          exact mul_le_mul_of_nonneg_left hx2l (by rw [he0]; positivity)
        have h6 : (uQ * x ^ 2 + etaQ) ≤ ((uQ : ℝ) + etaQ / (xlo : ℝ) ^ 2) * x ^ 2 := by
          nlinarith
        have h7 : 0 ≤ (uQ : ℝ) + etaQ / (xlo : ℝ) ^ 2 := by rw [hu0, he0]; positivity
        calc (uQ * x ^ 2 + etaQ) * m ≤ ((uQ : ℝ) + etaQ / (xlo : ℝ) ^ 2) * x ^ 2 * m :=
              mul_le_mul_of_nonneg_right h6 hm0.le
          _ ≤ ((uQ : ℝ) + etaQ / (xlo : ℝ) ^ 2) * x ^ 2 * xx :=
              mul_le_mul_of_nonneg_left hxxm (by positivity)
          _ = _ := by ring
      linarith
    have hu1 : (uQ : ℝ) * (1 / xx) ≤ uQ / m := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (by rw [hu0]; positivity) hm0 hxxm
    have htri := abs_sub_le s (1 / xx) ((x ^ 2)⁻¹)
    simp only [tailSErr]
    push_cast
    rw [← hm]
    linarith

/-- The bound on the computed `R/S` against `R/S (1/x²)`. -/
def tailQErr (R S : List ℚ) (xlo slo shi : ℚ) : ℚ :=
  let eR := hornerErr R slo shi
  let eS := hornerErr S slo shi
  let MR := magBound R slo shi
  let mS := lowBound S slo shi
  (eR / (mS - eS) + MR * eS / ((mS - eS) * mS) + uQ * ((MR + eR) / (mS - eS)) + etaQ) +
    magBound (subP (mulP (derivP R) S) (mulP R (derivP S))) slo shi / mS ^ 2 * tailSErr xlo

/-- The bound on the computed `(z - x)(z + x)`. -/
def tailPErr (xhi : ℚ) : ℚ :=
  xhi / 2 ^ 20 * (uQ * (2 * xhi)) + uQ * (xhi / 2 ^ 20 * (2 * xhi + uQ * (2 * xhi))) + etaQ

/-- The bound on the computed argument of the second exponential. -/
def tailDelta (R S : List ℚ) (xlo xhi slo shi : ℚ) : ℚ :=
  tailPErr xhi + tailQErr R S xlo slo shi +
    uQ * (2 * xhi ^ 2 / 2 ^ 20 + magBound R slo shi / lowBound S slo shi + tailPErr xhi +
      tailQErr R S xlo slo shi)

/-- The rational conditions of `tail_arg2` for one interval. -/
def tailOK (R S : List ℚ) (xlo xhi slo shi : ℚ) : Bool :=
  decide (1 ≤ xlo) && decide (xlo ≤ xhi) && decide (xhi < 32) && decide (0 ≤ slo) &&
    decide (slo ≤ (1 - uQ) / (xhi ^ 2 * (1 + uQ) + etaQ) - etaQ) &&
    decide ((1 + uQ) / (xlo ^ 2 * (1 - uQ) - etaQ) + etaQ ≤ shi) &&
    hornerOK R slo shi && hornerOK S slo shi &&
    decide (hornerErr S slo shi < lowBound S slo shi) && decide (0 < lowBound S slo shi) &&
    decide ((magBound R slo shi + hornerErr R slo shi) /
      (lowBound S slo shi - hornerErr S slo shi) < 2 ^ 1000) &&
    decide (tailDelta R S xlo xhi slo shi + epsT ≤ 1 / 2)

theorem tailOK_data (R S : List ℚ) (xlo xhi slo shi : ℚ) (hok : tailOK R S xlo xhi slo shi = true) :
    1 ≤ xlo ∧ xlo ≤ xhi ∧ xhi < 32 ∧ 0 ≤ slo ∧
      slo ≤ (1 - uQ) / (xhi ^ 2 * (1 + uQ) + etaQ) - etaQ ∧
      (1 + uQ) / (xlo ^ 2 * (1 - uQ) - etaQ) + etaQ ≤ shi ∧
      hornerOK R slo shi = true ∧ hornerOK S slo shi = true ∧
      hornerErr S slo shi < lowBound S slo shi ∧ 0 < lowBound S slo shi ∧
      (magBound R slo shi + hornerErr R slo shi) / (lowBound S slo shi - hornerErr S slo shi) <
        2 ^ 1000 ∧
      tailDelta R S xlo xhi slo shi + epsT ≤ 1 / 2 := by
  simp only [tailOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩, k⟩, l⟩ := hok
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The computed argument of the second exponential, for `x` in `[xlo, xhi]`. -/
theorem tail_arg2 (R S : List ℚ) (RW SW : List UInt64)
    (hR : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) RW R)
    (hS : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) SW S)
    (hRn : R ≠ []) (hSn : S ≠ [])
    (xlo xhi slo shi : ℚ) (hok : tailOK R S xlo xhi slo shi = true)
    (X : UInt64) (hX : Finite X) (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi) :
    Approx (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))))
      ((value (zWord X) - value X) * (value (zWord X) + value X) +
        eval R (value X ^ 2)⁻¹ / eval S (value X ^ 2)⁻¹)
      (tailDelta R S xlo xhi slo shi) := by
  obtain ⟨h1, hxx, h32, hs0, hslo, hshi, hokR, hokS, hSe, hmS, hmaxq, _⟩ :=
    tailOK_data R S xlo xhi slo shi hok
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have he : multiplicationUnderflowEpsilon = ((etaQ : ℚ) : ℝ) := etaQ_eq.symm
  have hu0 : (uQ : ℝ) = 1 / 2 ^ 53 := by simp [uQ]
  have he0 : (etaQ : ℝ) = 1 / 2 ^ 1075 := by simp [etaQ]
  set x := value X with hxdef
  have h1' : (1 : ℝ) ≤ xlo := by exact_mod_cast h1
  have h32' : (xhi : ℝ) < 32 := by exact_mod_cast h32
  have hx1 : 1 ≤ x := h1'.trans hxl
  have hxhi0 : (0 : ℝ) ≤ xhi := by linarith
  obtain ⟨hsf, hsl, hsh, hse⟩ := tail_s xlo xhi h1 h32 X hX hxl hxh
  rw [← hxdef] at hse
  set sW := Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)
  set s := value sW
  have hsl' : (slo : ℝ) ≤ s := le_trans (by exact_mod_cast hslo) hsl
  have hsh' : s ≤ (shi : ℝ) := le_trans hsh (by exact_mod_cast hshi)
  -- `1/x²` in `[slo, shi]`
  have hx0 : 0 < x := by linarith
  have hix : (slo : ℝ) ≤ (x ^ 2)⁻¹ ∧ (x ^ 2)⁻¹ ≤ (shi : ℝ) := by
    have hxl2 : (xlo : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hxl 2
    have hxh2 : x ^ 2 ≤ (xhi : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hxh 2
    have hslo' : (slo : ℝ) ≤ (1 - uQ) / ((xhi : ℝ) ^ 2 * (1 + uQ) + etaQ) - etaQ := by
      exact_mod_cast hslo
    have hshi' : (1 + (uQ : ℝ)) / ((xlo : ℝ) ^ 2 * (1 - uQ) - etaQ) + etaQ ≤ shi := by
      exact_mod_cast hshi
    have hm0 : (0 : ℝ) < (xlo : ℝ) ^ 2 * (1 - uQ) - etaQ := by rw [hu0, he0]; nlinarith
    constructor
    · have h2 : (1 - (uQ : ℝ)) / ((xhi : ℝ) ^ 2 * (1 + uQ) + etaQ) ≤ 1 / x ^ 2 := by
        rw [div_le_div_iff₀ (by rw [hu0, he0]; positivity) (by positivity)]
        rw [hu0, he0]
        nlinarith
      rw [inv_eq_one_div]
      have : (0 : ℝ) ≤ etaQ := by rw [he0]; positivity
      linarith
    · have h2 : 1 / x ^ 2 ≤ (1 + (uQ : ℝ)) / ((xlo : ℝ) ^ 2 * (1 - uQ) - etaQ) := by
        rw [div_le_div_iff₀ (by positivity) hm0]
        rw [hu0, he0]
        nlinarith
      rw [inv_eq_one_div]
      have : (0 : ℝ) ≤ etaQ := by rw [he0]; positivity
      linarith
  -- the quotient
  have hP := hornerW_approx R RW hR hRn slo shi sW hsf hsl' hsh' hokR
  have hQ := hornerW_approx S SW hS hSn slo shi sW hsf hsl' hsh' hokS
  have hMR : |eval R s| ≤ ((magBound R slo shi : ℚ) : ℝ) := magBound_sound R slo shi s hsl' hsh'
  have hmSs : ((lowBound S slo shi : ℚ) : ℝ) ≤ eval S s := lowBound_sound S slo shi s hsl' hsh'
  have hSe' : ((hornerErr S slo shi : ℚ) : ℝ) < lowBound S slo shi := by exact_mod_cast hSe
  have hmS' : (0 : ℝ) < lowBound S slo shi := by exact_mod_cast hmS
  have hmaxq' : (((magBound R slo shi : ℚ) : ℝ) + hornerErr R slo shi) /
      ((lowBound S slo shi : ℝ) - hornerErr S slo shi) < 2 ^ 1022 := by
    have h : ((((magBound R slo shi + hornerErr R slo shi) /
        (lowBound S slo shi - hornerErr S slo shi)) : ℚ) : ℝ) < 2 ^ 1000 := by
      exact_mod_cast hmaxq
    push_cast at h
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num]
  have hD := F64DivApprox.div_approx hP hQ _ _ hMR hmSs hSe' hmaxq'
  have hSpos : ∀ t ∈ Set.Icc (slo : ℝ) shi, 0 < eval S t :=
    fun t ht => lt_of_lt_of_le hmS' (lowBound_sound S slo shi t ht.1 ht.2)
  set A := subP (mulP (derivP R) S) (mulP R (derivP S))
  have hL0 : (0 : ℝ) ≤ ((magBound A slo shi / lowBound S slo shi ^ 2 : ℚ) : ℝ) := by
    push_cast
    exact div_nonneg (magBound_nonneg A slo shi s hsl' hsh') (by positivity)
  have hLd : ∀ t ∈ Set.Icc (slo : ℝ) shi,
      |eval (derivP R) t * eval S t - eval R t * eval (derivP S) t| ≤
        ((magBound A slo shi / lowBound S slo shi ^ 2 : ℚ) : ℝ) * eval S t ^ 2 := by
    intro t ht
    have hA : eval A t = eval (derivP R) t * eval S t - eval R t * eval (derivP S) t := by
      simp only [A, eval_subP, eval_mulP]
    rw [← hA]
    have h1 := magBound_sound A slo shi t ht.1 ht.2
    have h2 : ((lowBound S slo shi : ℚ) : ℝ) ^ 2 ≤ eval S t ^ 2 :=
      pow_le_pow_left₀ hmS'.le (lowBound_sound S slo shi t ht.1 ht.2) 2
    have h3 : ((magBound A slo shi : ℚ) : ℝ) =
        ((magBound A slo shi / lowBound S slo shi ^ 2 : ℚ) : ℝ) *
          ((lowBound S slo shi : ℚ) : ℝ) ^ 2 := by
      push_cast
      field_simp
    calc |eval A t| ≤ ((magBound A slo shi : ℚ) : ℝ) := h1
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hL0
  have hLip := F64DivApprox.ratio_lipschitz R S slo shi _ hSpos hLd
    (x := s) (y := (x ^ 2)⁻¹) ⟨hsl', hsh'⟩ hix
  have hQ2 : Approx (Wasm.IEEE64.div (hornerW RW sW) (hornerW SW sW))
      (eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹) (tailQErr R S xlo slo shi) := by
    refine ⟨hD.1, ?_⟩
    have h1 := hD.2
    have h2 : |eval R s / eval S s - eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹| ≤
        ((magBound A slo shi / lowBound S slo shi ^ 2 : ℚ) : ℝ) * tailSErr xlo :=
      hLip.trans (mul_le_mul_of_nonneg_left hse hL0)
    have hsum := abs_sub_le (value (Wasm.IEEE64.div (hornerW RW sW) (hornerW SW sW)))
      (eval R s / eval S s) (eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹)
    have hdef : ((tailQErr R S xlo slo shi : ℚ) : ℝ) =
        (((hornerErr R slo shi : ℚ) : ℝ) / ((lowBound S slo shi : ℝ) - hornerErr S slo shi) +
          (magBound R slo shi : ℝ) * hornerErr S slo shi /
            (((lowBound S slo shi : ℝ) - hornerErr S slo shi) * lowBound S slo shi) +
          unitRoundoff64 * (((magBound R slo shi : ℝ) + hornerErr R slo shi) /
            ((lowBound S slo shi : ℝ) - hornerErr S slo shi)) +
          multiplicationUnderflowEpsilon) +
        ((magBound A slo shi / lowBound S slo shi ^ 2 : ℚ) : ℝ) * tailSErr xlo := by
      rw [hu, he]
      simp only [tailQErr, A]
      push_cast
      ring
    rw [hdef]
    linarith
  -- the split
  obtain ⟨hzf, hzs, _, _, _, _, hz0, hzx, hgap⟩ := z_facts X hX hx1 (by linarith)
  obtain ⟨hd1f, hd1v⟩ := d1_exact X hX hx1 (by linarith)
  rw [← hxdef] at hzx hgap hd1v
  set z := value (zWord X)
  have hd1 : Approx (Wasm.IEEE64.sub (zWord X) X) (z - x) 0 := ⟨hd1f, by rw [hd1v]; simp⟩
  have hzxa : |z - x| ≤ (xhi : ℝ) / 2 ^ 20 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have : x / 2 ^ 20 ≤ (xhi : ℝ) / 2 ^ 20 := div_le_div_of_nonneg_right hxh (by positivity)
    linarith
  have hzx2 : |z + x| ≤ 2 * (xhi : ℝ) := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hd2 := add_approx (approx_self (zWord X) hzf) (approx_self X hX) (2 * (xhi : ℝ))
    (by rw [add_zero, add_zero]; exact hzx2) (by linarith [show (64 : ℝ) < 2 ^ 1023 by norm_num])
  have hp0 := mul_approx hd1 hd2 ((xhi : ℝ) / 2 ^ 20) (2 * (xhi : ℝ)) hzxa hzx2 (by
    have hu1 : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    simp only [add_zero, zero_add, hu1]
    have h1 : (xhi : ℝ) / 2 ^ 20 ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [show (32 : ℝ) ≤ 2 ^ 20 by norm_num]
    have h2 : 2 * (xhi : ℝ) + 1 / 2 ^ 53 * (2 * xhi) ≤ 128 := by linarith only [h32']
    have h3 : (xhi : ℝ) / 2 ^ 20 * (2 * xhi + 1 / 2 ^ 53 * (2 * xhi)) ≤ 1 * 128 :=
      mul_le_mul h1 h2 (by linarith) (by norm_num)
    linarith [show (128 : ℝ) < 2 ^ 1022 by norm_num])
  have hp : Approx (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
      ((z - x) * (z + x)) (tailPErr xhi) := hp0.mono (le_of_eq (by
    rw [hu, he]
    simp only [tailPErr]
    push_cast
    ring))
  -- the sum
  have hRS : |eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹| ≤
      ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) := by
    have hq := hSpos _ hix
    rw [abs_div, abs_of_pos hq]
    push_cast
    exact div_le_div₀ ((abs_nonneg _).trans (magBound_sound R slo shi _ hix.1 hix.2))
      (magBound_sound R slo shi _ hix.1 hix.2) hmS' (lowBound_sound S slo shi _ hix.1 hix.2)
  have hpq : |(z - x) * (z + x)| ≤ 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 := by
    rw [abs_mul]
    calc |z - x| * |z + x| ≤ (xhi : ℝ) / 2 ^ 20 * (2 * xhi) :=
          mul_le_mul hzxa hzx2 (abs_nonneg _) (div_nonneg hxhi0 (by norm_num))
      _ = 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 := by ring
  have hT := add_approx hp hQ2
    (2 * (xhi : ℝ) ^ 2 / 2 ^ 20 + ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) +
      ((tailPErr xhi : ℚ) : ℝ) + ((tailQErr R S xlo slo shi : ℚ) : ℝ)) (by
    have := abs_add_le ((z - x) * (z + x)) (eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹)
    linarith) (by
    have hb : ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) +
        ((tailPErr xhi : ℚ) : ℝ) + ((tailQErr R S xlo slo shi : ℚ) : ℝ) < 2 ^ 1001 := by
      have h2 := (abs_nonneg _).trans hp.2
      have h3 := (abs_nonneg _).trans hQ2.2
      have h4 := (Rat.cast_lt (K := ℝ)).mpr hmaxq
      have h5 := (Rat.cast_le (K := ℝ)).mpr (tailOK_data R S xlo xhi slo shi hok).2.2.2.2.2.2.2.2.2.2.2
      have hMR0 := magBound_nonneg R slo shi s hsl' hsh'
      have he0' : (0 : ℝ) ≤ hornerErr R slo shi := (abs_nonneg _).trans hP.2
      have hseS : (0 : ℝ) ≤ hornerErr S slo shi := (abs_nonneg _).trans hQ.2
      have h6 : ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) ≤
          (((magBound R slo shi + hornerErr R slo shi) /
            (lowBound S slo shi - hornerErr S slo shi) : ℚ) : ℝ) := by
        push_cast
        apply div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
      have h7 : ((tailPErr xhi : ℚ) : ℝ) + ((tailQErr R S xlo slo shi : ℚ) : ℝ) ≤
          ((tailDelta R S xlo xhi slo shi : ℚ) : ℝ) := by
        have hu' : (0 : ℝ) ≤ uQ := by rw [hu0]; positivity
        have hRS0 := (abs_nonneg _).trans hRS
        have hsum0 : (0 : ℝ) ≤ 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 +
            ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) + ((tailPErr xhi : ℚ) : ℝ) +
            ((tailQErr R S xlo slo shi : ℚ) : ℝ) := by
          have : (0 : ℝ) ≤ 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 := by positivity
          linarith only [this, hRS0, h2, h3]
        have hm := mul_nonneg hu' hsum0
        have hdef : ((tailDelta R S xlo xhi slo shi : ℚ) : ℝ) = ((tailPErr xhi : ℚ) : ℝ) +
            ((tailQErr R S xlo slo shi : ℚ) : ℝ) + (uQ : ℝ) * (2 * (xhi : ℝ) ^ 2 / 2 ^ 20 +
            ((magBound R slo shi / lowBound S slo shi : ℚ) : ℝ) + ((tailPErr xhi : ℚ) : ℝ) +
            ((tailQErr R S xlo slo shi : ℚ) : ℝ)) := by
          simp only [tailDelta]
          push_cast
          ring
        linarith only [hm, hdef]
      have h8 : (0 : ℝ) ≤ epsT := by norm_num [epsT]
      have h5' : ((tailDelta R S xlo xhi slo shi : ℚ) : ℝ) + (epsT : ℝ) ≤ 1 / 2 := by
        push_cast at h5 ⊢
        linarith only [h5]
      have h4' : (((magBound R slo shi + hornerErr R slo shi) /
          (lowBound S slo shi - hornerErr S slo shi) : ℚ) : ℝ) < 2 ^ 1000 := by
        push_cast at h4 ⊢
        exact h4
      linarith only [h4', h5', h6, h7, h8, show (1 : ℝ) / 2 + 2 ^ 1000 ≤ 2 ^ 1001 by norm_num]
    have h9 : 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 ≤ 1 := by
      have h10 : (xhi : ℝ) ^ 2 ≤ 32 ^ 2 := pow_le_pow_left₀ hxhi0 h32'.le 2
      have h11 : (2 : ℝ) * 32 ^ 2 / 2 ^ 20 ≤ 1 := by norm_num
      have h12 : 2 * (xhi : ℝ) ^ 2 / 2 ^ 20 ≤ 2 * 32 ^ 2 / 2 ^ 20 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith only [h10]
      linarith only [h11, h12]
    linarith only [hb, h9, show (1 : ℝ) + 2 ^ 1001 < 2 ^ 1023 by norm_num])
  refine hT.mono (le_of_eq ?_)
  rw [hu]
  simp only [tailDelta]
  push_cast
  ring

#print axioms erfTail_bits
#print axioms ra_rel
#print axioms sa_rel
#print axioms rb_rel
#print axioms sb_rel
#print axioms tail_s
#print axioms tail_arg2

end Library.Numerics.Float64.Erf.ErfTailEval
