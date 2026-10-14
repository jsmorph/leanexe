import Verified.Examples.LgammaPolyIv
import Verified.Examples.TgammaPolyLip

/-!
The series term of `Lgamma.asLgammaAsymAccurate`: from `zh + zl ≈ Z = 1/x` (`LgammaAsymRecip`),
the code squares the pair with `mulDD`, evaluates the polynomial of the range with `polyDD` at the
square, and multiplies the result by the pair with `mulDD`.  `series_gen` puts the result within
`R/2^99` of `Z · P (Z²)` for `R ≈ Z`, from a kernel check of the polynomial's steps on
subintervals (`LgammaPolyIv.kern_iv`), a check that its value lies in `[lo, hi]` (`valOk`), and its
Lipschitz bound `TgammaPolyLip.lipQ`.  The square differs from `Z²` by at most `R²/2^94`.
-/

namespace Verified.Examples.LgammaAsymSeries
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaMul TgammaWords
  LgammaPolyIv

set_option exponentiation.threshold 4096

/-- The enclosures of the polynomial's value on the subintervals lie in `[lo, hi]`. -/
def valOk (tab : Array UInt64) (o N P : ℕ) (X lo hi : ℚ) : Bool :=
  (List.range P).all fun p =>
    decide (lo ≤ (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) (N - 1)).1) &&
    decide ((hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) (N - 1)).2 ≤ hi)

/-- **The value of the polynomial** on `[0, X]` lies in `[lo, hi]`. -/
theorem val_at (tab : Array UInt64) (o N P : ℕ) (X lo hi : ℚ) (hP : 0 < P) (hN : 1 ≤ N)
    (hval : valOk tab o N P X lo hi = true) (v : ℝ) (hv0 : 0 ≤ v) (hvX : v ≤ X) :
    (lo : ℝ) ≤ PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ∧
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ≤ hi := by
  simp only [valOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hval
  obtain ⟨p, hp, hpa, hpb⟩ := piece_cover (X : ℝ) P v hv0 P hP
    (by rw [mul_div_assoc, div_self (by exact_mod_cast hP.ne'), mul_one]; exact hvX)
  have hX0 : (0 : ℚ) ≤ X := by exact_mod_cast hv0.trans hvX
  have he : horner (fun k => (cq tab o k : ℝ)) N 0 v (N - 1) =
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v := by
    rw [horner_eval _ N hN, zero_mul, add_zero,
      show LgammaApprox.ddCoeffs tab o N = (List.range N).map (fun k =>
        LgammaApprox.q tab (o + 2 * k) + LgammaApprox.q tab (o + 2 * k + 1)) from rfl,
      eval_map_range]
    rfl
  obtain ⟨h1, h2⟩ := horner_iv (fun k => (cq tab o k : ℝ)) (cq tab o) N (fun _ _ => rfl)
    (X * p / P) (X * (p + 1) / P) (div_nonneg (mul_nonneg hX0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    v (by push_cast; exact hpa) (by push_cast; exact hpb) (N - 1) (by omega)
  obtain ⟨h3, h4⟩ := hval p hp
  rw [he] at h1 h2
  exact ⟨le_trans (by exact_mod_cast h3) h1, le_trans h2 (by exact_mod_cast h4)⟩

set_option maxHeartbeats 2000000 in
/-- **The series term** `z P (z²)` within `R/2^99` of `Z P (Z²)`. -/
theorem series_gen (hF : FmaSpec.FmaNearest) (o N P : ℕ) (X Xh Xl Rm lo hi Lp : ℚ)
    (C Cl E Λ K : List ℚ)
    (hok : stepsIvOk Lgamma.asymTable (o + 2) N P X Xh Xl C Cl E Λ K = true)
    (hval : valOk Lgamma.asymTable (o + 2) N P X lo hi = true)
    (hlip : TgammaPolyLip.lipQ X (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) ≤ Lp)
    (hE0 : ∀ m, 0 ≤ E.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0) (hP : 0 < P) (hN1 : 1 ≤ N)
    (hon : o + 2 + 2 * N < 2 ^ 63)
    (hXh : Rm ^ 2 * (1 + 1 / 2 ^ 50) ≤ Xh) (hXl : Rm ^ 2 / 2 ^ 47 + 1 / 2 ^ 1069 ≤ Xl)
    (hX : Rm ^ 2 * (1 + 1 / 2 ^ 40) ≤ X) (hRm1 : Rm ≤ 1)
    (hEn : E.getD (N - 1) 0 ≤ 1 / 2 ^ 105) (hΛn : Λ.getD (N - 1) 0 ≤ 1 / 2 ^ 52)
    (hhi : hi ≤ 1 / 8) (hlo : -(1 / 8) ≤ lo) (hLp : Lp ≤ 1 / 2 ^ 8)
    (o' n' : UInt64) (ho : o'.toNat = o + 2) (hn : n'.toNat = N)
    (zh zl : Float) (hzh : Finite zh.toBits) (hzl : Finite zl.toBits) (R Z : ℝ)
    (hR : 1 / 2 ^ 120 ≤ R) (hRm : R ≤ Rm)
    (hz1 : |value zh.toBits - R| ≤ R / 2 ^ 52) (hz2 : |value zl.toBits| ≤ R / 2 ^ 49)
    (hz3 : |value zh.toBits + value zl.toBits - Z| ≤ R / 2 ^ 98) :
    let W := mulDD zh zl zh zl
    let F := Lgamma.polyDD Lgamma.asymTable o' n' W.1 W.2 0.0
    let G := mulDD zh zl F.1 F.2
    Finite G.1.toBits ∧ Finite G.2.toBits ∧
      |value G.1.toBits + value G.2.toBits -
          Z * PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) (Z ^ 2)| ≤
        R / 2 ^ 99 ∧
      |value G.1.toBits| ≤ R / 7 ∧ |value G.2.toBits| ≤ R / 2 ^ 50 := by
  intro W F G
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hR1 : R ≤ 1 := hRm.trans (by exact_mod_cast hRm1)
  set a := value zh.toBits with ha
  set b := value zl.toBits with hb
  have hab : |a| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub a R
    rw [abs_of_pos hR0] at this
    linarith
  have hRu : 0 ≤ R * (1 + 1 / 2 ^ 52) := mul_nonneg hR0.le (by norm_num)
  have hRv : 0 ≤ R / 2 ^ 49 := div_nonneg hR0.le (by norm_num)
  -- `R²`, the scale of the square
  set Q := R * R with hQ
  have hQ0 : 1 / 2 ^ 240 ≤ Q := by
    have := mul_le_mul hR hR (by positivity) hR0.le
    rw [← hQ] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 120 * (1 / 2 ^ 120) = 1 / 2 ^ 240)]
  have hQm : Q ≤ (Rm : ℝ) ^ 2 := by
    rw [hQ, ← sq]; exact pow_le_pow_left₀ hR0.le hRm 2
  have hQ1 : Q ≤ 1 := by
    have := mul_le_mul hR1 hR1 hR0.le (by norm_num)
    rw [← hQ] at this
    linarith
  have hη : (1 : ℝ) / 2 ^ 1070 ≤ Q / 2 ^ 800 := by
    have := div_le_div_of_nonneg_right hQ0 (by positivity : (0 : ℝ) ≤ 2 ^ 800)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 240 / 2 ^ 800)]
  -- `W = z²`
  obtain ⟨w1f, w2f, we, w2b, w1b⟩ := mulDD_spec hF zh zl zh zl hzh hzl hzh hzl
    (R * (1 + 1 / 2 ^ 52) * (R * (1 + 1 / 2 ^ 52))) (R * (1 + 1 / 2 ^ 52) * (R / 2 ^ 49))
    (R / 2 ^ 49 * (R * (1 + 1 / 2 ^ 52))) (R / 2 ^ 49 * (R / 2 ^ 49))
    (mul_le_mul hab hab (abs_nonneg _) hRu) (mul_le_mul hab hz2 (abs_nonneg _) hRu)
    (mul_le_mul hz2 hab (abs_nonneg _) hRv) (mul_le_mul hz2 hz2 (abs_nonneg _) hRv)
    (by nlinarith) (by nlinarith)
  rw [show mulDD zh zl zh zl = W from rfl] at w1f w2f we w2b w1b
  have eH : R * (1 + 1 / 2 ^ 52) * (R * (1 + 1 / 2 ^ 52)) = Q * (1 + 1 / 2 ^ 52) ^ 2 := by
    rw [hQ]; ring
  have eP : R * (1 + 1 / 2 ^ 52) * (R / 2 ^ 49) = Q * (1 + 1 / 2 ^ 52) / 2 ^ 49 := by
    rw [hQ]; ring
  have eP' : R / 2 ^ 49 * (R * (1 + 1 / 2 ^ 52)) = Q * (1 + 1 / 2 ^ 52) / 2 ^ 49 := by
    rw [hQ]; ring
  have eL : R / 2 ^ 49 * (R / 2 ^ 49) = Q / 2 ^ 98 := by rw [hQ]; ring
  rw [eH, eP, eP', eL, ← ha, ← hb] at we
  rw [eH, eP, eP'] at w2b
  rw [eH] at w1b
  set w := value W.1.toBits + value W.2.toBits with hw
  -- `Z` near `R`
  have hZR : |Z - R| ≤ R / 2 ^ 48 := by
    have h1 := abs_sub (a + b - Z) (a - R)
    have h2 : |a + b - Z - (a - R)| = |Z - R - b| := by
      rw [show a + b - Z - (a - R) = -(Z - R - b) by ring, abs_neg]
    have h3 := abs_sub_abs_le_abs_sub (Z - R) b
    have h4 : R / 2 ^ 98 + R / 2 ^ 52 + R / 2 ^ 49 ≤ R / 2 ^ 48 := by
      have : R / 2 ^ 98 + R / 2 ^ 52 + R / 2 ^ 49 = R * (1 / 2 ^ 98 + 1 / 2 ^ 52 + 1 / 2 ^ 49) := by
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 98 + 1 / 2 ^ 52 + 1 / 2 ^ 49 ≤
        1 / 2 ^ 48) hR0.le
      linarith [(by ring : R * (1 / 2 ^ 48) = R / 2 ^ 48)]
    rw [h2] at h1
    linarith
  have hZlo : R * (1 - 1 / 2 ^ 48) ≤ Z := by
    have := (abs_le.mp hZR).1
    linarith
  have hZhi : Z ≤ R * (1 + 1 / 2 ^ 48) := by
    have := (abs_le.mp hZR).2
    linarith
  have hZ0 : 0 ≤ Z := le_trans (mul_nonneg hR0.le (by norm_num)) hZlo
  -- `w` near `Z²`
  have hsq : |(a + b) * (a + b) - Z ^ 2| ≤ 3 * Q / 2 ^ 98 := by
    rw [show (a + b) * (a + b) - Z ^ 2 = (a + b - Z) * (a + b + Z) by ring, abs_mul]
    have h1 : |a + b + Z| ≤ 3 * R := by
      have := abs_add_le (a + b - Z) (2 * Z)
      rw [show a + b - Z + 2 * Z = a + b + Z by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg hZ0] at this
      have : R / 2 ^ 98 ≤ R / 2 ^ 10 := div_le_div_of_nonneg_left hR0.le (by norm_num) (by norm_num)
      nlinarith
    have := mul_le_mul hz3 h1 (abs_nonneg _) (div_nonneg hR0.le (by norm_num))
    linarith [(by rw [hQ]; ring : R / 2 ^ 98 * (3 * R) = 3 * Q / 2 ^ 98)]
  have hwZ : |w - Z ^ 2| ≤ Q / 2 ^ 94 := by
    have h1 := abs_add_le (w - (a + b) * (a + b)) ((a + b) * (a + b) - Z ^ 2)
    rw [show w - (a + b) * (a + b) + ((a + b) * (a + b) - Z ^ 2) = w - Z ^ 2 by ring] at h1
    have h2 : Q / 2 ^ 98 + (4 * (Q * (1 + 1 / 2 ^ 52) / 2 ^ 49 + Q * (1 + 1 / 2 ^ 52) / 2 ^ 49) +
        Q * (1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 51) / 2 ^ 53 + Q / 2 ^ 800 + 3 * Q / 2 ^ 98 ≤ Q / 2 ^ 94 := by
      have : Q / 2 ^ 98 + (4 * (Q * (1 + 1 / 2 ^ 52) / 2 ^ 49 + Q * (1 + 1 / 2 ^ 52) / 2 ^ 49) +
          Q * (1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 51) / 2 ^ 53 + Q / 2 ^ 800 + 3 * Q / 2 ^ 98 =
          Q * (1 / 2 ^ 98 + (4 * ((1 + 1 / 2 ^ 52) / 2 ^ 49 + (1 + 1 / 2 ^ 52) / 2 ^ 49) +
            (1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 800 + 3 / 2 ^ 98) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 98 + (4 * ((1 + 1 / 2 ^ 52) /
        2 ^ 49 + (1 + 1 / 2 ^ 52) / 2 ^ 49) + (1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 51) / 2 ^ 53 +
        1 / 2 ^ 800 + 3 / 2 ^ 98 ≤ 1 / 2 ^ 94) (by linarith : (0 : ℝ) ≤ Q)
      linarith [(by ring : Q * (1 / 2 ^ 94) = Q / 2 ^ 94)]
    linarith
  -- the point of the polynomial
  have hZ2lo : Q * (1 - 1 / 2 ^ 46) ≤ Z ^ 2 := by
    have h1 := mul_le_mul hZlo hZlo (mul_nonneg hR0.le (by norm_num)) hZ0
    have h2 : R * (1 - 1 / 2 ^ 48) * (R * (1 - 1 / 2 ^ 48)) = Q * (1 - 1 / 2 ^ 48) ^ 2 := by
      rw [hQ]; ring
    rw [h2, ← sq] at h1
    nlinarith
  have hZ2hi : Z ^ 2 ≤ Q * (1 + 1 / 2 ^ 46) := by
    have h1 := mul_le_mul hZhi hZhi hZ0 (mul_nonneg hR0.le (by norm_num))
    have h2 : R * (1 + 1 / 2 ^ 48) * (R * (1 + 1 / 2 ^ 48)) = Q * (1 + 1 / 2 ^ 48) ^ 2 := by
      rw [hQ]; ring
    rw [h2, ← sq] at h1
    nlinarith
  have hw0 : 0 ≤ w := by
    have := (abs_le.mp hwZ).1
    nlinarith
  have hwX : w ≤ X := by
    have := (abs_le.mp hwZ).2
    have h1 : Q * (1 + 1 / 2 ^ 46) + Q / 2 ^ 94 ≤ (Rm : ℝ) ^ 2 * (1 + 1 / 2 ^ 40) := by
      nlinarith
    have h2 : ((Rm ^ 2 * (1 + 1 / 2 ^ 40) : ℚ) : ℝ) ≤ X := by exact_mod_cast hX
    push_cast at h2
    linarith
  have hW1 : |value W.1.toBits| ≤ (Xh : ℝ) := by
    have h2 : ((Rm ^ 2 * (1 + 1 / 2 ^ 50) : ℚ) : ℝ) ≤ Xh := by exact_mod_cast hXh
    push_cast at h2
    have : Q * (1 + 1 / 2 ^ 52) ^ 2 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        (Rm : ℝ) ^ 2 * (1 + 1 / 2 ^ 50) := by nlinarith
    linarith
  have hW2 : |value W.2.toBits| ≤ (Xl : ℝ) := by
    have h2 : ((Rm ^ 2 / 2 ^ 47 + 1 / 2 ^ 1069 : ℚ) : ℝ) ≤ Xl := by exact_mod_cast hXl
    push_cast at h2
    have : (Q * (1 + 1 / 2 ^ 52) / 2 ^ 49 + Q * (1 + 1 / 2 ^ 52) / 2 ^ 49) * (1 + 1 / 2 ^ 50) +
        Q * (1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 52 + 1 / 2 ^ 1070 ≤ (Rm : ℝ) ^ 2 / 2 ^ 47 + 1 / 2 ^ 1069 := by
      nlinarith
    linarith
  -- the polynomial
  obtain ⟨f1f, f2f, fe, f2b⟩ := kern_iv hF Lgamma.asymTable (o + 2) N P X Xh Xl C Cl E Λ K hok
    hE0 hΛ0 o' n' ho hn hN1 hon W.1 W.2 w1f w2f hW1 hW2 hw0 hwX
  rw [show Lgamma.polyDD Lgamma.asymTable o' n' W.1 W.2 0.0 = F from rfl] at f1f f2f fe f2b
  rw [← hw] at fe
  have hEn' : (E.getD (N - 1) 0 : ℝ) ≤ 1 / 2 ^ 105 := by
    have := (Rat.cast_le (K := ℝ)).mpr hEn; push_cast at this; exact this
  have hΛn' : (Λ.getD (N - 1) 0 : ℝ) ≤ 1 / 2 ^ 52 := by
    have := (Rat.cast_le (K := ℝ)).mpr hΛn; push_cast at this; exact this
  obtain ⟨hv1, hv2⟩ := val_at Lgamma.asymTable (o + 2) N P X lo hi hP hN1 hval w hw0 hwX
  have hlo' : -(1 / 8 : ℝ) ≤ lo := by
    have := (Rat.cast_le (K := ℝ)).mpr hlo; push_cast at this; exact this
  have hhi' : (hi : ℝ) ≤ 1 / 8 := by
    have := (Rat.cast_le (K := ℝ)).mpr hhi; push_cast at this; exact this
  set Pw := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) w with hPw
  set PZ := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) (Z ^ 2) with hPZ
  have hX0 : (0 : ℚ) ≤ X := by exact_mod_cast hw0.trans hwX
  have hlipw := TgammaPolyLip.eval_lip X hX0 w (Z ^ 2) (by rw [abs_of_nonneg hw0]; exact hwX)
    (by
      rw [abs_of_nonneg (sq_nonneg Z)]
      have h2 : ((Rm ^ 2 * (1 + 1 / 2 ^ 40) : ℚ) : ℝ) ≤ X := by exact_mod_cast hX
      push_cast at h2
      nlinarith)
    (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N)
  rw [← hPw, ← hPZ] at hlipw
  have hLp' : ((TgammaPolyLip.lipQ X (LgammaApprox.ddCoeffs Lgamma.asymTable (o + 2) N) : ℚ) : ℝ) ≤
      1 / 2 ^ 8 := by
    have := (Rat.cast_le (K := ℝ)).mpr (hlip.trans hLp); push_cast at this; exact this
  have hlipb : |Pw - PZ| ≤ Q / 2 ^ 102 := by
    have := mul_le_mul hLp' hwZ (abs_nonneg _) (by norm_num)
    linarith [(by ring : 1 / 2 ^ 8 * (Q / 2 ^ 94) = Q / 2 ^ 102)]
  have hFP : |value F.1.toBits + value F.2.toBits - PZ| ≤ 1 / 2 ^ 101 := by
    have := abs_add_le (value F.1.toBits + value F.2.toBits - Pw) (Pw - PZ)
    rw [show value F.1.toBits + value F.2.toBits - Pw + (Pw - PZ) =
      value F.1.toBits + value F.2.toBits - PZ by ring] at this
    have : Q / 2 ^ 102 ≤ 1 / 2 ^ 102 := div_le_div_of_nonneg_right hQ1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 102 ≤ 1 / 2 ^ 101)]
  have hF1 : |value F.1.toBits| ≤ 1 / 8 + 1 / 2 ^ 51 := by
    have h1 : |Pw| ≤ 1 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (value F.1.toBits + value F.2.toBits) Pw
    have h3 := abs_sub_abs_le_abs_sub (value F.1.toBits) (value F.1.toBits + value F.2.toBits)
    rw [show value F.1.toBits - (value F.1.toBits + value F.2.toBits) = -value F.2.toBits by ring,
      abs_neg] at h3
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 52 ≤ 1 / 2 ^ 51)]
  have hF2 : |value F.2.toBits| ≤ 1 / 2 ^ 52 := by linarith
  have hFsum : |value F.1.toBits + value F.2.toBits| ≤ 1 / 8 + 1 / 2 ^ 105 := by
    have h1 : |Pw| ≤ 1 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 := abs_sub_abs_le_abs_sub (value F.1.toBits + value F.2.toBits) Pw
    linarith
  -- `G = z F`
  have hc1 : (0 : ℝ) ≤ 1 / 8 + 1 / 2 ^ 51 := by norm_num
  obtain ⟨g1f, g2f, ge, g2b, g1b⟩ := mulDD_spec hF zh zl F.1 F.2 hzh hzl f1f f2f
    ((1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52))) ((1 / 8 + 1 / 2 ^ 51) * (R / 2 ^ 49))
    (1 / 2 ^ 52 * (R * (1 + 1 / 2 ^ 52))) (1 / 2 ^ 52 * (R / 2 ^ 49))
    (mul_le_mul hF1 hab (abs_nonneg _) hc1) (mul_le_mul hF1 hz2 (abs_nonneg _) hc1)
    (mul_le_mul hF2 hab (abs_nonneg _) (by norm_num))
    (mul_le_mul hF2 hz2 (abs_nonneg _) (by norm_num)) (by nlinarith) (by nlinarith)
  rw [show mulDD zh zl F.1 F.2 = G from rfl] at g1f g2f ge g2b g1b
  rw [← ha, ← hb] at ge
  have hRη : (1 : ℝ) / 2 ^ 1070 ≤ R / 2 ^ 900 := by
    have := div_le_div_of_nonneg_right hR (by positivity : (0 : ℝ) ≤ 2 ^ 900)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 120 / 2 ^ 900)]
  refine ⟨g1f, g2f, ?_, ?_, ?_⟩
  · -- `(a + b) F - Z P(Z²) = (a + b - Z) F + Z (F - P(Z²))`
    have hid : (a + b) * (value F.1.toBits + value F.2.toBits) - Z * PZ =
        (a + b - Z) * (value F.1.toBits + value F.2.toBits) +
          Z * (value F.1.toBits + value F.2.toBits - PZ) := by ring
    have e1 : |(a + b - Z) * (value F.1.toBits + value F.2.toBits)| ≤
        R / 2 ^ 98 * (1 / 8 + 1 / 2 ^ 105) := by
      rw [abs_mul]; exact mul_le_mul hz3 hFsum (abs_nonneg _) (div_nonneg hR0.le (by norm_num))
    have e2 : |Z * (value F.1.toBits + value F.2.toBits - PZ)| ≤
        R * (1 + 1 / 2 ^ 48) * (1 / 2 ^ 101) := by
      rw [abs_mul, abs_of_nonneg hZ0]
      exact mul_le_mul hZhi hFP (abs_nonneg _) (mul_nonneg hR0.le (by norm_num))
    have h1 := abs_add_le (value G.1.toBits + value G.2.toBits -
      (a + b) * (value F.1.toBits + value F.2.toBits))
      ((a + b) * (value F.1.toBits + value F.2.toBits) - Z * PZ)
    rw [show value G.1.toBits + value G.2.toBits - (a + b) * (value F.1.toBits + value F.2.toBits) +
      ((a + b) * (value F.1.toBits + value F.2.toBits) - Z * PZ) =
        value G.1.toBits + value G.2.toBits - Z * PZ by ring, hid] at h1
    have h2 := abs_add_le ((a + b - Z) * (value F.1.toBits + value F.2.toBits))
      (Z * (value F.1.toBits + value F.2.toBits - PZ))
    have h3 : 1 / 2 ^ 52 * (R / 2 ^ 49) + (4 * ((1 / 8 + 1 / 2 ^ 51) * (R / 2 ^ 49) +
        1 / 2 ^ 52 * (R * (1 + 1 / 2 ^ 52))) + (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) /
          2 ^ 51) / 2 ^ 53 + R / 2 ^ 900 + R / 2 ^ 98 * (1 / 8 + 1 / 2 ^ 105) +
        R * (1 + 1 / 2 ^ 48) * (1 / 2 ^ 101) ≤ R / 2 ^ 99 := by
      have : 1 / 2 ^ 52 * (R / 2 ^ 49) + (4 * ((1 / 8 + 1 / 2 ^ 51) * (R / 2 ^ 49) +
          1 / 2 ^ 52 * (R * (1 + 1 / 2 ^ 52))) + (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) /
            2 ^ 51) / 2 ^ 53 + R / 2 ^ 900 + R / 2 ^ 98 * (1 / 8 + 1 / 2 ^ 105) +
          R * (1 + 1 / 2 ^ 48) * (1 / 2 ^ 101) =
          R * (1 / 2 ^ 52 / 2 ^ 49 + (4 * ((1 / 8 + 1 / 2 ^ 51) / 2 ^ 49 +
            1 / 2 ^ 52 * (1 + 1 / 2 ^ 52)) + (1 / 8 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 52) / 2 ^ 51) /
              2 ^ 53 + 1 / 2 ^ 900 + 1 / 2 ^ 98 * (1 / 8 + 1 / 2 ^ 105) +
            (1 + 1 / 2 ^ 48) * (1 / 2 ^ 101)) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 52 / 2 ^ 49 +
        (4 * ((1 / 8 + 1 / 2 ^ 51) / 2 ^ 49 + 1 / 2 ^ 52 * (1 + 1 / 2 ^ 52)) +
          (1 / 8 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 52) / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 900 +
          1 / 2 ^ 98 * (1 / 8 + 1 / 2 ^ 105) + (1 + 1 / 2 ^ 48) * (1 / 2 ^ 101) ≤ 1 / 2 ^ 99)
        hR0.le
      linarith [(by ring : R * (1 / 2 ^ 99) = R / 2 ^ 99)]
    linarith
  · have : (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        R / 7 := by
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 900 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1070)]
      have : (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) * (1 + 1 / 2 ^ 53) + R / 2 ^ 900 =
          R * ((1 / 8 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 900) := by ring
      have h6 := mul_le_mul_of_nonneg_left (by norm_num : (1 / 8 + 1 / 2 ^ 51 : ℝ) *
        (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 900 ≤ 1 / 7) hR0.le
      linarith [(by ring : R * (1 / 7) = R / 7)]
    linarith
  · have : ((1 / 8 + 1 / 2 ^ 51) * (R / 2 ^ 49) + 1 / 2 ^ 52 * (R * (1 + 1 / 2 ^ 52))) *
        (1 + 1 / 2 ^ 50) + (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 52 + 1 / 2 ^ 1070 ≤
        R / 2 ^ 50 := by
      have : ((1 / 8 + 1 / 2 ^ 51) * (R / 2 ^ 49) + 1 / 2 ^ 52 * (R * (1 + 1 / 2 ^ 52))) *
          (1 + 1 / 2 ^ 50) + (1 / 8 + 1 / 2 ^ 51) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 52 + R / 2 ^ 900 =
          R * (((1 / 8 + 1 / 2 ^ 51) / 2 ^ 49 + 1 / 2 ^ 52 * (1 + 1 / 2 ^ 52)) * (1 + 1 / 2 ^ 50) +
            (1 / 8 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 52) / 2 ^ 52 + 1 / 2 ^ 900) := by ring
      have h6 := mul_le_mul_of_nonneg_left (by norm_num : ((1 / 8 + 1 / 2 ^ 51 : ℝ) / 2 ^ 49 +
        1 / 2 ^ 52 * (1 + 1 / 2 ^ 52)) * (1 + 1 / 2 ^ 50) +
          (1 / 8 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 52) / 2 ^ 52 + 1 / 2 ^ 900 ≤ 1 / 2 ^ 50) hR0.le
      linarith [(by ring : R * (1 / 2 ^ 50) = R / 2 ^ 50)]
    linarith

#print axioms series_gen

end Verified.Examples.LgammaAsymSeries
