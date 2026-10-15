import Verified.Examples.LgammaReflCore
import Verified.Examples.GammaPi
import LeanExe.ProofKit.RatExpLog

/-!
Enclosures of `ln |Γ v|` at the 14 ends `v = ±(2k + 1)/4`, `k < 7`, of the windows of the accurate
path of `Lgamma`, each of width below `4 · 10^-21`.  `AccPolyFact` puts `ln Γ` at 3/4, 5/4, and
7/4 within `2^-72`, `2^-72`, and `2^-70` of the accurate path's polynomials, whose values the kernel
computes (`g3`, `g5`, `g7`).  The recurrence `ln Γ (v + 1) = ln Γ v + ln v` and, below 0, the
reflection formula with `sin (π/4) = sin (3π/4) = √2/2` (`refl_quarter`) reduce the other ends
to these three values and to `ln 2`, `ln (3/2)`, `ln (5/4)`, `ln (7/4)`, `ln (11/8)`, `ln (13/8)`,
and `ln (π/2)`.  `RatExpLog` bounds each logarithm within `10^-39` by Taylor sums of `exp` with 40
terms, through `GammaPi.pi_bounds128` for `ln (π/2)`.
-/

namespace Verified.Examples.LgammaEndEncl
open Real LeanExe.ProofKit RatExpLog GammaBasic

set_option exponentiation.threshold 4096

/-! ### Logarithms -/

/-- Rational bounds on `log a` from Taylor sums of `exp` with 40 terms. -/
theorem log_encl (a lo hi : ℚ) (ha : 0 < a) (hlo : |lo| ≤ 1) (hhi : |hi| ≤ 1)
    (h1 : expSum lo 40 + expRem 40 ≤ a) (h2 : a ≤ expSum hi 40 - expRem 40) :
    (lo : ℝ) ≤ log a ∧ log a ≤ hi :=
  ⟨le_log a lo 40 (by norm_num) hlo h1, log_le a hi 40 (by norm_num) hhi ha h2⟩

theorem l2 :
    (6931471805599453094172321214581765680754 / 10 ^ 40 : ℝ) ≤ log 2 ∧
      log 2 ≤ (6931471805599453094172321214581765680757 / 10 ^ 40 : ℝ) := by
  have h := log_encl 2
    (6931471805599453094172321214581765680754 / 10 ^ 40 : ℚ)
    (6931471805599453094172321214581765680757 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem m3 :
    (4054651081081643819780131154643491365718 / 10 ^ 40 : ℝ) ≤ log (3 / 2) ∧
      log (3 / 2) ≤ (4054651081081643819780131154643491365721 / 10 ^ 40 : ℝ) := by
  have h := log_encl (3 / 2)
    (4054651081081643819780131154643491365718 / 10 ^ 40 : ℚ)
    (4054651081081643819780131154643491365721 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem m5 :
    (2231435513142097557662950903098345033745 / 10 ^ 40 : ℝ) ≤ log (5 / 4) ∧
      log (5 / 4) ≤ (2231435513142097557662950903098345033748 / 10 ^ 40 : ℝ) := by
  have h := log_encl (5 / 4)
    (2231435513142097557662950903098345033745 / 10 ^ 40 : ℚ)
    (2231435513142097557662950903098345033748 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem m7 :
    (5596157879354226862708885005268265934859 / 10 ^ 40 : ℝ) ≤ log (7 / 4) ∧
      log (7 / 4) ≤ (5596157879354226862708885005268265934862 / 10 ^ 40 : ℝ) := by
  have h := log_encl (7 / 4)
    (5596157879354226862708885005268265934859 / 10 ^ 40 : ℚ)
    (5596157879354226862708885005268265934862 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem m11 :
    (3184537311185346158102472135905995955951 / 10 ^ 40 : ℝ) ≤ log (11 / 8) ∧
      log (11 / 8) ≤ (3184537311185346158102472135905995955954 / 10 ^ 40 : ℝ) := by
  have h := log_encl (11 / 8)
    (3184537311185346158102472135905995955951 / 10 ^ 40 : ℚ)
    (3184537311185346158102472135905995955954 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem m13 :
    (4855078157817008078017910771907889005786 / 10 ^ 40 : ℝ) ≤ log (13 / 8) ∧
      log (13 / 8) ≤ (4855078157817008078017910771907889005789 / 10 ^ 40 : ℝ) := by
  have h := log_encl (13 / 8)
    (4855078157817008078017910771907889005786 / 10 ^ 40 : ℚ)
    (4855078157817008078017910771907889005789 / 10 ^ 40 : ℚ)
    (by norm_num) (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

theorem mp :
    (4515827052894548647261952298948821435710 / 10 ^ 40 : ℝ) ≤ log (π / 2) ∧
      log (π / 2) ≤ (4515827052894548647261952298948821435723 / 10 ^ 40 : ℝ) := by
  have hlo := le_log (GammaPi.piLo128 / 2)
    (4515827052894548647261952298948821435710 / 10 ^ 40 : ℚ)
    40 (by norm_num) (by rw [abs_le]; norm_num) (by decide +kernel)
  have hhi := log_le (GammaPi.piHi128 / 2)
    (4515827052894548647261952298948821435723 / 10 ^ 40 : ℚ)
    40 (by norm_num) (by rw [abs_le]; norm_num) (by decide +kernel) (by decide +kernel)
  obtain ⟨p1, p2⟩ := GammaPi.pi_bounds128
  have h0 : (0 : ℝ) < GammaPi.piLo128 := by
    have : (0 : ℚ) < GammaPi.piLo128 := by decide +kernel
    exact_mod_cast this
  have e1 : log ((GammaPi.piLo128 / 2 : ℚ) : ℝ) ≤ log (π / 2) :=
    Real.log_le_log (by push_cast; positivity) (by push_cast; linarith)
  have e2 : log (π / 2) ≤ log ((GammaPi.piHi128 / 2 : ℚ) : ℝ) :=
    Real.log_le_log (by linarith [Real.pi_pos]) (by push_cast; linarith)
  push_cast at hlo hhi e1 e2
  exact ⟨hlo.trans e1, e2.trans hhi⟩

theorem log_quarter : log (1 / 4) = -(2 * log 2) := by
  rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem log_9_4 : log (9 / 4) = 2 * log (3 / 2) := by
  rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem log_3_4 : log (3 / 4) = log (3 / 2) - log 2 := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  norm_num

theorem log_11_4 : log (11 / 4) = log (11 / 8) + log 2 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log_13_4 : log (13 / 4) = log (13 / 8) + log 2 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

/-! ### `ln Γ` at 3/4, 5/4, and 7/4 -/

theorem poly_encl (g P c e1 e2 : ℝ) (h1 : |g - P| ≤ e1) (h2 : |P - c| ≤ e2) :
    |g - c| ≤ e1 + e2 := by
  have := abs_sub_le g P c
  linarith

theorem g3 (hAP : LgammaApprox.AccPolyFact) :
    |lgamma (3 / 4) -
        (2032809514312953714814329718624296997597 / 10 ^ 40 : ℝ)| ≤
      2 * (1 / 2 ^ 72 + 1 / 10 ^ 40) := by
  have h := hAP.1 (-1 / 4) (by rw [abs_le]; norm_num)
  have hk : |(-1 / 4 : ℚ) * qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (-1 / 4) -
      (2032809514312953714814329718624296997597 / 10 ^ 40 : ℚ)| ≤
      1 / 2 ^ 72 + 1 / 10 ^ 40 := by decide +kernel
  have hq : LgammaApprox.accSmallPoly (-1 / 4) =
      ((qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (-1 / 4) : ℚ) : ℝ) := by
    rw [qeval_cast]
    push_cast
    rfl
  generalize qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (-1 / 4) = P at hk hq
  have hk' : ((|(-1 / 4 : ℚ) * P -
      (2032809514312953714814329718624296997597 / 10 ^ 40 : ℚ)| : ℚ) : ℝ) ≤
      ((1 / 2 ^ 72 + 1 / 10 ^ 40 : ℚ) : ℝ) := Rat.cast_le.mpr hk
  push_cast at hk'
  rw [hq, show (1 : ℝ) + -1 / 4 = 3 / 4 by norm_num] at h
  have a := abs_le.mp h
  have b := abs_le.mp hk'
  rw [show (1 : ℝ) / 2 ^ 70 * |-1 / 4| = 1 / 2 ^ 72 by
    rw [abs_of_neg (by norm_num)]; norm_num] at a
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

theorem g5 (hAP : LgammaApprox.AccPolyFact) :
    |lgamma (5 / 4) -
        (-982718364218131614638538026966358402256 / 10 ^ 40 : ℝ)| ≤
      2 * (1 / 2 ^ 72 + 1 / 10 ^ 40) := by
  have h := hAP.1 (1 / 4) (by rw [abs_le]; norm_num)
  have hk : |(1 / 4 : ℚ) * qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (1 / 4) -
      (-982718364218131614638538026966358402256 / 10 ^ 40 : ℚ)| ≤
      1 / 2 ^ 72 + 1 / 10 ^ 40 := by decide +kernel
  have hq : LgammaApprox.accSmallPoly (1 / 4) =
      ((qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (1 / 4) : ℚ) : ℝ) := by
    rw [qeval_cast]
    push_cast
    rfl
  generalize qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) (1 / 4) = P at hk hq
  have hk' : ((|(1 / 4 : ℚ) * P -
      (-982718364218131614638538026966358402256 / 10 ^ 40 : ℚ)| : ℚ) : ℝ) ≤
      ((1 / 2 ^ 72 + 1 / 10 ^ 40 : ℚ) : ℝ) := Rat.cast_le.mpr hk
  push_cast at hk'
  rw [hq, show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num] at h
  have a := abs_le.mp h
  have b := abs_le.mp hk'
  rw [show (1 : ℝ) / 2 ^ 70 * |1 / 4| = 1 / 2 ^ 72 by
    rw [abs_of_pos (by norm_num)]; norm_num] at a
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

theorem g7 (hAP : LgammaApprox.AccPolyFact) :
    |lgamma (7 / 4) -
        (-844011210204855559577860341313977317438 / 10 ^ 40 : ℝ)| ≤
      2 * (1 / 2 ^ 70 + 1 / 10 ^ 40) := by
  have h := hAP.2 (1 / 4) (by rw [abs_le]; norm_num)
  have hk : |qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (1 / 4) -
      (-844011210204855559577860341313977317438 / 10 ^ 40 : ℚ)| ≤
      1 / 2 ^ 70 + 1 / 10 ^ 40 := by decide +kernel
  have hq : LgammaApprox.accMidPoly (1 / 4) =
      ((qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (1 / 4) : ℚ) : ℝ) := by
    rw [qeval_cast]
    push_cast
    rfl
  generalize qeval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) (1 / 4) = P at hk hq
  have hk' : ((|P -
      (-844011210204855559577860341313977317438 / 10 ^ 40 : ℚ)| : ℚ) : ℝ) ≤
      ((1 / 2 ^ 70 + 1 / 10 ^ 40 : ℚ) : ℝ) := Rat.cast_le.mpr hk
  push_cast at hk'
  rw [hq, show (3 / 2 : ℝ) + 1 / 4 = 7 / 4 by norm_num] at h
  have a := abs_le.mp h
  have b := abs_le.mp hk'
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

theorem lg_add (x : ℝ) (hx : 0 < x) : lgamma (x + 1) = lgamma x + log x :=
  lgamma_add_one (notPole_of_neg_one_lt (by linarith) hx.ne')

theorem noint (v : ℝ) (m : ℤ) (h : 4 * v = m) (hm : m % 4 ≠ 0) : ∀ n : ℤ, v ≠ n := by
  intro n hn
  rw [hn] at h
  have : 4 * n = m := by exact_mod_cast h
  omega

theorem sin_q1 : Real.sin (π * (1 / 4)) = √2 / 2 := by
  rw [show π * (1 / 4) = π / 4 by ring, Real.sin_pi_div_four]

theorem sin_q3 : Real.sin (π * (3 / 4)) = √2 / 2 := by
  rw [show π * (3 / 4) = π - π / 4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four]

/-- **The reflection at a quarter**: `ln |Γ v|` for a negative `v` whose fractional part is `1/4`
or `3/4`. -/
theorem refl_quarter (v : ℝ) (hv : v < 0) (hint : ∀ n : ℤ, v ≠ n)
    (hs : Real.sin (π * Int.fract v) = √2 / 2) :
    lgamma v = -(lgamma (-v) + log (-v)) + 3 / 2 * log 2 + log (π / 2) := by
  have h := LgammaReflCore.refl_L v hv hint
  rw [hs] at h
  have hpi := Real.pi_pos
  have ha : 0 < -v := by linarith
  have hs2 : (0 : ℝ) < √2 / 2 := by positivity
  have hsq : log (√2 / 2) = -(log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  have hm : log (-v * (√2 / 2 / π)) = log (-v) + log (√2 / 2) - log π := by
    rw [Real.log_mul ha.ne' (by positivity), Real.log_div hs2.ne' hpi.ne']
    ring
  have hp : log π = log (π / 2) + log 2 := by
    rw [Real.log_div hpi.ne' (by norm_num)]
    ring
  show log (Gamma v) = _
  rw [h, hm, hsq, hp]
  ring

theorem fract_eq (v f : ℝ) (n : ℤ) (h : v = n + f) (h0 : 0 ≤ f) (h1 : f < 1) :
    Int.fract v = f :=
  Int.fract_eq_iff.mpr ⟨h0, h1, n, by rw [h]; ring⟩

theorem refl_q1 (v : ℝ) (n : ℤ) (hv : v < 0) (h : v = n + 1 / 4) :
    lgamma v = -(lgamma (-v) + log (-v)) + 3 / 2 * log 2 + log (π / 2) := by
  refine refl_quarter v hv (noint v (4 * n + 1) (by rw [h]; push_cast; ring) (by omega)) ?_
  rw [fract_eq v (1 / 4) n h (by norm_num) (by norm_num), sin_q1]

theorem refl_q3 (v : ℝ) (n : ℤ) (hv : v < 0) (h : v = n + 3 / 4) :
    lgamma v = -(lgamma (-v) + log (-v)) + 3 / 2 * log 2 + log (π / 2) := by
  refine refl_quarter v hv (noint v (4 * n + 3) (by rw [h]; push_cast; ring) (by omega)) ?_
  rw [fract_eq v (3 / 4) n h (by norm_num) (by norm_num), sin_q3]

/-! ### The 14 ends -/

theorem e_p1 (hAP : LgammaApprox.AccPolyFact) :
    (12880225246980774573701869237460901457553 / 10 ^ 40 : ℝ) ≤ lgamma (1 / 4) ∧
      lgamma (1 / 4) ≤ (12880225246980774573710339566933444460957 / 10 ^ 40 : ℝ) := by
  have e := lg_add (1 / 4) (by norm_num)
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num, log_quarter] at e
  obtain ⟨a1, a2⟩ := l2
  have hg := abs_le.mp (g5 hAP)
  constructor <;> linarith

theorem e_n1 (hAP : LgammaApprox.AccPolyFact) :
    (15895753125511859903154736983051556857406 / 10 ^ 40 : ℝ) ≤ lgamma (-1 / 4) ∧
      lgamma (-1 / 4) ≤ (15895753125511859903163207312524099860810 / 10 ^ 40 : ℝ) := by
  have e := lgamma_add_one (x := -1 / 4) (notPole_of_neg_one_lt (by norm_num) (by norm_num))
  rw [show (-1 / 4 : ℝ) + 1 = 3 / 4 by norm_num, show (-1 / 4 : ℝ) = -(1 / 4) by norm_num,
    Real.log_neg_eq_log, log_quarter] at e
  rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num]
  obtain ⟨a1, a2⟩ := l2
  have hg := abs_le.mp (g3 hAP)
  constructor <;> linarith

theorem e_p3 (hAP : LgammaApprox.AccPolyFact) :
    (2032809514312953714810094553888025495898 / 10 ^ 40 : ℝ) ≤ lgamma (3 / 4) ∧
      lgamma (3 / 4) ≤ (2032809514312953714818564883360568499296 / 10 ^ 40 : ℝ) := by
  have hg := abs_le.mp (g3 hAP)
  constructor <;> linarith

theorem e_p5 (hAP : LgammaApprox.AccPolyFact) :
    (-982718364218131614642773191702629903955 / 10 ^ 40 : ℝ) ≤ lgamma (5 / 4) ∧
      lgamma (5 / 4) ≤ (-982718364218131614634302862230086900557 / 10 ^ 40 : ℝ) := by
  have hg := abs_le.mp (g5 hAP)
  constructor <;> linarith

theorem e_p7 (hAP : LgammaApprox.AccPolyFact) :
    (-844011210204855559594801000259063324223 / 10 ^ 40 : ℝ) ≤ lgamma (7 / 4) ∧
      lgamma (7 / 4) ≤ (-844011210204855559560919682368891310653 / 10 ^ 40 : ℝ) := by
  have hg := abs_le.mp (g7 hAP)
  constructor <;> linarith

theorem lg9 : lgamma (9 / 4) = lgamma (5 / 4) + log (5 / 4) := by
  rw [← lg_add (5 / 4) (by norm_num)]
  norm_num

theorem lg11 : lgamma (11 / 4) = lgamma (7 / 4) + log (7 / 4) := by
  rw [← lg_add (7 / 4) (by norm_num)]
  norm_num

theorem lg13 : lgamma (13 / 4) = lgamma (9 / 4) + log (9 / 4) := by
  rw [← lg_add (9 / 4) (by norm_num)]
  norm_num

theorem e_p9 (hAP : LgammaApprox.AccPolyFact) :
    (1248717148923965943020177711395715129790 / 10 ^ 40 : ℝ) ≤ lgamma (9 / 4) ∧
      lgamma (9 / 4) ≤ (1248717148923965943028648040868258133191 / 10 ^ 40 : ℝ) := by
  rw [lg9]
  have hg := abs_le.mp (g5 hAP)
  obtain ⟨b1, b2⟩ := m5
  constructor <;> linarith

theorem e_p11 (hAP : LgammaApprox.AccPolyFact) :
    (4752146669149371303114084005009202610636 / 10 ^ 40 : ℝ) ≤ lgamma (11 / 4) ∧
      lgamma (11 / 4) ≤ (4752146669149371303147965322899374624209 / 10 ^ 40 : ℝ) := by
  rw [lg11]
  have hg := abs_le.mp (g7 hAP)
  obtain ⟨b1, b2⟩ := m7
  constructor <;> linarith

theorem e_p13 (hAP : LgammaApprox.AccPolyFact) :
    (9358019311087253582580440020682697861226 / 10 ^ 40 : ℝ) ≤ lgamma (13 / 4) ∧
      lgamma (13 / 4) ≤ (9358019311087253582588910350155240864633 / 10 ^ 40 : ℝ) := by
  rw [lg13, lg9, log_9_4]
  have hg := abs_le.mp (g5 hAP)
  obtain ⟨b1, b2⟩ := m5
  obtain ⟨c1, c2⟩ := m3
  constructor <;> linarith

theorem e_n3 (hAP : LgammaApprox.AccPolyFact) :
    (15757045971498583848094059297399175772578 / 10 ^ 40 : ℝ) ≤ lgamma (-3 / 4) ∧
      lgamma (-3 / 4) ≤ (15757045971498583848102529626871718775999 / 10 ^ 40 : ℝ) := by
  rw [refl_q1 (-3 / 4) (-1) (by norm_num) (by norm_num), show -(-3 / 4 : ℝ) = 3 / 4 by norm_num,
    log_3_4]
  have hg := abs_le.mp (g3 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨c1, c2⟩ := m3
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

theorem e_n5 (hAP : LgammaApprox.AccPolyFact) :
    (13664317612369762345491786079953211823650 / 10 ^ 40 : ℝ) ≤ lgamma (-5 / 4) ∧
      lgamma (-5 / 4) ≤ (13664317612369762345500256409425754827068 / 10 ^ 40 : ℝ) := by
  rw [refl_q3 (-5 / 4) (-2) (by norm_num) (by norm_num), show -(-5 / 4 : ℝ) = 5 / 4 by norm_num]
  have hg := abs_le.mp (g5 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨b1, b2⟩ := m5
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

theorem e_n7 (hAP : LgammaApprox.AccPolyFact) :
    (10160888092144356985372468797922095332632 / 10 ^ 40 : ℝ) ≤ lgamma (-7 / 4) ∧
      lgamma (-7 / 4) ≤ (10160888092144356985406350115812267346222 / 10 ^ 40 : ℝ) := by
  rw [refl_q1 (-7 / 4) (-2) (by norm_num) (by norm_num), show -(-7 / 4 : ℝ) = 7 / 4 by norm_num]
  have hg := abs_le.mp (g7 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨b1, b2⟩ := m7
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

theorem e_n9 (hAP : LgammaApprox.AccPolyFact) :
    (5555015450206474705931523770666229092208 / 10 ^ 40 : ℝ) ≤ lgamma (-9 / 4) ∧
      lgamma (-9 / 4) ≤ (5555015450206474705939994100138772095632 / 10 ^ 40 : ℝ) := by
  rw [refl_q3 (-9 / 4) (-3) (by norm_num) (by norm_num), show -(-9 / 4 : ℝ) = 9 / 4 by norm_num,
    lg9, log_9_4]
  have hg := abs_le.mp (g5 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨b1, b2⟩ := m5
  obtain ⟨c1, c2⟩ := m3
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

theorem e_n11 (hAP : LgammaApprox.AccPolyFact) :
    (44878975359557733097675447434333695924 / 10 ^ 40 : ℝ) ≤ lgamma (-11 / 4) ∧
      lgamma (-11 / 4) ≤ (44878975359557733131556765324505709514 / 10 ^ 40 : ℝ) := by
  rw [refl_q1 (-11 / 4) (-3) (by norm_num) (by norm_num),
    show -(-11 / 4 : ℝ) = 11 / 4 by norm_num, lg11, log_11_4]
  have hg := abs_le.mp (g7 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨b1, b2⟩ := m7
  obtain ⟨c1, c2⟩ := m11
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

theorem e_n13 (hAP : LgammaApprox.AccPolyFact) :
    (-6231534513209986466258708215823425594335 / 10 ^ 40 : ℝ) ≤ lgamma (-13 / 4) ∧
      lgamma (-13 / 4) ≤ (-6231534513209986466250237886350882590911 / 10 ^ 40 : ℝ) := by
  rw [refl_q3 (-13 / 4) (-4) (by norm_num) (by norm_num),
    show -(-13 / 4 : ℝ) = 13 / 4 by norm_num, lg13, lg9, log_9_4, log_13_4]
  have hg := abs_le.mp (g5 hAP)
  obtain ⟨a1, a2⟩ := l2
  obtain ⟨b1, b2⟩ := m5
  obtain ⟨c1, c2⟩ := m3
  obtain ⟨e1, e2⟩ := m13
  obtain ⟨d1, d2⟩ := mp
  constructor <;> linarith

#print axioms mp
#print axioms g3
#print axioms g5
#print axioms g7
#print axioms e_p1
#print axioms e_n1
#print axioms e_p13
#print axioms e_n11
#print axioms e_n13

end Verified.Examples.LgammaEndEncl
