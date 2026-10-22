import LeanExe.ProofKit.Bessel
import LeanExe.ProofKit.EulerGamma
import LeanExe.ProofKit.PolyChecks
import LeanExe.ProofKit.F64Approx
import Mathlib.Analysis.Real.Pi.Bounds

/-!
fdlibm's rational approximations below 2 against the series of `LeanExe.ProofKit.Bessel`, in
`ζ = x²/4`, where fdlibm's argument is `z = x² = 4ζ` (`sc4`).  With `N = 18` terms of each
series, the remainders are below `2 ^ -99`, and one kernel check (`PolyBound.check`) per function
bounds the polynomial `S (A - ...) - R` whose quotient by `S ≥ 1` is the approximation error:

* `j0_approx`: `|J₀ x - (1 - z/4 + z² R(z)/S(z))| ≤ 0.12 u + 2^-99` for `|x| ≤ 2`;
* `j1_approx`: `|J₁ x - (x/2 + x z R(z)/S(z))| ≤ |x| (0.005 u + 2^-99)`;
* `y0_approx`: `|Y₀ x - (2/π) J₀ x ln x - U(z)/V(z)| ≤ 0.21 u + 2^-60` for `0 < x ≤ 2`;
* `y1_approx`: `|Y₁ x - (2/π)(J₁ x ln x - 1/x) - x U(z)/V(z)| ≤ x (0.155 u + 2^-60)`;

with `u = 2 ^ -53`.  The second-kind forms use `Y0_sub_log` and `Y1_sub_log`, and the constants
`(2/π)(γ - ln 2)` and `2/π` within `2^-64` of 30-digit rationals, from Mathlib's 20-digit bounds
on `π` and `EulerGamma`'s enclosures of `γ` and `ln 2`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallApprox
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

/-- The coefficients of `p (4 ζ)`. -/
def sc4 : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: scaleP 4 (sc4 p)

theorem eval_sc4 (p : List ℚ) (ζ : ℝ) : eval (sc4 p) ζ = eval p (4 * ζ) := by
  induction p with
  | nil => simp [sc4]
  | cons a p ih =>
    simp only [sc4, eval_cons, eval_scaleP, ih]
    push_cast
    ring

/-! fdlibm's coefficients. -/

def R0 : List ℚ := [ratOfWord 0x3F8FFFFFFFFFFFFD, ratOfWord 0xBF28E6A5B61AC6E9,
  ratOfWord 0x3EBEB1D10C503919, ratOfWord 0xBE33D5E773D63FCE]
def S0 : List ℚ := [1, ratOfWord 0x3F8FFCE882C8C2A4, ratOfWord 0x3F1EA6D2DD57DBF4,
  ratOfWord 0x3EA13B54CE84D5A9, ratOfWord 0x3E1408BCF4745D8F]
def R1 : List ℚ := [ratOfWord 0xBFB0000000000000, ratOfWord 0x3F570D9F98472C61,
  ratOfWord 0xBEF0C5C6BA169668, ratOfWord 0x3E6AAAFA46CA0BD9]
def S1 : List ℚ := [1, ratOfWord 0x3F939D0B12637E53, ratOfWord 0x3F285F56B9CDF664,
  ratOfWord 0x3EB3BFF8333F8498, ratOfWord 0x3E35AC88C97DFF2C, ratOfWord 0x3DAB2ACFCFB97ED8]
def U0 : List ℚ := [ratOfWord 0xBFB2E4D699CBD01F, ratOfWord 0x3FC69D019DE9E3FC,
  ratOfWord 0xBF8C4CE8B16CFA97, ratOfWord 0x3F36C54D20B29B6B, ratOfWord 0xBECFFEA773D25CAD,
  ratOfWord 0x3E5500573B4EABD4, ratOfWord 0xBDC5E43D693FB3C8]
def V0 : List ℚ := [1, ratOfWord 0x3F8A127091C9C71A, ratOfWord 0x3F13ECBBF578C6C1,
  ratOfWord 0x3E91642D7FF202FD, ratOfWord 0x3DFE50183BD6D9EF]
def U1 : List ℚ := [ratOfWord 0xBFC91866143CBC8A, ratOfWord 0x3FA9D3C776292CD1,
  ratOfWord 0xBF5F55E54844F50F, ratOfWord 0x3EF8AB038FA6B88E, ratOfWord 0xBE78AC00569105B8]
def V1 : List ℚ := [1, ratOfWord 0x3F94650D3F4DA9F0, ratOfWord 0x3F2A8C896C257764,
  ratOfWord 0x3EB6C05A894E8CA6, ratOfWord 0x3E3ABF1D5BA69A86, ratOfWord 0x3DB25039DACA772A]

/-- `2/π` and `(2/π)(γ - ln 2)` to 30 digits. -/
def κ2 : ℚ := 636619772367581343075535053490 / 10 ^ 30
def κ1 : ℚ := -73804295108687225274343927948 / 10 ^ 30

/-- The comparison polynomials in `ζ`. -/
def E0 : List ℚ := subP (mulP (sc4 S0) (subP (a0List 18) [1, -1])) (mulP [0, 0, 16] (sc4 R0))
def E1 : List ℚ := subP (mulP (sc4 S1) (subP (scaleP (1 / 2) (a1List 18)) [1 / 2]))
  (mulP [0, 4] (sc4 R1))
def E2 : List ℚ := subP (sc4 U0) (mulP (sc4 V0) (addP (scaleP κ1 (a0List 18)) (scaleP κ2 (c0List 18))))
def E3 : List ℚ := subP (sc4 U1) (mulP (sc4 V1)
  (subP (scaleP (κ1 / 2) (a1List 18)) (scaleP (κ2 / 4) (c1List 18))))

theorem checks :
    check E0 0 1 (12 / 100 / 2 ^ 53) 4 = true ∧ check E1 0 1 (5 / 1000 / 2 ^ 53) 5 = true ∧
      check E2 0 1 (21 / 100 / 2 ^ 53) 3 = true ∧ check E3 0 1 (155 / 1000 / 2 ^ 53) 3 = true := by
  decide +kernel

theorem signs :
    S0.tail.all (fun c => !decide (c < 0)) = true ∧ S1.tail.all (fun c => !decide (c < 0)) = true ∧
      V0.tail.all (fun c => !decide (c < 0)) = true ∧
      V1.tail.all (fun c => !decide (c < 0)) = true := by
  decide +kernel

theorem nonneg_of_all (l : List ℚ) (h : l.all (fun c => !decide (c < 0)) = true) :
    ∀ c ∈ l, 0 ≤ c := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at this
  exact this

theorem coeff_facts :
    (∀ c ∈ S0.tail, 0 ≤ c) ∧ (∀ c ∈ S1.tail, 0 ≤ c) ∧ (∀ c ∈ V0.tail, 0 ≤ c) ∧
      (∀ c ∈ V1.tail, 0 ≤ c) ∧ qabs (qa0 18) ≤ 1 / 2 ^ 100 ∧ qabs (qa1 18) ≤ 1 / 2 ^ 100 ∧
      qabs (qc0 18) ≤ 1 / 2 ^ 100 ∧ qabs (qc1 18) ≤ 1 / 2 ^ 100 ∧ qa0 0 = 1 ∧ qa0 1 = -1 ∧
      qabs (qa0 2) = 1 / 4 ∧ qa1 0 = 1 ∧ qabs (qa1 1) = 1 / 2 ∧ qc0 0 = 0 ∧ qabs (qc0 1) = 1 ∧
      qc1 0 = 1 ∧ qabs (qc1 1) = 5 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := signs
  refine ⟨nonneg_of_all _ h1, nonneg_of_all _ h2, nonneg_of_all _ h3, nonneg_of_all _ h4, ?_⟩
  decide +kernel

theorem eval_nonneg' (p : List ℚ) (hp : ∀ c ∈ p, 0 ≤ c) (z : ℝ) (hz : 0 ≤ z) : 0 ≤ eval p z := by
  induction p with
  | nil => simp
  | cons a q ih =>
    rw [eval_cons]
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hp a (by simp)
    have hq := ih (fun c hc => hp c (by simp [hc]))
    positivity

/-- A list `1 :: T` with nonnegative tail is at least 1 at `z ≥ 0`. -/
theorem one_le_eval (S : List ℚ) (hS : S = 1 :: S.tail) (ht : ∀ c ∈ S.tail, 0 ≤ c) (z : ℝ)
    (hz : 0 ≤ z) : 1 ≤ eval S z := by
  rw [hS, eval_cons]
  have := eval_nonneg' _ ht z hz
  push_cast
  nlinarith

/-- The sum of a series against its partial sum, for `0 ≤ ζ ≤ 1`. -/
theorem rem_small {a : ℕ → ℝ} {q : ℕ → ℚ} (ha : a 18 = q 18) (hq : qabs (q 18) ≤ 1 / 2 ^ 100)
    (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (h : |S - P| ≤ 2 * |a 18| * |ζ| ^ 18) :
    |S - P| ≤ 1 / 2 ^ 99 := by
  have h1 : |a 18| ≤ 1 / 2 ^ 100 := by
    rw [ha, ← qabs_cast]
    have := Rat.cast_le (K := ℝ) |>.mpr hq
    push_cast at this ⊢
    exact this
  have h2 : |ζ| ^ 18 ≤ 1 := by rw [abs_of_nonneg hζ0]; exact pow_le_one₀ hζ0 hζ1
  have h3 : 2 * |a 18| * |ζ| ^ 18 ≤ 2 * (1 / 2 ^ 100) * 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by positivity)
  have e : (2 : ℝ) * (1 / 2 ^ 100) * 1 = 1 / 2 ^ 99 := by norm_num
  linarith

theorem zeta_facts (x : ℝ) (hx : |x| ≤ 2) : 0 ≤ x ^ 2 / 4 ∧ x ^ 2 / 4 ≤ 1 := by
  constructor
  · positivity
  · have : x ^ 2 ≤ 4 := by nlinarith [abs_nonneg x, sq_abs x]
    linarith

theorem check_at (E : List ℚ) (ε : ℚ) (d : ℕ) (h : check E 0 1 ε d = true) (ζ : ℝ)
    (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) : |eval E ζ| ≤ ε := by
  have := check_sound E 0 1 ε d h ζ (by push_cast; exact h0) (by push_cast; exact h1)
  exact this

/-- `J₀` below 2. -/
theorem j0_approx (x : ℝ) (hx : |x| ≤ 2) :
    |J0 x - (1 - x ^ 2 / 4 + x ^ 2 * (x ^ 2 * eval R0 (x ^ 2)) / eval S0 (x ^ 2))| ≤
      12 / 100 * 𝐮 + 1 / 2 ^ 99 := by
  obtain ⟨c0, -, -, -⟩ := checks
  obtain ⟨hS0, -, -, -, h18, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x hx
  set ζ := x ^ 2 / 4 with hζ
  have hz : x ^ 2 = 4 * ζ := by rw [hζ]; ring
  have hr := rem_small (a := a0) (q := qa0) rfl h18 ζ hz0 hz1
    (a0_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hE := check_at _ _ _ c0 ζ hz0 hz1
  have hS : 1 ≤ eval S0 (x ^ 2) := one_le_eval S0 rfl hS0 _ (by positivity)
  rw [E0, eval_subP, eval_mulP, eval_mulP, eval_subP, eval_sc4, eval_sc4] at hE
  simp only [eval_cons, eval_nil] at hE
  rw [← hz] at hE
  push_cast at hE
  have hS0' : 0 < eval S0 (x ^ 2) := by linarith
  have key : |eval (a0List 18) ζ - (1 - x ^ 2 / 4 + x ^ 2 * (x ^ 2 * eval R0 (x ^ 2)) /
      eval S0 (x ^ 2))| ≤ 12 / 100 * 𝐮 := by
    have e : eval (a0List 18) ζ - (1 - x ^ 2 / 4 + x ^ 2 * (x ^ 2 * eval R0 (x ^ 2)) /
        eval S0 (x ^ 2)) = (eval S0 (x ^ 2) * (eval (a0List 18) ζ - (1 + ζ * (-1 + ζ * 0))) -
        (0 + ζ * (0 + ζ * (16 + ζ * 0))) * eval R0 (x ^ 2)) / eval S0 (x ^ 2) := by
      field_simp
      rw [hz]
      ring
    rw [e, abs_div, abs_of_pos hS0', div_le_iff₀ hS0']
    have : (12 / 100 / 2 ^ 53 : ℝ) = 12 / 100 * 𝐮 := by norm_num [unitRoundoff64]
    rw [this] at hE
    have h0 : 0 ≤ 12 / 100 * 𝐮 := by norm_num [unitRoundoff64]
    nlinarith
  have hJ : J0 x = psum a0 ζ := rfl
  rw [hJ]
  have := abs_sub_le (psum a0 ζ) (eval (a0List 18) ζ)
    (1 - x ^ 2 / 4 + x ^ 2 * (x ^ 2 * eval R0 (x ^ 2)) / eval S0 (x ^ 2))
  linarith


/-- `J₁` below 2. -/
theorem j1_approx (x : ℝ) (hx : |x| ≤ 2) :
    |J1 x - (x / 2 + x * (x ^ 2 * eval R1 (x ^ 2)) / eval S1 (x ^ 2))| ≤
      |x| * (5 / 1000 * 𝐮 + 1 / 2 ^ 99) := by
  obtain ⟨-, c1, -, -⟩ := checks
  obtain ⟨-, hS1, -, -, -, h18, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x hx
  set ζ := x ^ 2 / 4 with hζ
  have hz : x ^ 2 = 4 * ζ := by rw [hζ]; ring
  have hr := rem_small (a := a1) (q := qa1) rfl h18 ζ hz0 hz1
    (a1_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hE := check_at _ _ _ c1 ζ hz0 hz1
  have hS : 1 ≤ eval S1 (x ^ 2) := one_le_eval S1 rfl hS1 _ (by positivity)
  rw [E1, eval_subP, eval_mulP, eval_mulP, eval_subP, eval_sc4, eval_sc4, eval_scaleP] at hE
  simp only [eval_cons, eval_nil] at hE
  rw [← hz] at hE
  push_cast at hE
  have hS0' : 0 < eval S1 (x ^ 2) := by linarith
  have key : |eval (a1List 18) ζ / 2 - (1 / 2 + x ^ 2 * eval R1 (x ^ 2) / eval S1 (x ^ 2))| ≤
      5 / 1000 * 𝐮 := by
    have e : eval (a1List 18) ζ / 2 - (1 / 2 + x ^ 2 * eval R1 (x ^ 2) / eval S1 (x ^ 2)) =
        (eval S1 (x ^ 2) * (1 / 2 * eval (a1List 18) ζ - (1 / 2 + ζ * 0)) -
        (0 + ζ * (4 + ζ * 0)) * eval R1 (x ^ 2)) / eval S1 (x ^ 2) := by
      field_simp
      rw [hz]
      ring
    rw [e, abs_div, abs_of_pos hS0', div_le_iff₀ hS0']
    have : (5 / 1000 / 2 ^ 53 : ℝ) = 5 / 1000 * 𝐮 := by norm_num [unitRoundoff64]
    rw [this] at hE
    have h0 : 0 ≤ 5 / 1000 * 𝐮 := by norm_num [unitRoundoff64]
    nlinarith
  have hJ : J1 x = x / 2 * psum a1 ζ := rfl
  have e2 : J1 x - (x / 2 + x * (x ^ 2 * eval R1 (x ^ 2)) / eval S1 (x ^ 2)) =
      x * ((psum a1 ζ / 2 - eval (a1List 18) ζ / 2) + (eval (a1List 18) ζ / 2 -
        (1 / 2 + x ^ 2 * eval R1 (x ^ 2) / eval S1 (x ^ 2)))) := by
    rw [hJ]
    field_simp
    ring
  rw [e2, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
  have h1 : |psum a1 ζ / 2 - eval (a1List 18) ζ / 2| ≤ 1 / 2 ^ 99 := by
    rw [show psum a1 ζ / 2 - eval (a1List 18) ζ / 2 = (psum a1 ζ - eval (a1List 18) ζ) / 2 by ring,
      abs_div, abs_two]
    have : (0 : ℝ) ≤ 1 / 2 ^ 99 := by positivity
    linarith
  have := abs_add_le (psum a1 ζ / 2 - eval (a1List 18) ζ / 2) (eval (a1List 18) ζ / 2 -
    (1 / 2 + x ^ 2 * eval R1 (x ^ 2) / eval S1 (x ^ 2)))
  linarith

/-! The constants of the second-kind forms. -/

theorem two_div_pi_close : |2 / π - κ2| ≤ 1 / 2 ^ 64 := by
  have h1 : 2 / π < 2 / 3.14159265358979323846 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_d20
  have h2 : 2 / 3.14159265358979323847 < 2 / π :=
    div_lt_div_of_pos_left (by norm_num) Real.pi_pos Real.pi_lt_d20
  rw [abs_le, κ2]
  push_cast
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

def glo : ℚ := -1159315156584124488108 / 10 ^ 22
def ghi : ℚ := -1159315156584124488106 / 10 ^ 22

theorem gamma_bounds_q : glo ≤ EulerGamma.gammaMid - EulerGamma.logTwo - 1 / 2 ^ 84 - 1 / 2 ^ 100 ∧
    EulerGamma.gammaMid - EulerGamma.logTwo + 1 / 2 ^ 84 + 1 / 2 ^ 100 ≤ ghi := by
  decide +kernel

theorem gamma_sub_log_two : (glo : ℝ) ≤ eulerMascheroniConstant - log 2 ∧
    eulerMascheroniConstant - log 2 ≤ ghi := by
  have h1 := EulerGamma.gamma_close
  have h2 := EulerGamma.gamma_rad_small
  have h3 := EulerGamma.log_two_close
  obtain ⟨q1, q2⟩ := gamma_bounds_q
  have r1 := (Rat.cast_le (K := ℝ)).mpr q1
  have r2 := (Rat.cast_le (K := ℝ)).mpr q2
  have h2' := (Rat.cast_lt (K := ℝ)).mpr h2
  push_cast at r1 r2 h2'
  rw [abs_le] at h1 h3
  norm_num at h3
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

theorem k1_close : |2 / π * (eulerMascheroniConstant - log 2) - κ1| ≤ 1 / 2 ^ 64 := by
  have h1 : 2 / π < 2 / 3.14159265358979323846 :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_d20
  have h2 : 2 / 3.14159265358979323847 < 2 / π :=
    div_lt_div_of_pos_left (by norm_num) Real.pi_pos Real.pi_lt_d20
  obtain ⟨g1, g2⟩ := gamma_sub_log_two
  set g := eulerMascheroniConstant - log 2
  set p := 2 / π
  have hg : g < 0 := by
    have : ((ghi : ℚ) : ℝ) < 0 := by norm_num [ghi]
    linarith
  have hp : 0 < p := by positivity
  have e1 : p * g ≤ 2 / 3.14159265358979323847 * ghi := by
    have := mul_le_mul_of_nonneg_left g2 hp.le
    nlinarith
  have e2 : 2 / 3.14159265358979323846 * glo ≤ p * g := by
    have := mul_le_mul_of_nonneg_left g1 hp.le
    nlinarith
  rw [abs_le, κ1]
  simp only [glo, ghi] at e1 e2
  push_cast at e1 e2 ⊢
  constructor <;> norm_num at e1 e2 ⊢ <;> linarith

theorem psum_a0_bound (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) : |psum a0 ζ| ≤ 3 / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, q0, q1, q2, -⟩ := coeff_facts
  have hr := a0_remainder ζ (by rw [abs_of_nonneg h0]; exact h1) 2 (by norm_num)
  have e : eval (a0List 2) ζ = 1 - ζ := by
    simp only [a0List, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [q0, q1]
    push_cast
    ring
  have ha : |a0 2| = 1 / 4 := by rw [a0, ← qabs_cast, q2]; norm_num
  rw [e, ha, abs_of_nonneg h0] at hr
  have : ζ ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  rw [abs_le] at hr ⊢
  constructor <;> nlinarith [hr.1, hr.2]

theorem psum_c0_bound (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) : |psum c0 ζ| ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, r0, r1, -⟩ := coeff_facts
  have hr := c0_remainder ζ (by rw [abs_of_nonneg h0]; exact h1) 1 (by norm_num)
  have e : eval (c0List 1) ζ = 0 := by
    simp only [c0List, List.range_one, List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [r0]
    push_cast
    ring
  have hc : |c0 1| = 1 := by rw [c0, ← qabs_cast, r1]; norm_num
  rw [e, hc, abs_of_nonneg h0, sub_zero, pow_one] at hr
  linarith

theorem psum_a1_bound (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) : |psum a1 ζ| ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q0, q1, -⟩ := coeff_facts
  have hr := a1_remainder ζ (by rw [abs_of_nonneg h0]; exact h1) 1 (by norm_num)
  have e : eval (a1List 1) ζ = 1 := by
    simp only [a1List, List.range_one, List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [q0]
    push_cast
    ring
  have ha : |a1 1| = 1 / 2 := by rw [a1, ← qabs_cast, q1]; norm_num
  rw [e, ha, abs_of_nonneg h0, pow_one] at hr
  have := abs_sub_abs_le_abs_sub (psum a1 ζ) 1
  rw [abs_one] at this
  linarith

theorem psum_c1_bound (ζ : ℝ) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) : |psum c1 ζ| ≤ 7 / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, r0, r1⟩ := coeff_facts
  have hr := c1_remainder ζ (by rw [abs_of_nonneg h0]; exact h1) 1 (by norm_num)
  have e : eval (c1List 1) ζ = 1 := by
    simp only [c1List, List.range_one, List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [r0]
    push_cast
    ring
  have hc : |c1 1| = 5 / 4 := by rw [c1, ← qabs_cast, r1]; norm_num
  rw [e, hc, abs_of_nonneg h0, pow_one] at hr
  have := abs_sub_abs_le_abs_sub (psum c1 ζ) 1
  rw [abs_one] at this
  linarith

/-- `Y₀` below 2. -/
theorem y0_approx (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) :
    |Y0 x - 2 / π * log x * J0 x - eval U0 (x ^ 2) / eval V0 (x ^ 2)| ≤
      21 / 100 * 𝐮 + 1 / 2 ^ 60 := by
  obtain ⟨-, -, c2, -⟩ := checks
  obtain ⟨-, -, hV0, -, h18a, -, h18c, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x (by rw [abs_of_pos hx0]; exact hx)
  set ζ := x ^ 2 / 4 with hζ
  have hz : x ^ 2 = 4 * ζ := by rw [hζ]; ring
  have hra := rem_small (a := a0) (q := qa0) rfl h18a ζ hz0 hz1
    (a0_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hrc := rem_small (a := c0) (q := qc0) rfl h18c ζ hz0 hz1
    (c0_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hE := check_at _ _ _ c2 ζ hz0 hz1
  have hV : 1 ≤ eval V0 (x ^ 2) := one_le_eval V0 rfl hV0 _ (by positivity)
  rw [E2, eval_subP, eval_mulP, eval_addP, eval_scaleP, eval_scaleP, eval_sc4, eval_sc4] at hE
  rw [← hz] at hE
  have hV' : 0 < eval V0 (x ^ 2) := by linarith
  set AN := eval (a0List 18) ζ
  set CN := eval (c0List 18) ζ
  have key : |eval U0 (x ^ 2) / eval V0 (x ^ 2) - (κ1 * AN + κ2 * CN)| ≤ 21 / 100 * 𝐮 := by
    have e : eval U0 (x ^ 2) / eval V0 (x ^ 2) - (κ1 * AN + κ2 * CN) =
        (eval U0 (x ^ 2) - eval V0 (x ^ 2) * (κ1 * AN + κ2 * CN)) / eval V0 (x ^ 2) := by
      field_simp
    rw [e, abs_div, abs_of_pos hV', div_le_iff₀ hV']
    have : (21 / 100 / 2 ^ 53 : ℝ) = 21 / 100 * 𝐮 := by norm_num [unitRoundoff64]
    push_cast at hE
    rw [this] at hE
    have h0 : 0 ≤ 21 / 100 * 𝐮 := by norm_num [unitRoundoff64]
    nlinarith
  have hA := psum_a0_bound ζ hz0 hz1
  have hC := psum_c0_bound ζ hz0 hz1
  have k1 := k1_close
  have k2 := two_div_pi_close
  have hT : Y0 x - 2 / π * log x * J0 x =
      2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ + 2 / π * psum c0 ζ := by
    rw [Y0_sub_log x hx0]
    ring
  rw [hT]
  have b1 : |2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ - κ1 * AN| ≤
      1 / 2 ^ 64 * (3 / 2) + 1 / 10 * (1 / 2 ^ 99) := by
    have e : 2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ - κ1 * AN =
        (2 / π * (eulerMascheroniConstant - log 2) - κ1) * psum a0 ζ +
          κ1 * (psum a0 ζ - AN) := by ring
    rw [e]
    have := abs_add_le ((2 / π * (eulerMascheroniConstant - log 2) - κ1) * psum a0 ζ)
      (κ1 * (psum a0 ζ - AN))
    rw [abs_mul, abs_mul] at this
    have m1 := mul_le_mul k1 hA (abs_nonneg _) (by positivity)
    have hk : |(κ1 : ℝ)| ≤ 1 / 10 := by rw [κ1]; push_cast; rw [abs_le]; constructor <;> norm_num
    have m2 := mul_le_mul hk hra (abs_nonneg _) (by norm_num)
    linarith
  have b2 : |2 / π * psum c0 ζ - κ2 * CN| ≤ 1 / 2 ^ 64 * 2 + 1 * (1 / 2 ^ 99) := by
    have e : 2 / π * psum c0 ζ - κ2 * CN = (2 / π - κ2) * psum c0 ζ + κ2 * (psum c0 ζ - CN) := by
      ring
    rw [e]
    have := abs_add_le ((2 / π - κ2) * psum c0 ζ) (κ2 * (psum c0 ζ - CN))
    rw [abs_mul, abs_mul] at this
    have m1 := mul_le_mul k2 hC (abs_nonneg _) (by positivity)
    have hk : |(κ2 : ℝ)| ≤ 1 := by rw [κ2]; push_cast; rw [abs_le]; constructor <;> norm_num
    have m2 := mul_le_mul hk hrc (abs_nonneg _) (by norm_num)
    linarith
  have := abs_sub_le (2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ + 2 / π * psum c0 ζ)
    (κ1 * AN + κ2 * CN) (eval U0 (x ^ 2) / eval V0 (x ^ 2))
  have h3 : |2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ + 2 / π * psum c0 ζ -
      (κ1 * AN + κ2 * CN)| ≤ 1 / 2 ^ 64 * (3 / 2) + 1 / 10 * (1 / 2 ^ 99) +
        (1 / 2 ^ 64 * 2 + 1 * (1 / 2 ^ 99)) := by
    have e : 2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ + 2 / π * psum c0 ζ -
        (κ1 * AN + κ2 * CN) = (2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ - κ1 * AN) +
        (2 / π * psum c0 ζ - κ2 * CN) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add b1 b2)
  rw [abs_sub_comm (κ1 * AN + κ2 * CN)] at this
  have hnum : (1 : ℝ) / 2 ^ 64 * (3 / 2) + 1 / 10 * (1 / 2 ^ 99) + (1 / 2 ^ 64 * 2 + 1 * (1 / 2 ^ 99))
      ≤ 1 / 2 ^ 60 := by norm_num
  rw [show 2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ + 2 / π * psum c0 ζ -
    eval U0 (x ^ 2) / eval V0 (x ^ 2) = 2 / π * (eulerMascheroniConstant - log 2) * psum a0 ζ +
    2 / π * psum c0 ζ - eval U0 (x ^ 2) / eval V0 (x ^ 2) from rfl]
  linarith

/-- `Y₁` below 2. -/
theorem y1_approx (x : ℝ) (hx0 : 0 < x) (hx : x ≤ 2) :
    |Y1 x - 2 / π * (log x * J1 x - 1 / x) - x * (eval U1 (x ^ 2) / eval V1 (x ^ 2))| ≤
      x * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) := by
  obtain ⟨-, -, -, c3⟩ := checks
  obtain ⟨-, -, -, hV1, -, h18a, -, h18c, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x (by rw [abs_of_pos hx0]; exact hx)
  set ζ := x ^ 2 / 4 with hζ
  have hz : x ^ 2 = 4 * ζ := by rw [hζ]; ring
  have hra := rem_small (a := a1) (q := qa1) rfl h18a ζ hz0 hz1
    (a1_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hrc := rem_small (a := c1) (q := qc1) rfl h18c ζ hz0 hz1
    (c1_remainder ζ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))
  have hE := check_at _ _ _ c3 ζ hz0 hz1
  have hV : 1 ≤ eval V1 (x ^ 2) := one_le_eval V1 rfl hV1 _ (by positivity)
  rw [E3, eval_subP, eval_mulP, eval_subP, eval_scaleP, eval_scaleP, eval_sc4, eval_sc4] at hE
  rw [← hz] at hE
  have hV' : 0 < eval V1 (x ^ 2) := by linarith
  set AN := eval (a1List 18) ζ
  set CN := eval (c1List 18) ζ
  have key : |eval U1 (x ^ 2) / eval V1 (x ^ 2) - ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN)| ≤
      155 / 1000 * 𝐮 := by
    have e : eval U1 (x ^ 2) / eval V1 (x ^ 2) - ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN) =
        (eval U1 (x ^ 2) - eval V1 (x ^ 2) * ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN)) /
          eval V1 (x ^ 2) := by
      field_simp
    rw [e, abs_div, abs_of_pos hV', div_le_iff₀ hV']
    have hc : ((155 / 1000 / 2 ^ 53 : ℚ) : ℝ) = 155 / 1000 * 𝐮 := by
      push_cast; norm_num [unitRoundoff64]
    rw [hc] at hE
    have h0 : 0 ≤ 155 / 1000 * 𝐮 := by norm_num [unitRoundoff64]
    nlinarith
  have hA := psum_a1_bound ζ hz0 hz1
  have hC := psum_c1_bound ζ hz0 hz1
  have k1 := k1_close
  have k2 := two_div_pi_close
  have hT : Y1 x - 2 / π * (log x * J1 x - 1 / x) =
      x * (1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ -
        1 / 4 * (2 / π) * psum c1 ζ) := by
    rw [Y1_sub_log x hx0]
    field_simp
    ring
  rw [hT, ← mul_sub, abs_mul, abs_of_pos hx0]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have b1 : |1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ -
      (κ1 / 2 : ℚ) * AN| ≤ 1 / 2 ^ 64 * 2 + 1 / 10 * (1 / 2 ^ 99) := by
    have e : 1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ - (κ1 / 2 : ℚ) * AN =
        1 / 2 * ((2 / π * (eulerMascheroniConstant - log 2) - κ1) * psum a1 ζ +
          κ1 * (psum a1 ζ - AN)) := by push_cast; ring
    rw [e, abs_mul]
    have := abs_add_le ((2 / π * (eulerMascheroniConstant - log 2) - κ1) * psum a1 ζ)
      (κ1 * (psum a1 ζ - AN))
    rw [abs_mul, abs_mul] at this
    have m1 := mul_le_mul k1 hA (abs_nonneg _) (by positivity)
    have hk : |(κ1 : ℝ)| ≤ 1 / 10 := by rw [κ1]; push_cast; rw [abs_le]; constructor <;> norm_num
    have m2 := mul_le_mul hk hra (abs_nonneg _) (by norm_num)
    rw [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
    nlinarith
  have b2 : |1 / 4 * (2 / π) * psum c1 ζ - (κ2 / 4 : ℚ) * CN| ≤ 1 / 2 ^ 64 * 4 + 1 * (1 / 2 ^ 99) := by
    have e : 1 / 4 * (2 / π) * psum c1 ζ - (κ2 / 4 : ℚ) * CN =
        1 / 4 * ((2 / π - κ2) * psum c1 ζ + κ2 * (psum c1 ζ - CN)) := by push_cast; ring
    rw [e, abs_mul]
    have := abs_add_le ((2 / π - κ2) * psum c1 ζ) (κ2 * (psum c1 ζ - CN))
    rw [abs_mul, abs_mul] at this
    have m1 := mul_le_mul k2 hC (abs_nonneg _) (by positivity)
    have hk : |(κ2 : ℝ)| ≤ 1 := by rw [κ2]; push_cast; rw [abs_le]; constructor <;> norm_num
    have m2 := mul_le_mul hk hrc (abs_nonneg _) (by norm_num)
    rw [show |(1 / 4 : ℝ)| = 1 / 4 by norm_num]
    nlinarith
  have h3 : |(1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ -
      1 / 4 * (2 / π) * psum c1 ζ) - ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN)| ≤
      1 / 2 ^ 64 * 2 + 1 / 10 * (1 / 2 ^ 99) + (1 / 2 ^ 64 * 4 + 1 * (1 / 2 ^ 99)) := by
    have e : (1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ -
        1 / 4 * (2 / π) * psum c1 ζ) - ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN) =
        (1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ - (κ1 / 2 : ℚ) * AN) -
        (1 / 4 * (2 / π) * psum c1 ζ - (κ2 / 4 : ℚ) * CN) := by ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add b1 b2)
  have := abs_sub_le (1 / 2 * (2 / π * (eulerMascheroniConstant - log 2)) * psum a1 ζ -
    1 / 4 * (2 / π) * psum c1 ζ) ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN)
    (eval U1 (x ^ 2) / eval V1 (x ^ 2))
  rw [abs_sub_comm ((κ1 / 2 : ℚ) * AN - (κ2 / 4 : ℚ) * CN)] at this
  have hnum : (1 : ℝ) / 2 ^ 64 * 2 + 1 / 10 * (1 / 2 ^ 99) + (1 / 2 ^ 64 * 4 + 1 * (1 / 2 ^ 99)) ≤
      1 / 2 ^ 60 := by norm_num
  linarith

#print axioms eval_sc4
#print axioms checks
#print axioms j0_approx
#print axioms j1_approx
#print axioms two_div_pi_close
#print axioms k1_close
#print axioms y0_approx
#print axioms y1_approx

end Library.Numerics.Float64.Bessel.BesselSmallApprox
