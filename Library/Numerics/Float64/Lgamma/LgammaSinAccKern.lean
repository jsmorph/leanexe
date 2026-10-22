import Library.Numerics.Float64.Lgamma.LgammaPolyDDSteps
import Library.Numerics.Float64.Lgamma.LgammaApprox
import Library.Numerics.Float64.Tgamma.TgammaWords
import Library.Numerics.Float64.Tgamma.TgammaExpr
import Library.Numerics.Float64.Tgamma.TgammaPolyLip
import Library.Numerics.Float64.Tgamma.TgammaMainRed
import Library.Numerics.Float64.Tgamma.TgammaFloor

/-!
The kernels of `Lgamma.asSinpipidAccurate`: the double-double polynomials `polyDD` at word 143
(five pairs, `cos (π d/128) ≈ 1 + w sinAccCos w`) and at word 153 (six pairs,
`sin (π d/128) ≈ d sinAccSin w`) of `Lgamma.sinpiTable`, at `w = d2h + d2l` with `d2h = d · d` and
`d2l = fma (d, d, -d2h)`.  Their coefficients fall from `2.5 · 10^-2` to `5 · 10^-26`, so the
proof uses `LgammaPolyDDSteps.polyDD_steps` with a bound per step, which the kernel checks with
powers of two (`steps_ok`).  The errors are at most `2^-115` and `2^-109` at `w`
(`kern_spec`), and the Lipschitz bounds of the two polynomials move them to `d²`, which `w`
approximates within `d²/2^106 + 2^-1074` (`sq_spec`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinAccKern
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaMul
  LgammaPolyDDSteps TgammaWords

set_option exponentiation.threshold 4096

/-- The table of `asSinpipidAccurate`. -/
abbrev T := Lgamma.sinpiTable

/-- The high and the low word of coefficient `k` of the kernel at `o`. -/
abbrev hiQ (o k : ℕ) : ℚ := PolyBound.ratOfWord T[o + 2 * k]!
abbrev loQ (o k : ℕ) : ℚ := PolyBound.ratOfWord T[o + 2 * k + 1]!

/-- The bounds on `|d2h|`, `|d2l|`, and `|d2h + d2l|`. -/
def XhQ : ℚ := 1 / 4 + 1 / 2 ^ 54
def XlQ : ℚ := 1 / 2 ^ 54

/-- The bound on the Horner value of step `m` of the kernel at `o` with `N` coefficients. -/
def hbQ (o N : ℕ) : ℕ → ℚ
  | 0 => PolyBound.qabs (hiQ o (N - 1) + loQ o (N - 1))
  | m + 1 => PolyBound.qabs (hiQ o (N - 2 - m) + loQ o (N - 2 - m)) + (XhQ + XlQ) * hbQ o N m

/-- `lowS`, `topS`, `epsS`, and `growS` of `LgammaPolyDDSteps` on rationals. -/
def lowQ (Xh Xl K Λ Cl : ℚ) : ℚ :=
  Cl + ((K * Xl + Λ * Xh) * (1 + 1 / 2 ^ 50) + K * Xh / 2 ^ 52 + 1 / 2 ^ 1070)

def topQ (Xh K C : ℚ) : ℚ :=
  (C + (K * Xh * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075)) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073

def epsQ (Xh Xl K Λ C Cl : ℚ) : ℚ :=
  Λ * Xl + (4 * (K * Xl + Λ * Xh) + K * Xh / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 +
    (3 * lowQ Xh Xl K Λ Cl + topQ Xh K C / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53

def growQ (Xh Xl K Λ C Cl : ℚ) : ℚ :=
  lowQ Xh Xl K Λ Cl * (1 + 1 / 2 ^ 51) + topQ Xh K C / 2 ^ 51 + 1 / 2 ^ 1073

theorem epsS_cast (a b c d e f : ℚ) :
    epsS (a : ℝ) b c d e f = ((epsQ a b c d e f : ℚ) : ℝ) := by
  simp only [epsS, epsQ, lowS, lowQ, topS, topQ]
  push_cast
  ring

theorem growS_cast (a b c d e f : ℚ) :
    growS (a : ℝ) b c d e f = ((growQ a b c d e f : ℚ) : ℝ) := by
  simp only [growS, growQ, lowS, lowQ, topS, topQ]
  push_cast
  ring

/-- The powers `1/2^k` of a list of exponents. -/
def pw (l : List ℕ) : List ℚ := l.map fun k => 1 / 2 ^ k

theorem pw_nonneg (l : List ℕ) (m : ℕ) : 0 ≤ (pw l).getD m 0 := by
  induction l generalizing m with
  | nil => simp [pw]
  | cons a t ih =>
    cases m with
    | zero => simp only [pw, List.map_cons, List.getD_cons_zero]; positivity
    | succ m => simpa only [pw, List.map_cons, List.getD_cons_succ] using ih m

/-- The conditions of `polyDD_steps` for the kernel at `o` with `N` coefficients, the bounds `C`
and `Cl` on the words, and the bounds `E`, `Λ`, and `K` of the steps. -/
def stepsOk (o N : ℕ) (C Cl E Λ K : List ℚ) : Bool :=
  (List.range N).all (fun k => Wasm.IEEE64.isFinite T[o + 2 * k]! &&
    Wasm.IEEE64.isFinite T[o + 2 * k + 1]! &&
    decide (PolyBound.qabs (hiQ o k) ≤ C.getD k 0) && decide (PolyBound.qabs (loQ o k) ≤ Cl.getD k 0) &&
    decide (C.getD k 0 ≤ 2 ^ 797) && decide (Cl.getD k 0 ≤ 2 ^ 797)) &&
  decide (Cl.getD (N - 1) 0 / 2 ^ 53 ≤ E.getD 0 0) &&
  decide (Cl.getD (N - 1) 0 * (1 + 1 / 2 ^ 53) ≤ Λ.getD 0 0) &&
  (List.range (N - 1)).all (fun m =>
    decide (hbQ o N m + E.getD m 0 + Λ.getD m 0 ≤ K.getD m 0) &&
    decide (K.getD m 0 ≤ 2 ^ 797) && decide (Λ.getD m 0 ≤ 2 ^ 797) &&
    decide (K.getD m 0 * XhQ * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (hiQ o (N - 2 - m))) &&
    decide ((XhQ + XlQ) * E.getD m 0 + epsQ XhQ XlQ (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
      (Cl.getD (N - 2 - m) 0) ≤ E.getD (m + 1) 0) &&
    decide (growQ XhQ XlQ (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) ≤
      Λ.getD (m + 1) 0))

/-- The bounds of the cosine kernel. -/
def cC : List ℚ := pw [11, 25, 41, 58, 75]
def cCl : List ℚ := pw [65, 79, 97, 113, 133]
def cE : List ℚ := pw [186, 162, 145, 129, 115]
def cΛ : List ℚ := pw [132, 108, 91, 75, 61]
def cK : List ℚ := pw [75, 58, 41, 25]

/-- The bounds of the sine kernel. -/
def sC : List ℚ := pw [5, 18, 33, 49, 66, 84]
def sCl : List ℚ := pw [59, 72, 88, 103, 121, 138]
def sE : List ℚ := pw [191, 170, 153, 137, 122, 109]
def sΛ : List ℚ := pw [137, 116, 99, 83, 68, 55]
def sK : List ℚ := pw [84, 66, 49, 33, 18]

theorem cos_ok : stepsOk 143 5 cC cCl cE cΛ cK = true := by decide +kernel

theorem sin_ok : stepsOk 153 6 sC sCl sE sΛ sK = true := by decide +kernel

/-- The bounds on the polynomials: `|sinAccCos w| ≤ 1/3300` and `|sinAccSin w| ≤ 1/40.7`, and
their Lipschitz constants on `|w| ≤ 1/4 + 2^-52`. -/
theorem poly_bounds :
    hbQ 143 5 4 ≤ 1 / 3300 ∧ hbQ 153 6 5 ≤ 10 / 407 ∧
      Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (1 / 4 + 1 / 2 ^ 52) (LgammaApprox.ddCoeffs T 143 5) ≤ 1 / 2 ^ 25 ∧
      Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (1 / 4 + 1 / 2 ^ 52) (LgammaApprox.ddCoeffs T 153 6) ≤ 1 / 2 ^ 18 := by
  decide +kernel

/-- The exact Horner value of the kernel at `o` is the polynomial of its pairs. -/
theorem horner_dd (o' : UInt64) (o N : ℕ) (ho : o'.toNat = o) (hN : 1 ≤ N)
    (hf : ∀ k < N, Wasm.IEEE64.isFinite T[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite T[o + 2 * k + 1]! = true) (w : ℝ) :
    horner (cDD T o') N 0 w (N - 1) = PolyBound.eval (LgammaApprox.ddCoeffs T o N) w := by
  rw [horner_eval _ N hN, zero_mul, add_zero,
    show LgammaApprox.ddCoeffs T o N = (List.range N).map (fun k =>
      LgammaApprox.q T (o + 2 * k) + LgammaApprox.q T (o + 2 * k + 1)) from rfl,
    eval_map_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [cDD_rat T o' k (by rw [ho]; exact (hf k hk).1) (by rw [ho]; exact (hf k hk).2), ho]
  rfl

/-- The Horner values of the kernel at `o` are bounded by `hbQ`. -/
theorem horner_hb (o' : UInt64) (o N : ℕ) (ho : o'.toNat = o) (hN : 1 ≤ N)
    (hf : ∀ k < N, Wasm.IEEE64.isFinite T[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite T[o + 2 * k + 1]! = true) (w : ℝ) (hw : |w| ≤ ((XhQ + XlQ : ℚ) : ℝ)) :
    ∀ m, m + 1 ≤ N → |horner (cDD T o') N 0 w m| ≤ (hbQ o N m : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro _
    have e : horner (cDD T o') N 0 w 0 = ((hiQ o (N - 1) + loQ o (N - 1) : ℚ) : ℝ) := by
      rw [show horner (cDD T o') N 0 w 0 = cDD T o' (N - 1) + 0 from rfl, add_zero,
        cDD_rat T o' (N - 1) (by rw [ho]; exact (hf (N - 1) (by omega)).1)
          (by rw [ho]; exact (hf (N - 1) (by omega)).2), ho]
    rw [e, hbQ, Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [show horner (cDD T o') N 0 w (m + 1) = cDD T o' (N - 2 - m) + w * horner (cDD T o') N 0 w m
        from rfl,
      cDD_rat T o' (N - 2 - m) (by rw [ho]; exact (hf (N - 2 - m) (by omega)).1)
        (by rw [ho]; exact (hf (N - 2 - m) (by omega)).2), ho, hbQ]
    push_cast
    rw [Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]
    have h2 := abs_add_le (((hiQ o (N - 2 - m) + loQ o (N - 2 - m) : ℚ) : ℝ))
      (w * horner (cDD T o') N 0 w m)
    have h3 : |w * horner (cDD T o') N 0 w m| ≤ ((XhQ + XlQ : ℚ) : ℝ) * (hbQ o N m : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hw h1 (abs_nonneg _) (by unfold XhQ XlQ; norm_num)
    push_cast at h2 h3 ⊢
    linarith

/-- **A kernel from its check**: `polyDD` at the double-double `xh + xl` within `E (N - 1)` of the
polynomial of its pairs, with the low part at most `Λ (N - 1)`. -/
theorem kern_gen (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (o N : ℕ) (C Cl E Λ K : List ℚ)
    (hok : stepsOk o N C Cl E Λ K = true) (hK0 : ∀ m, 0 ≤ K.getD m 0) (o' n' : UInt64) (ho : o'.toNat = o) (hn : n'.toNat = N)
    (hN1 : 1 ≤ N) (hon : o + 2 * N < 2 ^ 63) (xh xl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hXh : |value xh.toBits| ≤ (XhQ : ℝ))
    (hXl : |value xl.toBits| ≤ (XlQ : ℝ)) :
    Finite (Lgamma.polyDD T o' n' xh xl 0.0).1.toBits ∧
      Finite (Lgamma.polyDD T o' n' xh xl 0.0).2.toBits ∧
      |value (Lgamma.polyDD T o' n' xh xl 0.0).1.toBits +
          value (Lgamma.polyDD T o' n' xh xl 0.0).2.toBits -
          PolyBound.eval (LgammaApprox.ddCoeffs T o N) (value xh.toBits + value xl.toBits)| ≤
        (E.getD (N - 1) 0 : ℝ) ∧
      |value (Lgamma.polyDD T o' n' xh xl 0.0).2.toBits| ≤ (Λ.getD (N - 1) 0 : ℝ) := by
  simp only [stepsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hw, hE0⟩, hΛ0⟩, hs⟩ := hok
  have hfin : ∀ k < N, Wasm.IEEE64.isFinite T[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite T[o + 2 * k + 1]! = true := fun k hk => (hw k hk).1.1.1.1
  have hXX : |value xh.toBits + value xl.toBits| ≤ ((XhQ + XlQ : ℚ) : ℝ) := by
    have := abs_add_le (value xh.toBits) (value xl.toBits)
    push_cast; linarith
  have z0 := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_finite
  have zv := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_value
  have hval : ∀ k < N, value (Float.ofBits T[o + 2 * k]!).toBits = (hiQ o k : ℝ) ∧
      value (Float.ofBits T[o + 2 * k + 1]!).toBits = (loQ o k : ℝ) := fun k hk =>
    ⟨ofBits_value _ (hfin k hk).1, ofBits_value _ (hfin k hk).2⟩
  obtain ⟨h1, h2, h3, h4⟩ := polyDD_steps hF T o' n' xh xl 0.0 (by rw [hn]; exact hN1)
    (by rw [ho, hn]; exact hon)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).1)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).2)
    (XhQ : ℝ) (XlQ : ℝ) 0 0 0 0 (fun k => (C.getD k 0 : ℝ)) (fun k => (Cl.getD k 0 : ℝ))
    (fun k => (E.getD k 0 : ℝ)) (fun k => (Λ.getD k 0 : ℝ)) (fun k => (K.getD k 0 : ℝ))
    hxh hxl hXh hXl (by unfold XhQ XlQ; norm_num)
    (fun k hk => by
      rw [ho]; rw [hn] at hk
      rw [(hval k hk).1, ← Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]
      exact_mod_cast (hw k hk).1.1.1.2)
    (fun k hk => by
      rw [ho]; rw [hn] at hk
      rw [(hval k hk).2, ← Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]
      exact_mod_cast (hw k hk).1.1.2)
    (fun k hk => by
      rw [hn] at hk
      exact ⟨by exact_mod_cast (hw k hk).1.2, by exact_mod_cast (hw k hk).2⟩)
    z0 (by rw [zv]; simp) (by rw [zv]; simp) (by rw [zv]; simp)
    (Or.inl le_rfl) (by norm_num)
    (by rw [hn]; simp only [zero_add]; exact_mod_cast hE0)
    (by
      rw [hn]; simp only [zero_add]
      have := (Rat.cast_le (K := ℝ)).mpr hΛ0
      push_cast at this ⊢
      linarith)
    (fun m hm => by
      rw [hn] at hm ⊢
      have hb := horner_hb o' o N ho hN1 hfin _ hXX m (by omega)
      have := (hs m (by omega)).1.1.1.1.1
      have hc : ((hbQ o N m + E.getD m 0 + Λ.getD m 0 : ℚ) : ℝ) ≤ (K.getD m 0 : ℝ) := by
        exact_mod_cast this
      push_cast at hc
      linarith)
    (fun m hm => by
      rw [hn] at hm
      exact ⟨by exact_mod_cast (hs m (by omega)).1.1.1.1.2,
        by exact_mod_cast (hs m (by omega)).1.1.1.2⟩)
    (fun m hm => by
      rw [hn] at hm ⊢
      rw [ho, (hval (N - 2 - m) (by omega)).1, ← Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]
      have hb := horner_hb o' o N ho hN1 hfin _ hXX m (by omega)
      have hk : ((hbQ o N m + E.getD m 0 + Λ.getD m 0 : ℚ) : ℝ) ≤ (K.getD m 0 : ℝ) := by
        exact_mod_cast (hs m (by omega)).1.1.1.1.1
      have := (hs m (by omega)).1.1.2
      have hc : ((K.getD m 0 * XhQ * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 : ℚ) : ℝ) ≤
          ((PolyBound.qabs (hiQ o (N - 2 - m)) : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at hk hc ⊢
      have h1 : |horner (cDD T o') N 0 (value xh.toBits + value xl.toBits) m| + (E.getD m 0 : ℝ) +
          (Λ.getD m 0 : ℝ) ≤ (K.getD m 0 : ℝ) := by linarith
      have h2 := mul_le_mul h1 hXh (abs_nonneg _) (Rat.cast_nonneg.mpr (hK0 m))
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
      linarith)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).1.2
      have hc : ((((XhQ + XlQ) * E.getD m 0 + epsQ XhQ XlQ (K.getD m 0) (Λ.getD m 0)
          (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) : ℚ)) : ℝ) ≤ (E.getD (m + 1) 0 : ℝ) := by
        exact_mod_cast this
      rw [epsS_cast]
      push_cast at hc ⊢
      exact hc)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).2
      have hc : ((growQ XhQ XlQ (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
          (Cl.getD (N - 2 - m) 0) : ℚ) : ℝ) ≤ (Λ.getD (m + 1) 0 : ℝ) := by exact_mod_cast this
      rw [growS_cast]
      exact hc)
  rw [hn, horner_dd o' o N ho hN1 hfin] at h3
  rw [hn] at h4
  exact ⟨h1, h2, h3, h4⟩

/-- **The square of `d`** as `d2h + d2l`, with `d2h = d · d` and `d2l = fma (d, d, -d2h)`. -/
theorem sq_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (d : Float) (hd : Finite d.toBits)
    (hD : |value d.toBits| ≤ 1 / 2) :
    Finite (d * d).toBits ∧ Finite (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits ∧
      |value (d * d).toBits| ≤ (XhQ : ℝ) ∧ |value (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits| ≤ (XlQ : ℝ) ∧
      |value (d * d).toBits + value (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits - value d.toBits ^ 2| ≤
        value d.toBits ^ 2 / 2 ^ 106 + 1 / 2 ^ 1074 := by
  set v := value d.toBits with hvdef
  have hv2 : |v| * |v| = v ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have hv4 : v ^ 2 ≤ 1 / 4 := by
    rw [← hv2]; nlinarith [abs_nonneg v]
  have ha := fapprox_mul (fapprox_self d hd) (fapprox_self d hd) |v| |v| le_rfl le_rfl (|v| * |v|)
    (by simp) (by nlinarith [abs_nonneg v])
  simp only [mul_zero, zero_mul, add_zero, zero_add, hv2] at ha
  obtain ⟨haf, hae⟩ := ha
  have hsq : v * v = v ^ 2 := by ring
  rw [hsq] at hae
  obtain ⟨hnf, hnv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.neg_float (d * d) haf
  have hr : |v ^ 2 - value (d * d).toBits| ≤ v ^ 2 / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_sub_comm]; exact hae
  have hS : |value d.toBits * value d.toBits + value (-(d * d)).toBits| ≤ 2 ^ 1000 := by
    rw [hnv, ← hvdef, hsq, ← sub_eq_add_neg]
    linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000),
      div_le_div_of_nonneg_right hv4 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)]
  obtain ⟨hff, hfe⟩ := fma_approx hF d d (-(d * d)) hd hd hnf hS
  rw [hnv, ← hvdef, hsq, ← sub_eq_add_neg] at hfe
  have hrb : |v ^ 2 - value (d * d).toBits| / 2 ^ 53 ≤ (v ^ 2 / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 :=
    div_le_div_of_nonneg_right hr (by norm_num)
  have hv0 : 0 ≤ v ^ 2 := sq_nonneg v
  refine ⟨haf, hff, ?_, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (value (d * d).toBits) (v ^ 2)
    rw [abs_of_nonneg hv0] at this
    unfold XhQ; push_cast
    linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 54),
      div_le_div_of_nonneg_right hv4 (by norm_num : (0 : ℝ) ≤ 2 ^ 53), abs_sub_comm (value (d * d).toBits) (v ^ 2)]
  · have := abs_sub_abs_le_abs_sub (value (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits) (v ^ 2 - value (d * d).toBits)
    unfold XlQ; push_cast
    have h4 := div_le_div_of_nonneg_right hv4 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
    linarith [(by norm_num : ((1 : ℝ) / 4 / 2 ^ 53 + 1 / 2 ^ 1075) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 54)]
  · have e : value (d * d).toBits + value (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits - v ^ 2 =
        value (Library.Numerics.Arithmetic.Fma.Fma.fma d d (-(d * d))).toBits - (v ^ 2 - value (d * d).toBits) := by ring
    rw [e]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 1074),
      (by ring : (v ^ 2 / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 = v ^ 2 / 2 ^ 106 + 1 / 2 ^ 1075 / 2 ^ 53)]

end Library.Numerics.Float64.Lgamma.LgammaSinAccKern
