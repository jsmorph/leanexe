import Library.Numerics.Float64.Lgamma.LgammaSinAccKern

/-!
`Lgamma.polyDD` at a nonnegative double-double point `xh + xl ≤ X`, with bounds per step that
the kernel checks on `P` subintervals of `[0, X]` (`kern_iv`).  `LgammaSinAccKern.kern_gen` bounds
the Horner values by the sums of the coefficients' magnitudes, which suits coefficients of one
sign pattern that fall fast.  The coefficients of Stirling's series alternate in sign and grow to
`2.4 · 10^14`, and that bound exceeds the values by a factor near `10^4`.  Here `hornerIv`
encloses the Horner values on each subinterval `[a, b]` with `0 ≤ a` by interval arithmetic
(`horner_iv`), and the condition that each product stay below its coefficient, which `fastSum`
needs, is checked at each subinterval with `|xh| ≤ b + Xl`, the form of
`LgammaPolyDDSteps.polyDD_steps`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPolyIv
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaMul
  LgammaPolyDDSteps TgammaWords LgammaSinAccKern

set_option exponentiation.threshold 4096

/-- The product of `v ∈ [a, b]` with `a ≥ 0` and `h ∈ [l, u]`. -/
theorem mul_iv (a b l u v h : ℝ) (ha : 0 ≤ a) (hav : a ≤ v) (hvb : v ≤ b) (hl : l ≤ h)
    (hu : h ≤ u) : min (a * l) (b * l) ≤ v * h ∧ v * h ≤ max (a * u) (b * u) := by
  have hv0 : 0 ≤ v := ha.trans hav
  constructor
  · have h1 : v * l ≤ v * h := mul_le_mul_of_nonneg_left hl hv0
    rcases le_total 0 l with h0 | h0
    · exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_right hav h0).trans h1)
    · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hvb h0).trans h1)
  · have h1 : v * h ≤ v * u := mul_le_mul_of_nonneg_left hu hv0
    rcases le_total 0 u with h0 | h0
    · exact (h1.trans (mul_le_mul_of_nonneg_right hvb h0)).trans (le_max_right _ _)
    · exact (h1.trans (mul_le_mul_of_nonpos_right hav h0)).trans (le_max_left _ _)

/-- One step of the enclosure: `c + v h` for `v ∈ [a, b]` and `h ∈ [l, u]`. -/
def ivStep (a b c : ℚ) (lu : ℚ × ℚ) : ℚ × ℚ :=
  (c + min (a * lu.1) (b * lu.1), c + max (a * lu.2) (b * lu.2))

/-- The enclosure of the Horner value of step `m` on `[a, b]`, for `a ≥ 0`. -/
def hornerIv (c : ℕ → ℚ) (N : ℕ) (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (c (N - 1), c (N - 1))
  | m + 1 => ivStep a b (c (N - 2 - m)) (hornerIv c N a b m)

/-- **The enclosure holds.** -/
theorem horner_iv (cr : ℕ → ℝ) (c : ℕ → ℚ) (N : ℕ) (hc : ∀ k < N, cr k = c k) (a b : ℚ)
    (ha : 0 ≤ a) (v : ℝ) (hav : (a : ℝ) ≤ v) (hvb : v ≤ b) :
    ∀ m, m + 1 ≤ N → ((hornerIv c N a b m).1 : ℝ) ≤ horner cr N 0 v m ∧
      horner cr N 0 v m ≤ (hornerIv c N a b m).2 := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [show horner cr N 0 v 0 = cr (N - 1) + 0 from rfl, add_zero, hc (N - 1) (by omega)]
    simp only [hornerIv]
    exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := mul_iv a b _ _ v _ (by exact_mod_cast ha) hav hvb h1 h2
    rw [show horner cr N 0 v (m + 1) = cr (N - 2 - m) + v * horner cr N 0 v m from rfl,
      hc (N - 2 - m) (by omega)]
    simp only [hornerIv, ivStep]
    push_cast
    constructor <;> linarith

/-- The uniform subintervals cover `[0, X]`. -/
theorem piece_cover (X : ℝ) (P : ℕ) (v : ℝ) (h0 : 0 ≤ v) :
    ∀ k : ℕ, 0 < k → v ≤ X * k / P → ∃ p < k, X * p / P ≤ v ∧ v ≤ X * (p + 1) / P := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hv
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, by omega, by simp [h0], ?_⟩
      simpa using hv
    · by_cases hc : v ≤ X * k / P
      · obtain ⟨p, hp, h1, h2⟩ := ih hk hc
        exact ⟨p, by omega, h1, h2⟩
      · refine ⟨k, by omega, le_of_lt (not_le.mp hc), ?_⟩
        push_cast at hv
        exact hv

/-- The powers `2^-k` of a list of integer exponents. -/
def pz (l : List ℤ) : List ℚ := l.map fun k => if 0 ≤ k then 1 / 2 ^ k.toNat else 2 ^ (-k).toNat

theorem pz_nonneg (l : List ℤ) (m : ℕ) : 0 ≤ (pz l).getD m 0 := by
  induction l generalizing m with
  | nil => simp [pz]
  | cons a t ih =>
    cases m with
    | zero =>
      simp only [pz, List.map_cons, List.getD_cons_zero]
      split <;> positivity
    | succ m => simpa only [pz, List.map_cons, List.getD_cons_succ] using ih m

/-- The coefficients of `polyDD` at `o` in `tab`, as rationals. -/
def cq (tab : Array UInt64) (o : ℕ) (k : ℕ) : ℚ :=
  PolyBound.ratOfWord tab[o + 2 * k]! + PolyBound.ratOfWord tab[o + 2 * k + 1]!

/-- The conditions of `polyDD_steps` with the Horner values enclosed on `P` subintervals of
`[0, X]`, for the double-double point `xh + xl` with `|xh| ≤ Xh` and `|xl| ≤ Xl`. -/
def stepsIvOk (tab : Array UInt64) (o N P : ℕ) (X Xh Xl : ℚ) (C Cl E Λ K : List ℚ) : Bool :=
  decide (0 < P) && decide (0 ≤ X) && decide (Xh + Xl ≤ 1) &&
  (List.range N).all (fun k => Wasm.IEEE64.isFinite tab[o + 2 * k]! &&
    Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * k]!) ≤ C.getD k 0) &&
    decide (PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * k + 1]!) ≤ Cl.getD k 0) &&
    decide (C.getD k 0 ≤ 2 ^ 797) && decide (Cl.getD k 0 ≤ 2 ^ 797)) &&
  decide (Cl.getD (N - 1) 0 / 2 ^ 53 ≤ E.getD 0 0) &&
  decide (Cl.getD (N - 1) 0 * (1 + 1 / 2 ^ 53) ≤ Λ.getD 0 0) &&
  (List.range (N - 1)).all (fun m =>
    decide (K.getD m 0 ≤ 2 ^ 797) && decide (Λ.getD m 0 ≤ 2 ^ 797) &&
    decide ((Xh + Xl) * E.getD m 0 + epsQ Xh Xl (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
      (Cl.getD (N - 2 - m) 0) ≤ E.getD (m + 1) 0) &&
    decide (growQ Xh Xl (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) ≤
      Λ.getD (m + 1) 0)) &&
  (List.range P).all (fun p =>
    (List.range (N - 1)).all (fun m =>
      decide (max (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).1)
          (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).2) +
          E.getD m 0 + Λ.getD m 0 ≤ K.getD m 0) &&
      decide ((max (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).1)
          (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).2) +
          E.getD m 0 + Λ.getD m 0) * (X * (p + 1) / P + Xl) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]!))))

/-- The exact Horner value of the kernel at `o` is the polynomial of its pairs. -/
theorem horner_dd_tab (tab : Array UInt64) (o' : UInt64) (o N : ℕ) (ho : o'.toNat = o) (hN : 1 ≤ N)
    (hf : ∀ k < N, Wasm.IEEE64.isFinite tab[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! = true) (w : ℝ) :
    horner (cDD tab o') N 0 w (N - 1) = PolyBound.eval (LgammaApprox.ddCoeffs tab o N) w := by
  rw [horner_eval _ N hN, zero_mul, add_zero,
    show LgammaApprox.ddCoeffs tab o N = (List.range N).map (fun k =>
      LgammaApprox.q tab (o + 2 * k) + LgammaApprox.q tab (o + 2 * k + 1)) from rfl,
    eval_map_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [cDD_rat tab o' k (by rw [ho]; exact (hf k hk).1) (by rw [ho]; exact (hf k hk).2), ho]
  rfl

/-- The check at one point `0 ≤ v ≤ X`: the enclosure of the subinterval that holds `v` bounds
the Horner value of every step, and the product of that bound with `|xh| ≤ v + Xl` stays below
the coefficient. -/
theorem iv_at (tab : Array UInt64) (o' : UInt64) (o N P : ℕ) (ho : o'.toNat = o) (X Xl : ℚ)
    (E Λ K : List ℚ) (hE0 : ∀ m, 0 ≤ E.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0) (hP : 0 < P)
    (hf : ∀ k < N, Wasm.IEEE64.isFinite tab[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! = true)
    (hiv : ∀ p < P, ∀ m < N - 1,
      max (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).1)
          (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).2) +
          E.getD m 0 + Λ.getD m 0 ≤ K.getD m 0 ∧
      (max (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).1)
          (PolyBound.qabs (hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m).2) +
          E.getD m 0 + Λ.getD m 0) * (X * (p + 1) / P + Xl) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        PolyBound.qabs (PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]!))
    (v : ℝ) (hv0 : 0 ≤ v) (hvX : v ≤ X) (xh : ℝ) (hxh : |xh| ≤ v + Xl) :
    ∀ m, m + 2 ≤ N →
      |horner (cDD tab o') N 0 v m| + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) ≤ (K.getD m 0 : ℝ) ∧
      (|horner (cDD tab o') N 0 v m| + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ)) * |xh| *
          (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |((PolyBound.ratOfWord tab[o + 2 * (N - 2 - m)]! : ℚ) : ℝ)| := by
  intro m hm
  obtain ⟨p, hp, hpa, hpb⟩ := piece_cover (X : ℝ) P v hv0 P hP
    (by rw [mul_div_assoc, div_self (by exact_mod_cast hP.ne'), mul_one]; exact hvX)
  have hc : ∀ k < N, cDD tab o' k = (cq tab o k : ℝ) := fun k hk => by
    rw [cDD_rat tab o' k (by rw [ho]; exact (hf k hk).1) (by rw [ho]; exact (hf k hk).2), ho]; rfl
  have hX0 : (0 : ℝ) ≤ X := by
    have := hv0.trans hvX
    exact this
  have ha : (0 : ℚ) ≤ X * p / P := by
    have : (0 : ℚ) ≤ X := by exact_mod_cast hX0
    positivity
  obtain ⟨h1, h2⟩ := horner_iv (cDD tab o') (cq tab o) N hc (X * p / P) (X * (p + 1) / P) ha v
    (by push_cast; exact hpa) (by push_cast; exact hpb) m (by omega)
  obtain ⟨hk, hd⟩ := hiv p hp m (by omega)
  set I := hornerIv (cq tab o) N (X * p / P) (X * (p + 1) / P) m
  have hk' := (Rat.cast_le (K := ℝ)).mpr hk
  have hd' := (Rat.cast_le (K := ℝ)).mpr hd
  push_cast at hk' hd'
  simp only [Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast] at hk' hd'
  have hE' : (0 : ℝ) ≤ E.getD m 0 := Rat.cast_nonneg.mpr (hE0 m)
  have hΛ' : (0 : ℝ) ≤ Λ.getD m 0 := Rat.cast_nonneg.mpr (hΛ0 m)
  have hM : |horner (cDD tab o') N 0 v m| ≤ max |(I.1 : ℝ)| |(I.2 : ℝ)| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (I.1 : ℝ)
      have := le_max_left |(I.1 : ℝ)| |(I.2 : ℝ)|
      linarith
    · have := le_abs_self (I.2 : ℝ)
      have := le_max_right |(I.1 : ℝ)| |(I.2 : ℝ)|
      linarith
  have hxb : |xh| ≤ (X : ℝ) * (p + 1) / P + Xl := by linarith
  have hS := mul_le_mul (show |horner (cDD tab o') N 0 v m| + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) ≤
      max |(I.1 : ℝ)| |(I.2 : ℝ)| + (E.getD m 0 : ℝ) + (Λ.getD m 0 : ℝ) by linarith) hxb
    (abs_nonneg _) (by linarith [(abs_nonneg (I.1 : ℝ)).trans (le_max_left _ |(I.2 : ℝ)|)])
  have h3 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
  exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
/-- **A kernel from its interval check**: `polyDD` at a double-double `xh + xl` in `[0, X]` within
`E (N - 1)` of the polynomial of its pairs, with the low part at most `Λ (N - 1)`. -/
theorem kern_iv (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (o N P : ℕ) (X Xh Xl : ℚ)
    (C Cl E Λ K : List ℚ) (hok : stepsIvOk tab o N P X Xh Xl C Cl E Λ K = true)
    (hE0 : ∀ m, 0 ≤ E.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0)
    (o' n' : UInt64) (ho : o'.toNat = o) (hn : n'.toNat = N) (hN1 : 1 ≤ N)
    (hon : o + 2 * N < 2 ^ 63) (xh xl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hXh : |value xh.toBits| ≤ (Xh : ℝ)) (hXl : |value xl.toBits| ≤ (Xl : ℝ))
    (hv0 : 0 ≤ value xh.toBits + value xl.toBits) (hvX : value xh.toBits + value xl.toBits ≤ X) :
    Finite (Lgamma.polyDD tab o' n' xh xl 0.0).1.toBits ∧
      Finite (Lgamma.polyDD tab o' n' xh xl 0.0).2.toBits ∧
      |value (Lgamma.polyDD tab o' n' xh xl 0.0).1.toBits +
          value (Lgamma.polyDD tab o' n' xh xl 0.0).2.toBits -
          PolyBound.eval (LgammaApprox.ddCoeffs tab o N) (value xh.toBits + value xl.toBits)| ≤
        (E.getD (N - 1) 0 : ℝ) ∧
      |value (Lgamma.polyDD tab o' n' xh xl 0.0).2.toBits| ≤ (Λ.getD (N - 1) 0 : ℝ) := by
  simp only [stepsIvOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hP, -⟩, hX1⟩, hw⟩, hE00⟩, hΛ00⟩, hs⟩, hiv⟩ := hok
  have hfin : ∀ k < N, Wasm.IEEE64.isFinite tab[o + 2 * k]! = true ∧
      Wasm.IEEE64.isFinite tab[o + 2 * k + 1]! = true := fun k hk => (hw k hk).1.1.1.1
  have z0 := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_finite
  have zv := Library.Numerics.Float64.Tgamma.TgammaMainRed.zero_value
  have hval : ∀ k < N, value (Float.ofBits tab[o + 2 * k]!).toBits =
      ((PolyBound.ratOfWord tab[o + 2 * k]! : ℚ) : ℝ) ∧
      value (Float.ofBits tab[o + 2 * k + 1]!).toBits =
        ((PolyBound.ratOfWord tab[o + 2 * k + 1]! : ℚ) : ℝ) := fun k hk =>
    ⟨ofBits_value _ (hfin k hk).1, ofBits_value _ (hfin k hk).2⟩
  have hxb : |value xh.toBits| ≤ (value xh.toBits + value xl.toBits) + Xl := by
    have h1 := abs_sub (value xh.toBits + value xl.toBits) (value xl.toBits)
    rw [add_sub_cancel_right, abs_of_nonneg hv0] at h1
    linarith
  have hI := iv_at tab o' o N P ho X Xl E Λ K hE0 hΛ0 hP hfin hiv _ hv0 hvX _ hxb
  obtain ⟨h1, h2, h3, h4⟩ := polyDD_steps hF tab o' n' xh xl 0.0 (by rw [hn]; exact hN1)
    (by rw [ho, hn]; exact hon)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).1)
    (fun k hk => by rw [ho]; rw [hn] at hk; exact ofBits_finite _ (hfin k hk).2)
    (Xh : ℝ) (Xl : ℝ) 0 0 0 0 (fun k => (C.getD k 0 : ℝ)) (fun k => (Cl.getD k 0 : ℝ))
    (fun k => (E.getD k 0 : ℝ)) (fun k => (Λ.getD k 0 : ℝ)) (fun k => (K.getD k 0 : ℝ))
    hxh hxl hXh hXl (by exact_mod_cast hX1)
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
    (by rw [hn]; simp only [zero_add]; exact_mod_cast hE00)
    (by
      rw [hn]; simp only [zero_add]
      have := (Rat.cast_le (K := ℝ)).mpr hΛ00
      push_cast at this ⊢
      linarith)
    (fun m hm => by rw [hn] at hm ⊢; exact (hI m hm).1)
    (fun m hm => by
      rw [hn] at hm
      exact ⟨by exact_mod_cast (hs m (by omega)).1.1.1,
        by exact_mod_cast (hs m (by omega)).1.1.2⟩)
    (fun m hm => by
      rw [hn] at hm ⊢
      rw [ho, (hval (N - 2 - m) (by omega)).1]
      exact (hI m hm).2)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).1.2
      have hc : ((((Xh + Xl) * E.getD m 0 + epsQ Xh Xl (K.getD m 0) (Λ.getD m 0)
          (C.getD (N - 2 - m) 0) (Cl.getD (N - 2 - m) 0) : ℚ)) : ℝ) ≤ (E.getD (m + 1) 0 : ℝ) := by
        exact_mod_cast this
      rw [epsS_cast]
      push_cast at hc ⊢
      exact hc)
    (fun m hm => by
      rw [hn] at hm ⊢
      have := (hs m (by omega)).2
      have hc : ((growQ Xh Xl (K.getD m 0) (Λ.getD m 0) (C.getD (N - 2 - m) 0)
          (Cl.getD (N - 2 - m) 0) : ℚ) : ℝ) ≤ (Λ.getD (m + 1) 0 : ℝ) := by exact_mod_cast this
      rw [growS_cast]
      exact hc)
  rw [hn, horner_dd_tab tab o' o N ho hN1 hfin] at h3
  rw [hn] at h4
  exact ⟨h1, h2, h3, h4⟩

#print axioms kern_iv

end Library.Numerics.Float64.Lgamma.LgammaPolyIv
