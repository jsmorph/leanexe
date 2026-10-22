import Library.Numerics.Float64.Erfc.ErfcOps

/-!
Error tracking for the proof of `Erfc.erfc`.  `Tr x v M e` states that the float `x` is finite,
lies within `e` of the real number `v`, and `|v| ≤ M`.  `Pr h l V M L e` states that the
double-double `(h, l)` is finite, that `h + l` lies within `e` of `V`, that `|V| ≤ M`, and that
`|l| ≤ L`.  Each lemma bounds one operation or one step of `Erfc` from the bounds of its operands.
The result's bounds are parameters, and the inequalities that justify them are hypotheses, so that
an application to concrete coefficients needs only rational inequalities.  The magnitudes stay below
`2 ^ 20`, far from overflow.

The steps are those of `Erfc.erfFastMain`: `pr_fts` is `fast_two_sum` of two floats, `pr_add` adds a
float to a double-double, and `pr_mulB`, `pr_mulC`, and `pr_mulD` multiply a double-double by an
exact float `z` and add a coefficient, in the three orders of the code.
-/

namespace Library.Numerics.Float64.Erfc.ErfcTrack

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcEft2 Library.Numerics.Arithmetic.Fma.FmaSpec

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

/-- The float `x` is finite and lies within `e` of `v`, and `|v| ≤ M`. -/
def Tr (x : Float) (v M e : ℝ) : Prop := ff x ∧ |fv x - v| ≤ e ∧ |v| ≤ M

/-- The double-double `(h, l)` is finite, `h + l` lies within `e` of `V`, `|V| ≤ M`, and
`|l| ≤ L`. -/
def Pr (h l : Float) (V M L e : ℝ) : Prop :=
  ff h ∧ ff l ∧ |fv h + fv l - V| ≤ e ∧ |V| ≤ M ∧ |fv l| ≤ L

theorem Tr.e_nonneg {x : Float} {v M e : ℝ} (h : Tr x v M e) : 0 ≤ e :=
  (abs_nonneg _).trans h.2.1

theorem Tr.M_nonneg {x : Float} {v M e : ℝ} (h : Tr x v M e) : 0 ≤ M :=
  (abs_nonneg _).trans h.2.2

theorem Tr.abs_le {x : Float} {v M e : ℝ} (h : Tr x v M e) : |fv x| ≤ M + e := by
  have := abs_sub_abs_le_abs_sub (fv x) v
  linarith [h.2.1, h.2.2]

theorem Tr.mono {x : Float} {v M e M' e' : ℝ} (h : Tr x v M e) (hM : M ≤ M') (he : e ≤ e') :
    Tr x v M' e' :=
  ⟨h.1, h.2.1.trans he, h.2.2.trans hM⟩

theorem tr_exact (x : Float) (hx : ff x) (M : ℝ) (hM : |fv x| ≤ M) : Tr x (fv x) M 0 :=
  ⟨hx, by simp, hM⟩

theorem Pr.e_nonneg {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) : 0 ≤ e :=
  (abs_nonneg _).trans hp.2.2.1

theorem Pr.L_nonneg {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) : 0 ≤ L :=
  (abs_nonneg _).trans hp.2.2.2.2

theorem Pr.M_nonneg {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) : 0 ≤ M :=
  (abs_nonneg _).trans hp.2.2.2.1

theorem Pr.h_le {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) : |fv h| ≤ M + e + L := by
  obtain ⟨-, -, he, hM, hL⟩ := hp
  have : fv h = (fv h + fv l - V) + V - fv l := by ring
  rw [this]
  calc _ ≤ |fv h + fv l - V + V| + |fv l| := abs_sub_le' _ _
    _ ≤ |fv h + fv l - V| + |V| + |fv l| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem Pr.h_ge {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) : |V| - e - L ≤ |fv h| := by
  obtain ⟨-, -, he, -, hL⟩ := hp
  have : V = fv h + fv l - (fv h + fv l - V) := by ring
  have h1 : |V| ≤ |fv h| + |fv l| + |fv h + fv l - V| := by
    calc |V| = |fv h + fv l - (fv h + fv l - V)| := by rw [← this]
      _ ≤ |fv h + fv l| + |fv h + fv l - V| := abs_sub_le' _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  linarith

theorem Pr.mono {h l : Float} {V M L e M' L' e' : ℝ} (hp : Pr h l V M L e) (hM : M ≤ M')
    (hL : L ≤ L') (he : e ≤ e') : Pr h l V M' L' e' :=
  ⟨hp.1, hp.2.1, hp.2.2.1.trans he, hp.2.2.2.1.trans hM, hp.2.2.2.2.trans hL⟩

theorem abs_add3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)

theorem tr_add {a b : Float} {va vb Ma Mb ea eb : ℝ} (ha : Tr a va Ma ea) (hb : Tr b vb Mb eb)
    (M e : ℝ) (hM : Ma + Mb ≤ M) (he : ea + eb + u * (M + ea + eb) ≤ e)
    (hov : M + ea + eb ≤ 2 ^ 1000) : Tr (a + b) (va + vb) M e := by
  have hab : |fv a + fv b| ≤ M + ea + eb :=
    (abs_add_le _ _).trans (by linarith [ha.abs_le, hb.abs_le])
  obtain ⟨hf, herr⟩ := add_f a b ha.1 hb.1 (hab.trans (hov.trans (by norm_num)))
  refine ⟨hf, ?_, (abs_add_le _ _).trans (by linarith [ha.2.2, hb.2.2])⟩
  have e1 : fv (a + b) - (va + vb) = (fv (a + b) - (fv a + fv b)) + (fv a - va) + (fv b - vb) := by
    ring
  rw [e1]
  have : u * |fv a + fv b| ≤ u * (M + ea + eb) := by gcongr
  linarith [abs_add3 (fv (a + b) - (fv a + fv b)) (fv a - va) (fv b - vb), ha.2.1, hb.2.1]

theorem tr_sub {a b : Float} {va vb Ma Mb ea eb : ℝ} (ha : Tr a va Ma ea) (hb : Tr b vb Mb eb)
    (M e : ℝ) (hM : Ma + Mb ≤ M) (he : ea + eb + u * (M + ea + eb) ≤ e)
    (hov : M + ea + eb ≤ 2 ^ 1000) : Tr (a - b) (va - vb) M e := by
  have hab : |fv a - fv b| ≤ M + ea + eb :=
    (abs_sub_le' _ _).trans (by linarith [ha.abs_le, hb.abs_le])
  obtain ⟨hf, herr⟩ := sub_f a b ha.1 hb.1 (hab.trans (hov.trans (by norm_num)))
  refine ⟨hf, ?_, (abs_sub_le' _ _).trans (by linarith [ha.2.2, hb.2.2])⟩
  have e1 : fv (a - b) - (va - vb) =
      (fv (a - b) - (fv a - fv b)) + (fv a - va) + -(fv b - vb) := by ring
  rw [e1]
  have : u * |fv a - fv b| ≤ u * (M + ea + eb) := by gcongr
  have := abs_add3 (fv (a - b) - (fv a - fv b)) (fv a - va) (-(fv b - vb))
  rw [abs_neg] at this
  linarith [ha.2.1, hb.2.1]

theorem prod_err {fa fb va vb Ma Mb ea eb : ℝ} (ha : |fa - va| ≤ ea) (hb : |fb - vb| ≤ eb)
    (hMa : |va| ≤ Ma) (hMb : |vb| ≤ Mb) :
    |fa * fb - va * vb| ≤ ea * Mb + Ma * eb + ea * eb := by
  have e1 : fa * fb - va * vb = (fa - va) * vb + va * (fb - vb) + (fa - va) * (fb - vb) := by ring
  rw [e1]
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha
  refine (abs_add3 _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul]
  gcongr
  · exact (abs_nonneg _).trans hMa

theorem prod_mag {fa fb Ma Mb ea eb : ℝ} (ha : |fa| ≤ Ma + ea) (hb : |fb| ≤ Mb + eb) :
    |fa * fb| ≤ (Ma + ea) * (Mb + eb) := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem tr_mul {a b : Float} {va vb Ma Mb ea eb : ℝ} (ha : Tr a va Ma ea) (hb : Tr b vb Mb eb)
    (M e : ℝ) (hM : Ma * Mb ≤ M)
    (he : ea * Mb + Ma * eb + ea * eb + u * ((Ma + ea) * (Mb + eb)) + η ≤ e)
    (hov : (Ma + ea) * (Mb + eb) ≤ 2 ^ 1000) : Tr (a * b) (va * vb) M e := by
  have hab := prod_mag ha.abs_le hb.abs_le
  obtain ⟨hf, herr⟩ := mul_f a b ha.1 hb.1 (hab.trans (hov.trans (by norm_num)))
  refine ⟨hf, ?_, ?_⟩
  · have e1 : fv (a * b) - va * vb = (fv (a * b) - fv a * fv b) + (fv a * fv b - va * vb) := by
      ring
    rw [e1]
    have h2 := prod_err ha.2.1 hb.2.1 ha.2.2 hb.2.2
    have : u * |fv a * fv b| ≤ u * ((Ma + ea) * (Mb + eb)) := by gcongr
    linarith [abs_add_le (fv (a * b) - fv a * fv b) (fv a * fv b - va * vb)]
  · rw [abs_mul]
    exact (mul_le_mul ha.2.2 hb.2.2 (abs_nonneg _) ha.M_nonneg).trans hM

theorem tr_fma (hF : FmaNearest) {a b c : Float} {va vb vc Ma Mb Mc ea eb ec : ℝ}
    (ha : Tr a va Ma ea) (hb : Tr b vb Mb eb) (hc : Tr c vc Mc ec) (M e : ℝ)
    (hM : Ma * Mb + Mc ≤ M)
    (he : ea * Mb + Ma * eb + ea * eb + ec + u * ((Ma + ea) * (Mb + eb) + Mc + ec) + η ≤ e)
    (hov : (Ma + ea) * (Mb + eb) + Mc + ec ≤ 2 ^ 1000) :
    Tr (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) (va * vb + vc) M e := by
  have hab := prod_mag ha.abs_le hb.abs_le
  have habc : |fv a * fv b + fv c| ≤ (Ma + ea) * (Mb + eb) + Mc + ec :=
    (abs_add_le _ _).trans (by linarith [hc.abs_le])
  obtain ⟨hf, herr⟩ := fma_f hF a b c ha.1 hb.1 hc.1 (habc.trans (hov.trans (by norm_num)))
  refine ⟨hf, ?_, ?_⟩
  · have e1 : fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) - (va * vb + vc) = (fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) - (fv a * fv b + fv c)) +
        (fv a * fv b - va * vb) + (fv c - vc) := by ring
    rw [e1]
    have h2 := prod_err ha.2.1 hb.2.1 ha.2.2 hb.2.2
    have : u * |fv a * fv b + fv c| ≤ u * ((Ma + ea) * (Mb + eb) + Mc + ec) := by gcongr
    linarith [abs_add3 (fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) - (fv a * fv b + fv c)) (fv a * fv b - va * vb)
      (fv c - vc), hc.2.1]
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul ha.2.2 hb.2.2 (abs_nonneg _) ha.M_nonneg
    linarith [hc.2.2]

theorem tr_neg {a : Float} {va M e : ℝ} (ha : Tr a va M e) : Tr (-a) (-va) M e := by
  obtain ⟨hf, hv⟩ := neg_f a ha.1
  refine ⟨hf, ?_, by rw [abs_neg]; exact ha.2.2⟩
  rw [hv, show -fv a - -va = -(fv a - va) by ring, abs_neg]
  exact ha.2.1

theorem fts_fst (a b : Float) : (Erfc.fastTwoSum a b).1 = a + b := rfl

/-- A rounded sum of two bounded floats. -/
theorem add_bound {p q : Float} {P Q : ℝ} (hp : ff p) (hq : ff q) (hP : |fv p| ≤ P)
    (hQ : |fv q| ≤ Q) (hov : P + Q ≤ 2 ^ 1000) :
    ff (p + q) ∧ |fv (p + q) - (fv p + fv q)| ≤ u * (P + Q) ∧ |fv (p + q)| ≤ (P + Q) * (1 + u) := by
  have hpq : |fv p + fv q| ≤ P + Q := (abs_add_le _ _).trans (by linarith)
  obtain ⟨hf, herr⟩ := add_f p q hp hq (hpq.trans (hov.trans (by norm_num)))
  have h1 : u * |fv p + fv q| ≤ u * (P + Q) := by gcongr
  refine ⟨hf, herr.trans h1, ?_⟩
  have : fv (p + q) = (fv (p + q) - (fv p + fv q)) + (fv p + fv q) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- A rounded fused multiply-add of three bounded floats. -/
theorem fma_bound (hF : FmaNearest) {a b c : Float} {A B C : ℝ} (ha : ff a) (hb : ff b)
    (hc : ff c) (hA : |fv a| ≤ A) (hB : |fv b| ≤ B) (hC : |fv c| ≤ C) (hov : A * B + C ≤ 2 ^ 1000) :
    ff (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) ∧ |fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) - (fv a * fv b + fv c)| ≤ u * (A * B + C) + η ∧
      |fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c)| ≤ (A * B + C) * (1 + u) + η := by
  have hab : |fv a * fv b| ≤ A * B := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) ((abs_nonneg _).trans hA)
  have habc : |fv a * fv b + fv c| ≤ A * B + C := (abs_add_le _ _).trans (by linarith)
  obtain ⟨hf, herr⟩ := fma_f hF a b c ha hb hc (habc.trans (hov.trans (by norm_num)))
  have h1 : u * |fv a * fv b + fv c| ≤ u * (A * B + C) := by gcongr
  refine ⟨hf, herr.trans (by linarith), ?_⟩
  have : fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) = (fv (Library.Numerics.Arithmetic.Fma.Fma.fma a b c) - (fv a * fv b + fv c)) + (fv a * fv b + fv c) := by
    ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- `aMul z h` for `|z| ≤ R` and `|h| ≤ H`: the high part, the low part, and their sum. -/
theorem amul_bound (hF : FmaNearest) {z h : Float} {R H : ℝ} (hz : ff z) (hh : ff h)
    (hzR : |fv z| ≤ R) (hhH : |fv h| ≤ H) (hov : R * H ≤ 2 ^ 1000) :
    ff (Erfc.aMul z h).1 ∧ ff (Erfc.aMul z h).2 ∧
      |fv (Erfc.aMul z h).1| ≤ R * H * (1 + u) + η ∧
      |fv (Erfc.aMul z h).2| ≤ u * u * (R * H) + 2 * η + (u * (R * H) + η) ∧
      |fv (Erfc.aMul z h).1 + fv (Erfc.aMul z h).2 - fv z * fv h| ≤ u * u * (R * H) + 2 * η := by
  have hzh : |fv z * fv h| ≤ R * H := by
    rw [abs_mul]; exact mul_le_mul hzR hhH (abs_nonneg _) ((abs_nonneg _).trans hzR)
  obtain ⟨h1, h2, he1, he2⟩ := aMul_f hF z h hz hh (hzh.trans (hov.trans (by norm_num)))
  have hu : (0 : ℝ) ≤ u := by positivity
  have k1 : u * |fv z * fv h| ≤ u * (R * H) := by gcongr
  have k2 : u * u * |fv z * fv h| ≤ u * u * (R * H) := by gcongr
  refine ⟨h1, h2, ?_, ?_, he2.trans (by linarith)⟩
  · have : fv (Erfc.aMul z h).1 = (fv (Erfc.aMul z h).1 - fv z * fv h) + fv z * fv h := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith
  · have : fv (Erfc.aMul z h).2 = (fv (Erfc.aMul z h).1 + fv (Erfc.aMul z h).2 - fv z * fv h) -
        (fv (Erfc.aMul z h).1 - fv z * fv h) := by ring
    rw [this]
    refine (abs_sub_le' _ _).trans ?_
    linarith

/-- `fast_two_sum a b` for `|b| ≤ |a|`: the exact sum and the bound on the error term. -/
theorem fts_bound {a b : Float} {A B : ℝ} (ha : ff a) (hb : ff b) (hA : |fv a| ≤ A)
    (hB : |fv b| ≤ B) (hpre : |fv b| ≤ |fv a|) (hov : A + B ≤ 2 ^ 1000) :
    ff (Erfc.fastTwoSum a b).1 ∧ ff (Erfc.fastTwoSum a b).2 ∧
      fv (Erfc.fastTwoSum a b).1 + fv (Erfc.fastTwoSum a b).2 = fv a + fv b ∧
      |fv (Erfc.fastTwoSum a b).2| ≤ u * (A + B) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have k : (2 : ℝ) ^ 1000 ≤ 2 ^ 1020 := by norm_num
  obtain ⟨h1, h2, hsum, -⟩ := fastTwoSum_f a b ha hb hpre (hA.trans (by linarith))
  obtain ⟨-, herr, -⟩ := add_bound ha hb hA hB hov
  refine ⟨h1, h2, hsum, ?_⟩
  have ht : fv (Erfc.fastTwoSum a b).2 = -(fv (a + b) - (fv a + fv b)) := by
    rw [← fts_fst]; linarith
  rw [ht, abs_neg]
  exact herr

/-- `fast_two_sum` of two floats whose first dominates. -/
theorem pr_fts {a b : Float} {va vb Ma Mb ea eb : ℝ} (ha : Tr a va Ma ea) (hb : Tr b vb Mb eb)
    (ma : ℝ) (hma : ma ≤ |va|) (hpre : Mb + eb + ea ≤ ma) (M L : ℝ) (hM : Ma + Mb ≤ M)
    (hL : u * (M + ea + eb) ≤ L) (hov : M + ea + eb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a b).1 (Erfc.fastTwoSum a b).2 (va + vb) M L (ea + eb) := by
  have hfa : |va| - ea ≤ |fv a| := by
    have := abs_sub_abs_le_abs_sub va (fv a)
    rw [abs_sub_comm] at this
    linarith [ha.2.1]
  have hba : |fv b| ≤ |fv a| := by linarith [hb.abs_le]
  obtain ⟨h1, h2, hsum, ht⟩ := fts_bound ha.1 hb.1 ha.abs_le hb.abs_le hba
    (by linarith [hb.M_nonneg, ha.e_nonneg, hb.e_nonneg])
  refine ⟨h1, h2, ?_, (abs_add_le _ _).trans (by linarith [ha.2.2, hb.2.2]), ?_⟩
  · rw [hsum, show fv a + fv b - (va + vb) = (fv a - va) + (fv b - vb) by ring]
    exact (abs_add_le _ _).trans (by linarith [ha.2.1, hb.2.1])
  · refine ht.trans (le_trans ?_ hL)
    have : (0 : ℝ) ≤ u := by positivity
    have : Ma + ea + (Mb + eb) ≤ M + ea + eb := by linarith
    gcongr

/-- `(h, l) + b`: `fast_two_sum (h, b)` with its error term added to `l`. -/
theorem pr_add {h l b : Float} {V vb M L e Mb eb : ℝ} (hp : Pr h l V M L e)
    (hb : Tr b vb Mb eb) (mV : ℝ) (hmV : mV ≤ |V|) (hpre : Mb + eb + e + L ≤ mV)
    (M' L' e' T : ℝ) (hM : M + Mb ≤ M') (hT : u * (M + e + L + (Mb + eb)) ≤ T)
    (hL : (L + T) * (1 + u) ≤ L') (he : e + eb + u * (L + T) ≤ e')
    (hov : M + e + L + Mb + eb + T ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum h b).1 (l + (Erfc.fastTwoSum h b).2) (V + vb) M' L' e' := by
  have hh := hp.h_le
  have hhg := hp.h_ge
  have hba : |fv b| ≤ |fv h| := by linarith [hb.abs_le]
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have heb := hb.e_nonneg
  have hMb := hb.M_nonneg
  have hM0 := hp.M_nonneg
  have hT0 : 0 ≤ T := le_trans (mul_nonneg (by norm_num) (by linarith)) hT
  obtain ⟨h1, h2, hsum, ht⟩ := fts_bound hp.1 hb.1 hh hb.abs_le hba (by linarith)
  have hT' : |fv (Erfc.fastTwoSum h b).2| ≤ T := ht.trans hT
  obtain ⟨hf, herr, hmag⟩ := add_bound hp.2.1 h2 hp.2.2.2.2 hT' (by linarith)
  refine ⟨h1, hf, ?_, (abs_add_le _ _).trans (by linarith [hp.2.2.2.1, hb.2.2]), hmag.trans hL⟩
  have e1 : fv (Erfc.fastTwoSum h b).1 + fv (l + (Erfc.fastTwoSum h b).2) - (V + vb) =
      (fv h + fv l - V) + (fv b - vb) +
        (fv (l + (Erfc.fastTwoSum h b).2) - (fv l + fv (Erfc.fastTwoSum h b).2)) := by
    linarith
  rw [e1]
  linarith [abs_add3 (fv h + fv l - V) (fv b - vb)
    (fv (l + (Erfc.fastTwoSum h b).2) - (fv l + fv (Erfc.fastTwoSum h b).2)), hp.2.2.1, hb.2.1]

/-- `a + z (h, l)` in the order of the third stage of `cr_erf_fast`: the product's error term and
`z l` by one `fma`, then the error of `fast_two_sum`. -/
theorem pr_mulB (hF : FmaNearest) {z a h l : Float} {V M L e R Ma ma : ℝ} (hz : ff z)
    (hzR : |fv z| ≤ R) (ha : ff a) (hMa : |fv a| ≤ Ma) (hma : ma ≤ |fv a|)
    (hp : Pr h l V M L e) (H Th Ttl W M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : R * H * (1 + u) + η ≤ Th) (hpre : Th ≤ ma)
    (hTtl : u * u * (R * H) + 2 * η + (u * (R * H) + η) ≤ Ttl)
    (hW : (R * L + Ttl) * (1 + u) + η ≤ W) (hM : Ma + R * M ≤ M')
    (hL : (u * (Ma + Th) + W) * (1 + u) ≤ L')
    (he : R * e + (u * u * (R * H) + 2 * η) + (u * (R * L + Ttl) + η) +
      u * (u * (Ma + Th) + W) ≤ e')
    (hov : Ma + Th + R * H + R * L + Ttl + W ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a (Erfc.aMul z h).1).1
      ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2)
      (fv a + fv z * V) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hRH : 0 ≤ R * H := mul_nonneg hR0 hH0
  have hRL : 0 ≤ R * L := mul_nonneg hR0 hL0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hz hp.1 hzR hhH (by linarith)
  have hth : |fv (Erfc.aMul z h).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul z h).2| ≤ Ttl := mtl.trans hTtl
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound ha m1 hMa hth (hth.trans (hpre.trans hma))
    (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hz hp.2.1 m2 hzR hp.2.2.2.2 htl (by linarith)
  have hw : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2)| ≤ W := wmag.trans hW
  obtain ⟨s1, serr, smag⟩ := add_bound f2 w1 ft hw (by nlinarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).1 +
        fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) -
          (fv a + fv z * V) =
        (fv (Erfc.aMul z h).1 + fv (Erfc.aMul z h).2 - fv z * fv h) +
          (fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) - (fv z * fv l + fv (Erfc.aMul z h).2)) +
          (fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) -
            (fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2))) +
          fv z * (fv h + fv l - V) := by
      linear_combination fsum
    rw [e1]
    have hzV : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have := abs_add3 (fv (Erfc.aMul z h).1 + fv (Erfc.aMul z h).2 - fv z * fv h)
      (fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) - (fv z * fv l + fv (Erfc.aMul z h).2))
      (fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) -
        (fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2)))
    have := abs_add_le
      (fv (Erfc.aMul z h).1 + fv (Erfc.aMul z h).2 - fv z * fv h +
        (fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) - (fv z * fv l + fv (Erfc.aMul z h).2)) +
        (fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2) -
          (fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2))))
      (fv z * (fv h + fv l - V))
    have k1 : u * (R * L + Ttl) + η ≥ u * (R * L + Ttl) + η := le_refl _
    have k2 : u * (u * (Ma + Th) + W) ≥ u * (u * (Ma + Th) + W) := le_refl _
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hzR hp.2.2.2.1 (abs_nonneg _) hR0
    linarith

/-- `(a + b) + z (h, l)` in the order of the second stage of `cr_erf_fast`: `z l + b` by one `fma`,
added to the product's error term, then to the error of `fast_two_sum`. -/
theorem pr_mulC (hF : FmaNearest) {z a b h l : Float} {V M L e R Ma ma Mb : ℝ} (hz : ff z)
    (hzR : |fv z| ≤ R) (ha : ff a) (hMa : |fv a| ≤ Ma) (hma : ma ≤ |fv a|) (hb : ff b)
    (hMb : |fv b| ≤ Mb) (hp : Pr h l V M L e) (H Th Ttl W Vb M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : R * H * (1 + u) + η ≤ Th) (hpre : Th ≤ ma)
    (hTtl : u * u * (R * H) + 2 * η + (u * (R * H) + η) ≤ Ttl)
    (hW : (R * L + Mb) * (1 + u) + η ≤ W) (hVb : (Ttl + W) * (1 + u) ≤ Vb)
    (hM : Ma + Mb + R * M ≤ M') (hL : (u * (Ma + Th) + Vb) * (1 + u) ≤ L')
    (he : R * e + (u * u * (R * H) + 2 * η) + (u * (R * L + Mb) + η) + u * (Ttl + W) +
      u * (u * (Ma + Th) + Vb) ≤ e')
    (hov : Ma + Th + R * H + R * L + Mb + Ttl + W + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a (Erfc.aMul z h).1).1
      ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + ((Erfc.aMul z h).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l b))
      (fv a + fv b + fv z * V) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hMb
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hRH : 0 ≤ R * H := mul_nonneg hR0 hH0
  have hRL : 0 ≤ R * L := mul_nonneg hR0 hL0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hz hp.1 hzR hhH (by linarith)
  have hth : |fv (Erfc.aMul z h).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul z h).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound ha m1 hMa hth (hth.trans (hpre.trans hma))
    (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hz hp.2.1 hb hzR hp.2.2.2.2 hMb (by linarith)
  have hw : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l b)| ≤ W := wmag.trans hW
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  obtain ⟨v1, verr, vmag⟩ := add_bound m2 w1 htl hw (by linarith)
  have hv : |fv ((Erfc.aMul z h).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l b)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hut : u * (Ma + Th) ≤ Ma + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 v1 ft hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul z h).1
    set tl := fv (Erfc.aMul z h).2
    set t := fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).2
    set w := fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l b)
    set v := fv ((Erfc.aMul z h).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l b)
    set lo := fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + ((Erfc.aMul z h).2 + Library.Numerics.Arithmetic.Fma.Fma.fma z l b))
    have e1 : fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).1 + lo - (fv a + fv b + fv z * V) =
        (th + tl - fv z * fv h) + (w - (fv z * fv l + fv b)) + (v - (tl + w)) + (lo - (t + v)) +
          fv z * (fv h + fv l - V) := by
      linear_combination fsum
    rw [e1]
    have hzV : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (th + tl - fv z * fv h) (w - (fv z * fv l + fv b)) (v - (tl + w))
    have k2 := abs_add3 (th + tl - fv z * fv h + (w - (fv z * fv l + fv b)) + (v - (tl + w)))
      (lo - (t + v)) (fv z * (fv h + fv l - V))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hzR hp.2.2.2.1 (abs_nonneg _) hR0
    have := abs_add_le (fv a) (fv b)
    linarith

/-- `(a + b) + z (h, l)` in the order of the first stage of `cr_erf_fast`: the product's error term
plus `z l` by one `fma`, plus `b`, then the error of `fast_two_sum`. -/
theorem pr_mulD (hF : FmaNearest) {z a b h l : Float} {V M L e R Ma ma Mb : ℝ} (hz : ff z)
    (hzR : |fv z| ≤ R) (ha : ff a) (hMa : |fv a| ≤ Ma) (hma : ma ≤ |fv a|) (hb : ff b)
    (hMb : |fv b| ≤ Mb) (hp : Pr h l V M L e) (H Th Ttl W Vb M' L' e' : ℝ) (hH : M + e + L ≤ H)
    (hTh : R * H * (1 + u) + η ≤ Th) (hpre : Th ≤ ma)
    (hTtl : u * u * (R * H) + 2 * η + (u * (R * H) + η) ≤ Ttl)
    (hW : (R * L + Ttl) * (1 + u) + η ≤ W) (hVb : (W + Mb) * (1 + u) ≤ Vb)
    (hM : Ma + Mb + R * M ≤ M') (hL : (u * (Ma + Th) + Vb) * (1 + u) ≤ L')
    (he : R * e + (u * u * (R * H) + 2 * η) + (u * (R * L + Ttl) + η) + u * (W + Mb) +
      u * (u * (Ma + Th) + Vb) ≤ e')
    (hov : Ma + Th + R * H + R * L + Mb + Ttl + W + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum a (Erfc.aMul z h).1).1
      ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2 + b))
      (fv a + fv b + fv z * V) M' L' e' := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hzR
  have hL0 := hp.L_nonneg
  have hM0 := hp.M_nonneg
  have he0 := hp.e_nonneg
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hMb
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hRH : 0 ≤ R * H := mul_nonneg hR0 hH0
  have hRL : 0 ≤ R * L := mul_nonneg hR0 hL0
  have hu : (0 : ℝ) ≤ u := by positivity
  have hη : (0 : ℝ) ≤ η := by positivity
  obtain ⟨m1, m2, mth, mtl, msum⟩ := amul_bound hF hz hp.1 hzR hhH (by linarith)
  have hth : |fv (Erfc.aMul z h).1| ≤ Th := mth.trans hTh
  have htl : |fv (Erfc.aMul z h).2| ≤ Ttl := mtl.trans hTtl
  have hTh0 : 0 ≤ Th := (abs_nonneg _).trans hth
  have hTtl0 : 0 ≤ Ttl := (abs_nonneg _).trans htl
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound ha m1 hMa hth (hth.trans (hpre.trans hma))
    (by linarith)
  obtain ⟨w1, werr, wmag⟩ := fma_bound hF hz hp.2.1 m2 hzR hp.2.2.2.2 htl (by linarith)
  have hw : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2)| ≤ W := wmag.trans hW
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hw
  obtain ⟨v1, verr, vmag⟩ := add_bound w1 hb hw hMb (by linarith)
  have hv : |fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2 + b)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hut : u * (Ma + Th) ≤ Ma + Th := by
    have : u ≤ 1 := by norm_num
    nlinarith
  obtain ⟨s1, serr, smag⟩ := add_bound f2 v1 ft hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · set th := fv (Erfc.aMul z h).1
    set tl := fv (Erfc.aMul z h).2
    set t := fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).2
    set w := fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2)
    set v := fv (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2 + b)
    set lo := fv ((Erfc.fastTwoSum a (Erfc.aMul z h).1).2 + (Library.Numerics.Arithmetic.Fma.Fma.fma z l (Erfc.aMul z h).2 + b))
    have e1 : fv (Erfc.fastTwoSum a (Erfc.aMul z h).1).1 + lo - (fv a + fv b + fv z * V) =
        (th + tl - fv z * fv h) + (w - (fv z * fv l + tl)) + (v - (w + fv b)) + (lo - (t + v)) +
          fv z * (fv h + fv l - V) := by
      linear_combination fsum
    rw [e1]
    have hzV : |fv z * (fv h + fv l - V)| ≤ R * e := by
      rw [abs_mul]; exact mul_le_mul hzR hp.2.2.1 (abs_nonneg _) hR0
    have k1 := abs_add3 (th + tl - fv z * fv h) (w - (fv z * fv l + tl)) (v - (w + fv b))
    have k2 := abs_add3 (th + tl - fv z * fv h + (w - (fv z * fv l + tl)) + (v - (w + fv b)))
      (lo - (t + v)) (fv z * (fv h + fv l - V))
    linarith
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hzR hp.2.2.2.1 (abs_nonneg _) hR0
    have := abs_add_le (fv a) (fv b)
    linarith

#print axioms tr_fma
#print axioms pr_fts
#print axioms pr_add
#print axioms pr_mulB
#print axioms pr_mulC
#print axioms pr_mulD

end Library.Numerics.Float64.Erfc.ErfcTrack
