import LeanExe.ProofKit.BesselEnergy
import LeanExe.ProofKit.PolyCalc

/-!
Bounds on `P` and `Q` over `[2, ∞)` from a chain of polynomial approximations, for any pair of
functions that satisfies the system `P'' = 2 Q' - (κ/x ^ 2) P`, `Q'' = -2 P' - (κ/x ^ 2) Q`.

A `Piece` approximates `(P, Q)` on `[a, b] ⊆ [c - H, c + H]` by polynomials `A` and `B` in
`h = x - c`.  Its residuals `r₁ = A'' - 2 B' + (κ/x ^ 2) A` and `r₂ = B'' + 2 A' + (κ/x ^ 2) B`
are `res1 / x ^ 2` and `res2 / x ^ 2` for polynomials `res1` and `res2` in `h`, so
`|r₁| + |r₂| ≤ residBound` on the piece.  The energy of the error grows by at most
`residBound · (x - a)` across the piece (`BesselEnergy`), and at the boundary with the next piece
by at most `jumpBound`, the size of the difference of the two approximations there, because the
square root of the energy is a weighted Euclidean norm.  `chainCheck` computes these bounds over
a list of pieces from a bound at the first point, and `chainCheck_sound` turns its acceptance into
the bound on every piece.  An `AsymPiece` approximates `(P, Q)` on `[X, ∞)` by polynomials in
`t = 1/x`; its residuals are `O (t ^ (m + 2))`, whose integral to `∞` is `O (X ^ -(m + 1))`.

Order 0 has `κ = 1/4 ≥ 0` and uses `energy0`; order 1 has `κ = -3/4` and uses `energy1`.
-/

namespace LeanExe.ProofKit.BesselChain

open Real Set PolyBound PolyChecks PolyCalc PolyCalculus BesselEnergy AsinRemainder TaylorRemainder

/-- The system of the large-argument functions, for `x > 0`. -/
def PQSystem (κ : ℝ) (P Q Pd Qd : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → HasDerivAt P (Pd x) x ∧ HasDerivAt Q (Qd x) x ∧
    HasDerivAt Pd (2 * Qd x - κ / x ^ 2 * P x) x ∧ HasDerivAt Qd (-2 * Pd x - κ / x ^ 2 * Q x) x

/-- Polynomial approximations `A` and `B` in `x - c` on `[a, b] ⊆ [c - H, c + H]`. -/
structure Piece where
  a : ℚ
  b : ℚ
  c : ℚ
  H : ℚ
  A : List ℚ
  B : List ℚ

namespace Piece

noncomputable def fA (pc : Piece) (x : ℝ) : ℝ := eval pc.A (x - pc.c)
noncomputable def fB (pc : Piece) (x : ℝ) : ℝ := eval pc.B (x - pc.c)
noncomputable def fA1 (pc : Piece) (x : ℝ) : ℝ := eval (derivP pc.A) (x - pc.c)
noncomputable def fB1 (pc : Piece) (x : ℝ) : ℝ := eval (derivP pc.B) (x - pc.c)
noncomputable def fA2 (pc : Piece) (x : ℝ) : ℝ := eval (derivP (derivP pc.A)) (x - pc.c)
noncomputable def fB2 (pc : Piece) (x : ℝ) : ℝ := eval (derivP (derivP pc.B)) (x - pc.c)

/-- The conditions on the interval. -/
def ok (pc : Piece) : Bool :=
  decide (0 < pc.a ∧ pc.a ≤ pc.b ∧ pc.c - pc.H ≤ pc.a ∧ pc.b ≤ pc.c + pc.H)

theorem hasDerivAt_shift (p : List ℚ) (c : ℚ) (x : ℝ) :
    HasDerivAt (fun y => eval p (y - c)) (eval (derivP p) (x - c)) x := by
  have h := (hasDerivAt_eval p (x - c)).comp x ((hasDerivAt_id' x).sub_const (c : ℝ))
  rw [mul_one] at h
  exact h

end Piece

/-- `(c + X) ^ 2`. -/
def sqAt (c : ℚ) : List ℚ := [c * c, 2 * c, 1]

theorem eval_sqAt (c : ℚ) (x : ℝ) : eval (sqAt c) (x - c) = x ^ 2 := by
  simp [sqAt]; ring

/-- `x ^ 2 (A'' - 2 B') + κ A` as a polynomial in `x - c`. -/
def res1 (κ : ℚ) (pc : Piece) : List ℚ :=
  addP (mulP (sqAt pc.c) (subP (derivP (derivP pc.A)) (scaleP 2 (derivP pc.B)))) (scaleP κ pc.A)

/-- `x ^ 2 (B'' + 2 A') + κ B` as a polynomial in `x - c`. -/
def res2 (κ : ℚ) (pc : Piece) : List ℚ :=
  addP (mulP (sqAt pc.c) (addP (derivP (derivP pc.B)) (scaleP 2 (derivP pc.A)))) (scaleP κ pc.B)

/-- The bound on `|r₁| + |r₂|` over the piece. -/
def residBound (κ : ℚ) (pc : Piece) : ℚ :=
  (absSum pc.H (res1 κ pc) + absSum pc.H (res2 κ pc)) / (pc.a * pc.a)

theorem residBound_nonneg (κ : ℚ) (pc : Piece) (hH : 0 ≤ pc.H) : (0 : ℝ) ≤ residBound κ pc := by
  have h1 := absSum_nonneg pc.H hH (res1 κ pc)
  have h2 := absSum_nonneg pc.H hH (res2 κ pc)
  rw [residBound]
  push_cast
  exact div_nonneg (add_nonneg h1 h2) (mul_self_nonneg _)

theorem ok_facts {pc : Piece} (hok : pc.ok = true) :
    (0 : ℝ) < (pc.a : ℝ) ∧ (pc.a : ℝ) ≤ (pc.b : ℝ) ∧ (pc.c : ℝ) - (pc.H : ℝ) ≤ (pc.a : ℝ) ∧
      (pc.b : ℝ) ≤ (pc.c : ℝ) + (pc.H : ℝ) := by
  simp only [Piece.ok, decide_eq_true_eq] at hok
  obtain ⟨h1, h2, h3, h4⟩ := hok
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

theorem resid_le (κ : ℚ) (pc : Piece) (hok : pc.ok = true) (x : ℝ)
    (hx : x ∈ Icc (pc.a : ℝ) pc.b) :
    |pc.fA2 x - 2 * pc.fB1 x + κ / x ^ 2 * pc.fA x| +
      |pc.fB2 x + 2 * pc.fA1 x + κ / x ^ 2 * pc.fB x| ≤ ((residBound κ pc : ℚ) : ℝ) := by
  obtain ⟨ha, hab, hca, hbc⟩ := ok_facts hok
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hH : (0 : ℝ) ≤ pc.H := by linarith [hx.1, hx.2]
  have hHq : (0 : ℚ) ≤ pc.H := by exact_mod_cast hH
  have hxc : |x - pc.c| ≤ ((pc.H : ℚ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have e1 : pc.fA2 x - 2 * pc.fB1 x + κ / x ^ 2 * pc.fA x = eval (res1 κ pc) (x - pc.c) / x ^ 2 := by
    simp only [res1, eval_addP, eval_mulP, eval_subP, eval_scaleP, eval_sqAt, Piece.fA2,
      Piece.fB1, Piece.fA]
    field_simp
    push_cast
    ring
  have e2 : pc.fB2 x + 2 * pc.fA1 x + κ / x ^ 2 * pc.fB x = eval (res2 κ pc) (x - pc.c) / x ^ 2 := by
    simp only [res2, eval_addP, eval_mulP, eval_scaleP, eval_sqAt, Piece.fB2, Piece.fA1,
      Piece.fB]
    field_simp
    push_cast
    ring
  have b1 := abs_eval_le pc.H hHq (res1 κ pc) (x - pc.c) hxc
  have b2 := abs_eval_le pc.H hHq (res2 κ pc) (x - pc.c) hxc
  have hxa : (pc.a : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha.le hx.1 2
  simp only [e1, e2]
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < x ^ 2), residBound]
  push_cast
  rw [← add_div]
  have hs : 0 ≤ |eval (res1 κ pc) (x - pc.c)| + |eval (res2 κ pc) (x - pc.c)| := by positivity
  calc (|eval (res1 κ pc) (x - pc.c)| + |eval (res2 κ pc) (x - pc.c)|) / x ^ 2
      ≤ (|eval (res1 κ pc) (x - pc.c)| + |eval (res2 κ pc) (x - pc.c)|) / ((pc.a : ℝ) * pc.a) := by
        rw [← sq]
        exact div_le_div_of_nonneg_left hs (by positivity) hxa
    _ ≤ (((absSum pc.H (res1 κ pc) : ℚ) : ℝ) + ((absSum pc.H (res2 κ pc) : ℚ) : ℝ)) /
          ((pc.a : ℝ) * pc.a) := by
        gcongr

/-- The errors of a piece form an `ErrorSystem`. -/
theorem errorSystem (κ : ℚ) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd) (pc : Piece)
    (ha : (0 : ℝ) < pc.a) :
    ErrorSystem κ pc.a pc.b (fun x => P x - pc.fA x) (fun x => Q x - pc.fB x)
      (fun x => Pd x - pc.fA1 x) (fun x => Qd x - pc.fB1 x)
      (fun x => pc.fA2 x - 2 * pc.fB1 x + κ / x ^ 2 * pc.fA x)
      (fun x => pc.fB2 x + 2 * pc.fA1 x + κ / x ^ 2 * pc.fB x) where
  pos := ha
  hp x hx := by
    obtain ⟨h1, -, -, -⟩ := hsys x (lt_of_lt_of_le ha hx.1)
    exact h1.sub (Piece.hasDerivAt_shift pc.A pc.c x)
  hq x hx := by
    obtain ⟨-, h2, -, -⟩ := hsys x (lt_of_lt_of_le ha hx.1)
    exact h2.sub (Piece.hasDerivAt_shift pc.B pc.c x)
  hp' x hx := by
    obtain ⟨-, -, h3, -⟩ := hsys x (lt_of_lt_of_le ha hx.1)
    refine (h3.sub (Piece.hasDerivAt_shift (derivP pc.A) pc.c x)).congr_deriv ?_
    simp only [Piece.fA, Piece.fB1, Piece.fA2]
    ring
  hq' x hx := by
    obtain ⟨-, -, -, h4⟩ := hsys x (lt_of_lt_of_le ha hx.1)
    refine (h4.sub (Piece.hasDerivAt_shift (derivP pc.B) pc.c x)).congr_deriv ?_
    simp only [Piece.fB, Piece.fA1, Piece.fB2]
    ring

/-- The square root of the energy of the errors of an approximation `(fA, fB)` with derivatives
`(fA1, fB1)` at `x`, order 0. -/
noncomputable def root0 (κ : ℝ) (P Q Pd Qd fA fB fA1 fB1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  √(energy0 κ x (P x - fA x) (Q x - fB x) (Pd x - fA1 x) (Qd x - fB1 x))

/-- The same for order 1. -/
noncomputable def root1 (κ : ℝ) (P Q Pd Qd fA fB fA1 fB1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  √(energy1 κ x (P x - fA x) (Q x - fB x) (Pd x - fA1 x) (Qd x - fB1 x))

/-- The energy root of a piece, order 0. -/
noncomputable abbrev rootE0 (κ : ℝ) (P Q Pd Qd : ℝ → ℝ) (pc : Piece) : ℝ → ℝ :=
  root0 κ P Q Pd Qd pc.fA pc.fB pc.fA1 pc.fB1

/-- The energy root of a piece, order 1. -/
noncomputable abbrev rootE1 (κ : ℝ) (P Q Pd Qd : ℝ → ℝ) (pc : Piece) : ℝ → ℝ :=
  root1 κ P Q Pd Qd pc.fA pc.fB pc.fA1 pc.fB1

theorem piece_bound0 (κ : ℚ) (hκ : 0 ≤ κ) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (pc : Piece) (hok : pc.ok = true) :
    ∀ x ∈ Icc (pc.a : ℝ) pc.b,
      rootE0 κ P Q Pd Qd pc x ≤ rootE0 κ P Q Pd Qd pc pc.a + residBound κ pc * (x - pc.a) := by
  obtain ⟨ha, -, -, -⟩ := ok_facts hok
  have hκ' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  intro x hx
  have h := energy0_bound (errorSystem κ hsys pc ha) hκ'
    (G := fun y => (residBound κ pc : ℝ) * y) (g := fun _ => (residBound κ pc : ℝ))
    (fun y _ => by simpa using (hasDerivAt_id' y).const_mul (residBound κ pc : ℝ))
    (fun y hy => resid_le κ pc hok y hy) x hx
  simp only [rootE0, root0]
  linarith

theorem piece_bound1 (κ : ℚ) (hκ : κ ≤ 0) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (pc : Piece) (hok : pc.ok = true) (hm : 81 / 100 ≤ 1 + κ / (pc.a * pc.a)) :
    ∀ x ∈ Icc (pc.a : ℝ) pc.b,
      rootE1 κ P Q Pd Qd pc x ≤
        rootE1 κ P Q Pd Qd pc pc.a + 10 / 9 * residBound κ pc * (x - pc.a) := by
  obtain ⟨ha, -, -, -⟩ := ok_facts hok
  have hκ' : (κ : ℝ) ≤ 0 := by exact_mod_cast hκ
  have hm' : ((81 / 100 : ℚ) : ℝ) ≤ ((1 + κ / (pc.a * pc.a) : ℚ) : ℝ) := by exact_mod_cast hm
  push_cast at hm'
  intro x hx
  have hmx : ∀ y ∈ Icc (pc.a : ℝ) pc.b, (81 / 100 : ℝ) ≤ 1 + κ / y ^ 2 := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have h1 : (pc.a : ℝ) * pc.a ≤ y ^ 2 := by nlinarith [hy.1]
    have h2 : κ / ((pc.a : ℝ) * pc.a) ≤ κ / y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonpos_left h1 hκ'
    linarith
  have h := energy1_bound (errorSystem κ hsys pc ha) hκ' hmx
    (G := fun y => (10 / 9 * residBound κ pc : ℝ) * y) (g := fun _ => (10 / 9 * residBound κ pc : ℝ))
    (fun y _ => by simpa using (hasDerivAt_id' y).const_mul (10 / 9 * residBound κ pc : ℝ))
    (fun y hy => by have := resid_le κ pc hok y hy; linarith) x hx
  simp only [rootE1, root1]
  linarith

/-! Jumps between approximations. -/

theorem sqrt_sum4_add (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℝ) :
    √((a₁ + b₁) ^ 2 + (a₂ + b₂) ^ 2 + (a₃ + b₃) ^ 2 + (a₄ + b₄) ^ 2) ≤
      √(a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) + (|b₁| + |b₂| + |b₃| + |b₄|) := by
  set S := √(a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2)
  set T := |b₁| + |b₂| + |b₃| + |b₄|
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hT : 0 ≤ T := by positivity
  have hS2 : S ^ 2 = a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 := Real.sq_sqrt (by positivity)
  have hai : ∀ a : ℝ, a ^ 2 ≤ S ^ 2 → |a| ≤ S := fun a h => by
    rw [← Real.sqrt_sq hS] ; exact Real.abs_le_sqrt h
  have h1 := hai a₁ (by nlinarith [sq_nonneg a₂, sq_nonneg a₃, sq_nonneg a₄])
  have h2 := hai a₂ (by nlinarith [sq_nonneg a₁, sq_nonneg a₃, sq_nonneg a₄])
  have h3 := hai a₃ (by nlinarith [sq_nonneg a₂, sq_nonneg a₁, sq_nonneg a₄])
  have h4 := hai a₄ (by nlinarith [sq_nonneg a₂, sq_nonneg a₃, sq_nonneg a₁])
  have hab : ∀ a b : ℝ, |a| ≤ S → a * b ≤ S * |b| := fun a b h => by
    calc a * b ≤ |a * b| := le_abs_self _
      _ = |a| * |b| := abs_mul a b
      _ ≤ S * |b| := mul_le_mul_of_nonneg_right h (abs_nonneg b)
  have hb2 : b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + b₄ ^ 2 ≤ T ^ 2 := by
    have e1 := sq_abs b₁; have e2 := sq_abs b₂; have e3 := sq_abs b₃; have e4 := sq_abs b₄
    nlinarith [abs_nonneg b₁, abs_nonneg b₂, abs_nonneg b₃, abs_nonneg b₄,
      mul_nonneg (abs_nonneg b₁) (abs_nonneg b₂), mul_nonneg (abs_nonneg b₁) (abs_nonneg b₃),
      mul_nonneg (abs_nonneg b₁) (abs_nonneg b₄), mul_nonneg (abs_nonneg b₂) (abs_nonneg b₃),
      mul_nonneg (abs_nonneg b₂) (abs_nonneg b₄), mul_nonneg (abs_nonneg b₃) (abs_nonneg b₄)]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [hab a₁ b₁ h1, hab a₂ b₂ h2, hab a₃ b₃ h3, hab a₄ b₄ h4]

theorem energy0_shift (κ x p q p' q' jp jq jp' jq' s : ℝ) (hm : 0 ≤ 1 + κ / x ^ 2) (hs : 0 ≤ s)
    (hs2 : 1 + κ / x ^ 2 ≤ s ^ 2) :
    √(energy0 κ x (p + jp) (q + jq) (p' + jp') (q' + jq')) ≤
      √(energy0 κ x p q p' q') + (|jp' - jq| + |jq' + jp| + s * (|jp| + |jq|)) := by
  set r := √(1 + κ / x ^ 2)
  have hr2 : r ^ 2 = 1 + κ / x ^ 2 := Real.sq_sqrt hm
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrs : r ≤ s := by rw [← Real.sqrt_sq hs]; exact Real.sqrt_le_sqrt hs2
  have e1 : energy0 κ x (p + jp) (q + jq) (p' + jp') (q' + jq') =
      ((p' - q) + (jp' - jq)) ^ 2 + ((q' + p) + (jq' + jp)) ^ 2 + (r * p + r * jp) ^ 2 +
        (r * q + r * jq) ^ 2 := by
    unfold energy0; rw [← hr2]; ring
  have e2 : energy0 κ x p q p' q' = (p' - q) ^ 2 + (q' + p) ^ 2 + (r * p) ^ 2 + (r * q) ^ 2 := by
    unfold energy0; rw [← hr2]; ring
  rw [e1, e2]
  refine (sqrt_sum4_add _ _ _ _ _ _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hr]
  have : r * |jp| + r * |jq| ≤ s * (|jp| + |jq|) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_right hrs (by positivity)
  linarith

theorem energy1_shift (κ x p q p' q' jp jq jp' jq' s : ℝ) (hm : 0 < 1 + κ / x ^ 2) (hs : 0 ≤ s)
    (hs2 : 1 ≤ (1 + κ / x ^ 2) * s ^ 2) :
    √(energy1 κ x (p + jp) (q + jq) (p' + jp') (q' + jq')) ≤
      √(energy1 κ x p q p' q') + (s * (|jp' - jq| + |jq' + jp|) + (|jp| + |jq|)) := by
  set r := √(1 + κ / x ^ 2)
  have hr2 : r ^ 2 = 1 + κ / x ^ 2 := Real.sq_sqrt hm.le
  have hr : 0 < r := Real.sqrt_pos.mpr hm
  have hrs : 1 / r ≤ s := by
    rw [div_le_iff₀ hr]
    have : 1 ≤ (r * s) ^ 2 := by rw [mul_pow, hr2]; exact hs2
    have hrs0 : 0 ≤ r * s := mul_nonneg hr.le hs
    nlinarith [hrs0, this]
  have e1 : energy1 κ x (p + jp) (q + jq) (p' + jp') (q' + jq') =
      ((p' - q) / r + (jp' - jq) / r) ^ 2 + ((q' + p) / r + (jq' + jp) / r) ^ 2 + (p + jp) ^ 2 +
        (q + jq) ^ 2 := by
    unfold energy1; rw [← hr2]; field_simp; ring
  have e2 : energy1 κ x p q p' q' = ((p' - q) / r) ^ 2 + ((q' + p) / r) ^ 2 + p ^ 2 + q ^ 2 := by
    unfold energy1; rw [← hr2]; field_simp
  rw [e1, e2]
  refine (sqrt_sum4_add _ _ _ _ _ _ _ _).trans ?_
  rw [abs_div, abs_div, abs_of_pos hr]
  have : |jp' - jq| / r + |jq' + jp| / r ≤ s * (|jp' - jq| + |jq' + jp|) := by
    rw [← add_div, div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hrs (by positivity)
  linarith

/-- The size of the difference of two approximations at the rational point `x`, order 0. -/
def jumpBound0 (s x : ℚ) (pc pc' : Piece) : ℚ :=
  let jp := evalQ pc.A (x - pc.c) - evalQ pc'.A (x - pc'.c)
  let jq := evalQ pc.B (x - pc.c) - evalQ pc'.B (x - pc'.c)
  let jp' := evalQ (derivP pc.A) (x - pc.c) - evalQ (derivP pc'.A) (x - pc'.c)
  let jq' := evalQ (derivP pc.B) (x - pc.c) - evalQ (derivP pc'.B) (x - pc'.c)
  qabs (jp' - jq) + qabs (jq' + jp) + s * (qabs jp + qabs jq)

/-- The same for order 1. -/
def jumpBound1 (s x : ℚ) (pc pc' : Piece) : ℚ :=
  let jp := evalQ pc.A (x - pc.c) - evalQ pc'.A (x - pc'.c)
  let jq := evalQ pc.B (x - pc.c) - evalQ pc'.B (x - pc'.c)
  let jp' := evalQ (derivP pc.A) (x - pc.c) - evalQ (derivP pc'.A) (x - pc'.c)
  let jq' := evalQ (derivP pc.B) (x - pc.c) - evalQ (derivP pc'.B) (x - pc'.c)
  s * (qabs (jp' - jq) + qabs (jq' + jp)) + (qabs jp + qabs jq)

theorem jump0 (κ : ℚ) (P Q Pd Qd : ℝ → ℝ) (s x : ℚ) (pc pc' : Piece)
    (hm : (0 : ℝ) ≤ 1 + κ / (x : ℝ) ^ 2) (hs : 0 ≤ s) (hs2 : (1 : ℝ) + κ / (x : ℝ) ^ 2 ≤ (s : ℝ) ^ 2) :
    rootE0 κ P Q Pd Qd pc' x ≤ rootE0 κ P Q Pd Qd pc x + jumpBound0 s x pc pc' := by
  have h := energy0_shift κ x (P x - pc.fA x) (Q x - pc.fB x) (Pd x - pc.fA1 x) (Qd x - pc.fB1 x)
    (pc.fA x - pc'.fA x) (pc.fB x - pc'.fB x) (pc.fA1 x - pc'.fA1 x) (pc.fB1 x - pc'.fB1 x) s hm
    (by exact_mod_cast hs) hs2
  simp only [rootE0, root0]
  rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [jumpBound0, Piece.fA, Piece.fB, Piece.fA1, Piece.fB1]
  push_cast [qabs_cast, evalQ_cast]
  ring

theorem jump1 (κ : ℚ) (P Q Pd Qd : ℝ → ℝ) (s x : ℚ) (pc pc' : Piece)
    (hm : (0 : ℝ) < 1 + κ / (x : ℝ) ^ 2) (hs : 0 ≤ s)
    (hs2 : (1 : ℝ) ≤ (1 + κ / (x : ℝ) ^ 2) * (s : ℝ) ^ 2) :
    rootE1 κ P Q Pd Qd pc' x ≤ rootE1 κ P Q Pd Qd pc x + jumpBound1 s x pc pc' := by
  have h := energy1_shift κ x (P x - pc.fA x) (Q x - pc.fB x) (Pd x - pc.fA1 x) (Qd x - pc.fB1 x)
    (pc.fA x - pc'.fA x) (pc.fB x - pc'.fB x) (pc.fA1 x - pc'.fA1 x) (pc.fB1 x - pc'.fB1 x) s hm
    (by exact_mod_cast hs) hs2
  simp only [rootE1, root1]
  rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [jumpBound1, Piece.fA, Piece.fB, Piece.fA1, Piece.fB1]
  push_cast [qabs_cast, evalQ_cast]
  ring

#print axioms resid_le
#print axioms piece_bound0
#print axioms piece_bound1
#print axioms jump0
#print axioms jump1

end LeanExe.ProofKit.BesselChain
