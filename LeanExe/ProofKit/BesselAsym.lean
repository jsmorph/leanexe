import LeanExe.ProofKit.BesselChain

/-!
The last approximation of the chain in `BesselChain`, on `[X, ∞)`, and the induction over the
pieces.

An `AsymPiece` approximates `(P, Q)` by polynomials `A` and `B` in `t = 1/x`, the truncated
asymptotic series.  Its residuals are `t ^ 2 eval asymRes1 t` and `t ^ 2 eval asymRes2 t`; when
the kernel finds the coefficients of `asymRes1` and `asymRes2` below degree `m` to be zero, their
sum is at most `K t ^ (m + 2)` on `[X, ∞)`, whose integral from `X` is at most
`K X ^ -(m + 1) / (m + 1)`, the `asymTail`.

`chain0` and `chain1` check a list of pieces followed by a last piece: each piece is `ok`, each
ends where the next starts, and the bound at the start of each piece plus its residual's
integral stays below `δ`, with the bound at the next start increased by the jump.  `chainEnd0`
and `chainEnd1` give the bound at the end of the last piece.
-/

namespace LeanExe.ProofKit.BesselChain

open Real Set PolyBound PolyChecks PolyCalc BesselEnergy AsinRemainder TaylorRemainder

/-- Polynomial approximations `A` and `B` in `t = 1/x` on `[X, ∞)`. -/
structure AsymPiece where
  X : ℚ
  A : List ℚ
  B : List ℚ
  m : ℕ

namespace AsymPiece

noncomputable def fA (ap : AsymPiece) (x : ℝ) : ℝ := eval ap.A (1 / x)
noncomputable def fB (ap : AsymPiece) (x : ℝ) : ℝ := eval ap.B (1 / x)
noncomputable def fA1 (ap : AsymPiece) (x : ℝ) : ℝ := -(1 / x) ^ 2 * eval (derivP ap.A) (1 / x)
noncomputable def fB1 (ap : AsymPiece) (x : ℝ) : ℝ := -(1 / x) ^ 2 * eval (derivP ap.B) (1 / x)
noncomputable def fA2 (ap : AsymPiece) (x : ℝ) : ℝ :=
  2 * (1 / x) ^ 3 * eval (derivP ap.A) (1 / x) + (1 / x) ^ 4 * eval (derivP (derivP ap.A)) (1 / x)
noncomputable def fB2 (ap : AsymPiece) (x : ℝ) : ℝ :=
  2 * (1 / x) ^ 3 * eval (derivP ap.B) (1 / x) + (1 / x) ^ 4 * eval (derivP (derivP ap.B)) (1 / x)

theorem hasDerivAt_inv' (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x) ^ 2) x := by
  have h := hasDerivAt_inv hx
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp)
  field_simp

theorem hasDerivAt_comp (p : List ℚ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => eval p (1 / y)) (-(1 / x) ^ 2 * eval (derivP p) (1 / x)) x := by
  have h := (hasDerivAt_eval p (1 / x)).comp x (hasDerivAt_inv' x hx)
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_comp1 (p : List ℚ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => -(1 / y) ^ 2 * eval (derivP p) (1 / y))
      (2 * (1 / x) ^ 3 * eval (derivP p) (1 / x) + (1 / x) ^ 4 * eval (derivP (derivP p)) (1 / x)) x := by
  have h := (((hasDerivAt_inv' x hx).pow 2).neg).mul (hasDerivAt_comp (derivP p) x hx)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.pow_apply])
  simp only [Pi.neg_apply, Pi.pow_apply]
  push_cast
  ring

end AsymPiece

/-- `t ^ 2 A'' + 2 t A' + 2 B' + κ A` in `t`, which is `x ^ 2 r₁`. -/
def asymRes1 (κ : ℚ) (ap : AsymPiece) : List ℚ :=
  addP (addP (mulP [0, 0, 1] (derivP (derivP ap.A))) (scaleP 2 (mulP [0, 1] (derivP ap.A))))
    (addP (scaleP 2 (derivP ap.B)) (scaleP κ ap.A))

/-- `t ^ 2 B'' + 2 t B' - 2 A' + κ B` in `t`, which is `x ^ 2 r₂`. -/
def asymRes2 (κ : ℚ) (ap : AsymPiece) : List ℚ :=
  addP (addP (mulP [0, 0, 1] (derivP (derivP ap.B))) (scaleP 2 (mulP [0, 1] (derivP ap.B))))
    (addP (scaleP (-2) (derivP ap.A)) (scaleP κ ap.B))

/-- The conditions: `X > 0` and no terms below degree `m` in either residual. -/
def AsymPiece.ok (κ : ℚ) (ap : AsymPiece) : Bool :=
  decide (0 < ap.X) && ((asymRes1 κ ap).take ap.m).all (fun a => decide (a = 0)) &&
    ((asymRes2 κ ap).take ap.m).all (fun a => decide (a = 0))

/-- `K` with `|r₁| + |r₂| ≤ K t ^ (m + 2)`. -/
def asymK (κ : ℚ) (ap : AsymPiece) : ℚ :=
  absSum (1 / ap.X) ((asymRes1 κ ap).drop ap.m) + absSum (1 / ap.X) ((asymRes2 κ ap).drop ap.m)

/-- The integral of the residual bound from `X` to `∞`. -/
def asymTail (κ : ℚ) (ap : AsymPiece) : ℚ := asymK κ ap / (ap.m + 1) * (1 / ap.X) ^ (ap.m + 1)

theorem asym_resid_le (κ : ℚ) (ap : AsymPiece) (hok : ap.ok κ = true) (x : ℝ) (hx : (ap.X : ℝ) ≤ x) :
    |ap.fA2 x - 2 * ap.fB1 x + κ / x ^ 2 * ap.fA x| + |ap.fB2 x + 2 * ap.fA1 x + κ / x ^ 2 * ap.fB x| ≤
      (asymK κ ap : ℝ) * (1 / x) ^ (ap.m + 2) := by
  simp only [AsymPiece.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hX, h1⟩, h2⟩ := hok
  have hX' : (0 : ℝ) < ap.X := by exact_mod_cast hX
  have hx0 : 0 < x := lt_of_lt_of_le hX' hx
  set t := 1 / x with ht
  have ht0 : 0 < t := by positivity
  have htX : |t| ≤ ((1 / ap.X : ℚ) : ℝ) := by
    rw [abs_of_pos ht0, ht]
    push_cast
    exact one_div_le_one_div_of_le hX' hx
  have hx2 : x ^ 2 = 1 / t ^ 2 := by rw [ht]; field_simp
  have e1 : ap.fA2 x - 2 * ap.fB1 x + κ / x ^ 2 * ap.fA x = t ^ 2 * eval (asymRes1 κ ap) t := by
    simp only [asymRes1, eval_addP, eval_mulP, eval_scaleP, AsymPiece.fA2, AsymPiece.fB1,
      AsymPiece.fA, eval_cons, eval_nil, ← ht, hx2]
    push_cast
    field_simp
    ring
  have e2 : ap.fB2 x + 2 * ap.fA1 x + κ / x ^ 2 * ap.fB x = t ^ 2 * eval (asymRes2 κ ap) t := by
    simp only [asymRes2, eval_addP, eval_mulP, eval_scaleP, AsymPiece.fB2, AsymPiece.fA1,
      AsymPiece.fB, eval_cons, eval_nil, ← ht, hx2]
    push_cast
    field_simp
    ring
  have hq1 : eval (asymRes1 κ ap) t = t ^ ap.m * eval ((asymRes1 κ ap).drop ap.m) t := by
    rw [eval_take_drop _ ap.m t, eval_eq_zero_of_all _ h1, zero_add]
  have hq2 : eval (asymRes2 κ ap) t = t ^ ap.m * eval ((asymRes2 κ ap).drop ap.m) t := by
    rw [eval_take_drop _ ap.m t, eval_eq_zero_of_all _ h2, zero_add]
  have hX0 : (0 : ℚ) ≤ 1 / ap.X := by positivity
  have b1 := abs_eval_le (1 / ap.X) hX0 ((asymRes1 κ ap).drop ap.m) t htX
  have b2 := abs_eval_le (1 / ap.X) hX0 ((asymRes2 κ ap).drop ap.m) t htX
  rw [e1, e2, hq1, hq2, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < t ^ 2),
    abs_of_pos (by positivity : 0 < t ^ ap.m), asymK]
  push_cast
  have hp : 0 ≤ t ^ 2 * t ^ ap.m := by positivity
  calc t ^ 2 * (t ^ ap.m * |eval ((asymRes1 κ ap).drop ap.m) t|) +
        t ^ 2 * (t ^ ap.m * |eval ((asymRes2 κ ap).drop ap.m) t|)
      = t ^ 2 * t ^ ap.m * (|eval ((asymRes1 κ ap).drop ap.m) t| +
          |eval ((asymRes2 κ ap).drop ap.m) t|) := by ring
    _ ≤ t ^ 2 * t ^ ap.m * (((absSum (1 / ap.X) ((asymRes1 κ ap).drop ap.m) : ℚ) : ℝ) +
          ((absSum (1 / ap.X) ((asymRes2 κ ap).drop ap.m) : ℚ) : ℝ)) := by gcongr
    _ = _ := by ring

theorem asym_errorSystem (κ : ℚ) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (ap : AsymPiece) (hX : (0 : ℝ) < ap.X) (b : ℝ) :
    ErrorSystem κ ap.X b (fun x => P x - ap.fA x) (fun x => Q x - ap.fB x)
      (fun x => Pd x - ap.fA1 x) (fun x => Qd x - ap.fB1 x)
      (fun x => ap.fA2 x - 2 * ap.fB1 x + κ / x ^ 2 * ap.fA x)
      (fun x => ap.fB2 x + 2 * ap.fA1 x + κ / x ^ 2 * ap.fB x) where
  pos := hX
  hp x hx := by
    have hx0 := lt_of_lt_of_le hX hx.1
    exact (hsys x hx0).1.sub (AsymPiece.hasDerivAt_comp ap.A x hx0.ne')
  hq x hx := by
    have hx0 := lt_of_lt_of_le hX hx.1
    exact (hsys x hx0).2.1.sub (AsymPiece.hasDerivAt_comp ap.B x hx0.ne')
  hp' x hx := by
    have hx0 := lt_of_lt_of_le hX hx.1
    refine ((hsys x hx0).2.2.1.sub (AsymPiece.hasDerivAt_comp1 ap.A x hx0.ne')).congr_deriv ?_
    simp only [AsymPiece.fA, AsymPiece.fB1, AsymPiece.fA2]
    ring
  hq' x hx := by
    have hx0 := lt_of_lt_of_le hX hx.1
    refine ((hsys x hx0).2.2.2.sub (AsymPiece.hasDerivAt_comp1 ap.B x hx0.ne')).congr_deriv ?_
    simp only [AsymPiece.fB, AsymPiece.fA1, AsymPiece.fB2]
    ring

/-- The antiderivative of the residual bound. -/
theorem hasDerivAt_tailG (K : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => -(K / (m + 1)) * (1 / y) ^ (m + 1)) (K * (1 / x) ^ (m + 2)) x := by
  have h := ((AsymPiece.hasDerivAt_inv' x hx).pow (m + 1)).const_mul (-(K / (m + 1)))
  refine h.congr_deriv ?_
  rw [Nat.add_sub_cancel, pow_add]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  generalize (1 / x) = u
  field_simp

theorem tail_le (K : ℝ) (hK : 0 ≤ K) (m : ℕ) (X x : ℝ) (hX : 0 < X) (hx : X ≤ x) :
    -(K / (m + 1)) * (1 / x) ^ (m + 1) - -(K / (m + 1)) * (1 / X) ^ (m + 1) ≤
      K / (m + 1) * (1 / X) ^ (m + 1) := by
  have : 0 ≤ K / (m + 1) * (1 / x) ^ (m + 1) := by
    have : (0 : ℝ) < 1 / x := by have := lt_of_lt_of_le hX hx; positivity
    positivity
  linarith

theorem asym_bound0 (κ : ℚ) (hκ : 0 ≤ κ) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (ap : AsymPiece) (hok : ap.ok κ = true) (x : ℝ) (hx : (ap.X : ℝ) ≤ x) :
    root0 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 x ≤
      root0 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 ap.X + asymTail κ ap := by
  have hX : (0 : ℝ) < ap.X := by
    simp only [AsymPiece.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact_mod_cast hok.1.1
  have hK : (0 : ℝ) ≤ asymK κ ap := by
    have hXq : (0 : ℚ) < ap.X := by exact_mod_cast hX
    rw [asymK]; push_cast
    have := absSum_nonneg (1 / ap.X) (by positivity) ((asymRes1 κ ap).drop ap.m)
    have := absSum_nonneg (1 / ap.X) (by positivity) ((asymRes2 κ ap).drop ap.m)
    positivity
  have h := energy0_bound (asym_errorSystem κ hsys ap hX x) (by exact_mod_cast hκ)
    (G := fun y => -((asymK κ ap : ℝ) / (ap.m + 1)) * (1 / y) ^ (ap.m + 1))
    (g := fun y => (asymK κ ap : ℝ) * (1 / y) ^ (ap.m + 2))
    (fun y hy => hasDerivAt_tailG _ _ y (lt_of_lt_of_le hX hy.1).ne')
    (fun y hy => asym_resid_le κ ap hok y hy.1) x ⟨hx, le_rfl⟩
  have ht := tail_le _ hK ap.m ap.X x hX hx
  simp only [root0]
  rw [asymTail]
  push_cast
  linarith

theorem asym_bound1 (κ : ℚ) (hκ : κ ≤ 0) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (ap : AsymPiece) (hok : ap.ok κ = true) (hm : 81 / 100 ≤ 1 + κ / (ap.X * ap.X)) (x : ℝ)
    (hx : (ap.X : ℝ) ≤ x) :
    root1 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 x ≤
      root1 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 ap.X + 10 / 9 * asymTail κ ap := by
  have hX : (0 : ℝ) < ap.X := by
    simp only [AsymPiece.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact_mod_cast hok.1.1
  have hK : (0 : ℝ) ≤ asymK κ ap := by
    have hXq : (0 : ℚ) < ap.X := by exact_mod_cast hX
    rw [asymK]; push_cast
    have := absSum_nonneg (1 / ap.X) (by positivity) ((asymRes1 κ ap).drop ap.m)
    have := absSum_nonneg (1 / ap.X) (by positivity) ((asymRes2 κ ap).drop ap.m)
    positivity
  have hκ' : (κ : ℝ) ≤ 0 := by exact_mod_cast hκ
  have hm' : ((81 / 100 : ℚ) : ℝ) ≤ ((1 + κ / (ap.X * ap.X) : ℚ) : ℝ) := by exact_mod_cast hm
  push_cast at hm'
  have hmx : ∀ y ∈ Icc (ap.X : ℝ) x, (81 / 100 : ℝ) ≤ 1 + κ / y ^ 2 := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hX hy.1
    have h1 : (ap.X : ℝ) * ap.X ≤ y ^ 2 := by nlinarith [hy.1]
    have h2 : κ / ((ap.X : ℝ) * ap.X) ≤ κ / y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonpos_left h1 hκ'
    linarith
  have h := energy1_bound (asym_errorSystem κ hsys ap hX x) hκ' hmx
    (G := fun y => -((10 / 9 * asymK κ ap : ℝ) / (ap.m + 1)) * (1 / y) ^ (ap.m + 1))
    (g := fun y => (10 / 9 * asymK κ ap : ℝ) * (1 / y) ^ (ap.m + 2))
    (fun y hy => hasDerivAt_tailG _ _ y (lt_of_lt_of_le hX hy.1).ne')
    (fun y hy => by
      have := asym_resid_le κ ap hok y hy.1
      have hp : (0 : ℝ) ≤ (1 / y) ^ (ap.m + 2) := by
        have := lt_of_lt_of_le hX hy.1; positivity
      nlinarith) x ⟨hx, le_rfl⟩
  have ht := tail_le (10 / 9 * asymK κ ap : ℝ) (by positivity) ap.m ap.X x hX hx
  have e : 10 / 9 * (asymK κ ap : ℝ) / (ap.m + 1) * (1 / (ap.X : ℝ)) ^ (ap.m + 1) =
      10 / 9 * ((asymK κ ap : ℝ) / (ap.m + 1) * (1 / (ap.X : ℝ)) ^ (ap.m + 1)) := by ring
  simp only [root1]
  rw [asymTail]
  push_cast
  linarith

/-! The induction over the pieces. -/

/-- The piece after `pc` in `pc :: rest ++ [last]`. -/
def nextPiece (rest : List Piece) (last : Piece) : Piece :=
  match rest with
  | [] => last
  | p :: _ => p

/-- The check of the chain `pcs ++ [last]` from the bound `β` at its start, order 0. -/
def chain0 (κ s δ : ℚ) : List Piece → Piece → ℚ → Bool
  | [], last, β => last.ok && decide (β + residBound κ last * (last.b - last.a) ≤ δ)
  | pc :: rest, last, β =>
    pc.ok && decide (pc.b = (nextPiece rest last).a) && decide (0 ≤ s) &&
      decide (1 + κ / (pc.b * pc.b) ≤ s * s) &&
      decide (β + residBound κ pc * (pc.b - pc.a) ≤ δ) &&
      chain0 κ s δ rest last
        (β + residBound κ pc * (pc.b - pc.a) + jumpBound0 s pc.b pc (nextPiece rest last))

/-- The bound at the end of the chain, order 0. -/
def chainEnd0 (κ s : ℚ) : List Piece → Piece → ℚ → ℚ
  | [], last, β => β + residBound κ last * (last.b - last.a)
  | pc :: rest, last, β =>
    chainEnd0 κ s rest last
      (β + residBound κ pc * (pc.b - pc.a) + jumpBound0 s pc.b pc (nextPiece rest last))

/-- The first piece of `pcs ++ [last]`. -/
def firstPiece (pcs : List Piece) (last : Piece) : Piece := nextPiece pcs last

theorem chain0_sound (κ : ℚ) (hκ : 0 ≤ κ) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (s δ : ℚ) (pcs : List Piece) (last : Piece) (β : ℚ) (hc : chain0 κ s δ pcs last β = true)
    (hβ : rootE0 κ P Q Pd Qd (firstPiece pcs last) (firstPiece pcs last).a ≤ β) :
    (∀ pc ∈ pcs ++ [last], ∀ x ∈ Icc (pc.a : ℝ) pc.b, rootE0 κ P Q Pd Qd pc x ≤ δ) ∧
      rootE0 κ P Q Pd Qd last last.b ≤ chainEnd0 κ s pcs last β := by
  induction pcs generalizing β with
  | nil =>
    simp only [chain0, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hok, hδ⟩ := hc
    obtain ⟨ha, hab, -, -⟩ := ok_facts hok
    have hρ := residBound_nonneg κ last (by
      have := ok_facts hok; have h3 := this.2.2.1; have h4 := this.2.2.2
      have : (0 : ℝ) ≤ last.H := by linarith
      exact_mod_cast this)
    have hpb := piece_bound0 κ hκ hsys last hok
    simp only [firstPiece, nextPiece] at hβ
    have hδ' : (β : ℝ) + residBound κ last * (last.b - last.a) ≤ δ := by exact_mod_cast hδ
    refine ⟨fun pc hpc x hx => ?_, ?_⟩
    · simp only [List.nil_append, List.mem_singleton] at hpc
      subst hpc
      have h1 := hpb x hx
      have h2 : (residBound κ pc : ℝ) * (x - pc.a) ≤ residBound κ pc * (pc.b - pc.a) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) hρ
      linarith
    · have h1 := hpb last.b ⟨hab, le_rfl⟩
      simp only [chainEnd0]
      push_cast
      linarith
  | cons pc rest ih =>
    simp only [chain0, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hok, hnext⟩, hs⟩, hs2⟩, hδ⟩, hrest⟩ := hc
    obtain ⟨ha, hab, hca, hbc⟩ := ok_facts hok
    have hρ := residBound_nonneg κ pc (by
      have : (0 : ℝ) ≤ pc.H := by linarith
      exact_mod_cast this)
    have hpb := piece_bound0 κ hκ hsys pc hok
    simp only [firstPiece, nextPiece] at hβ
    have hδ' : (β : ℝ) + residBound κ pc * (pc.b - pc.a) ≤ δ := by exact_mod_cast hδ
    have hend := hpb pc.b ⟨hab, le_rfl⟩
    have hκ' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
    have hj := jump0 κ P Q Pd Qd s pc.b pc (nextPiece rest last)
      (by have : (0 : ℝ) ≤ κ / (pc.b : ℝ) ^ 2 := by positivity
          linarith)
      hs (by
        have : ((1 + κ / (pc.b * pc.b) : ℚ) : ℝ) ≤ ((s * s : ℚ) : ℝ) := by exact_mod_cast hs2
        push_cast at this
        rw [sq, sq]
        exact this)
    have hβ' : rootE0 κ P Q Pd Qd (firstPiece rest last) (firstPiece rest last).a ≤
        ((β + residBound κ pc * (pc.b - pc.a) + jumpBound0 s pc.b pc (nextPiece rest last) : ℚ) : ℝ) := by
      simp only [firstPiece]
      rw [← hnext]
      push_cast
      linarith
    obtain ⟨hall, hlast⟩ := ih _ hrest hβ'
    refine ⟨fun p hp x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with h | h
      · subst h
        have h1 := hpb x hx
        have h2 : (residBound κ p : ℝ) * (x - p.a) ≤ residBound κ p * (p.b - p.a) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) hρ
        linarith
      · exact hall p h x hx
    · simpa [chainEnd0] using hlast

/-- The check of the chain `pcs ++ [last]` from the bound `β` at its start, order 1. -/
def chain1 (κ s δ : ℚ) : List Piece → Piece → ℚ → Bool
  | [], last, β => last.ok && decide (81 / 100 ≤ 1 + κ / (last.a * last.a)) &&
      decide (β + 10 / 9 * residBound κ last * (last.b - last.a) ≤ δ)
  | pc :: rest, last, β =>
    pc.ok && decide (pc.b = (nextPiece rest last).a) && decide (0 ≤ s) &&
      decide (81 / 100 ≤ 1 + κ / (pc.a * pc.a)) &&
      decide (1 ≤ (1 + κ / (pc.b * pc.b)) * (s * s)) &&
      decide (β + 10 / 9 * residBound κ pc * (pc.b - pc.a) ≤ δ) &&
      chain1 κ s δ rest last
        (β + 10 / 9 * residBound κ pc * (pc.b - pc.a) + jumpBound1 s pc.b pc (nextPiece rest last))

/-- The bound at the end of the chain, order 1. -/
def chainEnd1 (κ s : ℚ) : List Piece → Piece → ℚ → ℚ
  | [], last, β => β + 10 / 9 * residBound κ last * (last.b - last.a)
  | pc :: rest, last, β =>
    chainEnd1 κ s rest last
      (β + 10 / 9 * residBound κ pc * (pc.b - pc.a) + jumpBound1 s pc.b pc (nextPiece rest last))

theorem chain1_sound (κ : ℚ) (hκ : κ ≤ 0) {P Q Pd Qd : ℝ → ℝ} (hsys : PQSystem κ P Q Pd Qd)
    (s δ : ℚ) (pcs : List Piece) (last : Piece) (β : ℚ) (hc : chain1 κ s δ pcs last β = true)
    (hβ : rootE1 κ P Q Pd Qd (firstPiece pcs last) (firstPiece pcs last).a ≤ β) :
    (∀ pc ∈ pcs ++ [last], ∀ x ∈ Icc (pc.a : ℝ) pc.b, rootE1 κ P Q Pd Qd pc x ≤ δ) ∧
      rootE1 κ P Q Pd Qd last last.b ≤ chainEnd1 κ s pcs last β := by
  induction pcs generalizing β with
  | nil =>
    simp only [chain1, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hok, hm⟩, hδ⟩ := hc
    obtain ⟨ha, hab, hca, hbc⟩ := ok_facts hok
    have hρ := residBound_nonneg κ last (by
      have : (0 : ℝ) ≤ last.H := by linarith
      exact_mod_cast this)
    have hpb := piece_bound1 κ hκ hsys last hok hm
    simp only [firstPiece, nextPiece] at hβ
    have hδ' : ((β + 10 / 9 * residBound κ last * (last.b - last.a) : ℚ) : ℝ) ≤ (δ : ℝ) := by
      exact_mod_cast hδ
    push_cast at hδ'
    refine ⟨fun pc hpc x hx => ?_, ?_⟩
    · simp only [List.nil_append, List.mem_singleton] at hpc
      subst hpc
      have h1 := hpb x hx
      have h2 : 10 / 9 * (residBound κ pc : ℝ) * (x - pc.a) ≤ 10 / 9 * residBound κ pc * (pc.b - pc.a) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by positivity)
      linarith
    · have h1 := hpb last.b ⟨hab, le_rfl⟩
      simp only [chainEnd1]
      push_cast
      linarith
  | cons pc rest ih =>
    simp only [chain1, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hok, hnext⟩, hs⟩, hm⟩, hs2⟩, hδ⟩, hrest⟩ := hc
    obtain ⟨ha, hab, hca, hbc⟩ := ok_facts hok
    have hρ := residBound_nonneg κ pc (by
      have : (0 : ℝ) ≤ pc.H := by linarith
      exact_mod_cast this)
    have hpb := piece_bound1 κ hκ hsys pc hok hm
    simp only [firstPiece, nextPiece] at hβ
    have hδ' : ((β + 10 / 9 * residBound κ pc * (pc.b - pc.a) : ℚ) : ℝ) ≤ (δ : ℝ) := by
      exact_mod_cast hδ
    push_cast at hδ'
    have hend := hpb pc.b ⟨hab, le_rfl⟩
    have hs2' : ((1 : ℚ) : ℝ) ≤ (((1 + κ / (pc.b * pc.b)) * (s * s) : ℚ) : ℝ) := by
      exact_mod_cast hs2
    push_cast at hs2'
    have hmpos : (0 : ℝ) < 1 + κ / (pc.b : ℝ) ^ 2 := by
      by_contra hc
      push Not at hc
      have : (1 + κ / ((pc.b : ℝ) * pc.b)) * ((s : ℝ) * s) ≤ 0 := by
        rw [← sq]
        exact mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
      linarith
    have hj := jump1 κ P Q Pd Qd s pc.b pc (nextPiece rest last) hmpos hs (by
        rw [sq, sq]; exact hs2')
    have hβ' : rootE1 κ P Q Pd Qd (firstPiece rest last) (firstPiece rest last).a ≤
        ((β + 10 / 9 * residBound κ pc * (pc.b - pc.a) + jumpBound1 s pc.b pc (nextPiece rest last) : ℚ) : ℝ) := by
      simp only [firstPiece]
      rw [← hnext]
      push_cast
      linarith
    obtain ⟨hall, hlast⟩ := ih _ hrest hβ'
    refine ⟨fun p hp x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with h | h
      · subst h
        have h1 := hpb x hx
        have h2 : 10 / 9 * (residBound κ p : ℝ) * (x - p.a) ≤ 10 / 9 * residBound κ p * (p.b - p.a) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) (by positivity)
        linarith
      · exact hall p h x hx
    · simpa [chainEnd1] using hlast

/-! The asymptotic approximation and its junction with the last piece. -/

/-- Hankel's coefficients `a_k = ∏_(j ≤ k) (μ - (2j - 1) ^ 2) / (k! 8 ^ k)` with `μ = 4 ν ^ 2`
([DLMF 10.17.1](https://dlmf.nist.gov/10.17)). -/
def hankel (μ : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => hankel μ k * (μ - (2 * k + 1) ^ 2) / (8 * (k + 1))

/-- The terms `i ^ k a_k t ^ k` of `P`, the real parts, for `k < n`. -/
def asymA (μ : ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map fun k => if k % 4 = 0 then hankel μ k else if k % 4 = 2 then -hankel μ k else 0

/-- The terms of `Q`, the imaginary parts, for `k < n`. -/
def asymB (μ : ℚ) (n : ℕ) : List ℚ :=
  (List.range n).map fun k => if k % 4 = 1 then hankel μ k else if k % 4 = 3 then -hankel μ k else 0

/-- The size of the difference between a piece and the asymptotic approximation at `X`, order 0. -/
def jumpAsym0 (s : ℚ) (pc : Piece) (ap : AsymPiece) : ℚ :=
  let t := 1 / ap.X
  let jp := evalQ pc.A (ap.X - pc.c) - evalQ ap.A t
  let jq := evalQ pc.B (ap.X - pc.c) - evalQ ap.B t
  let jp' := evalQ (derivP pc.A) (ap.X - pc.c) - -t ^ 2 * evalQ (derivP ap.A) t
  let jq' := evalQ (derivP pc.B) (ap.X - pc.c) - -t ^ 2 * evalQ (derivP ap.B) t
  qabs (jp' - jq) + qabs (jq' + jp) + s * (qabs jp + qabs jq)

/-- The same for order 1. -/
def jumpAsym1 (s : ℚ) (pc : Piece) (ap : AsymPiece) : ℚ :=
  let t := 1 / ap.X
  let jp := evalQ pc.A (ap.X - pc.c) - evalQ ap.A t
  let jq := evalQ pc.B (ap.X - pc.c) - evalQ ap.B t
  let jp' := evalQ (derivP pc.A) (ap.X - pc.c) - -t ^ 2 * evalQ (derivP ap.A) t
  let jq' := evalQ (derivP pc.B) (ap.X - pc.c) - -t ^ 2 * evalQ (derivP ap.B) t
  s * (qabs (jp' - jq) + qabs (jq' + jp)) + (qabs jp + qabs jq)

theorem jumpAsym0_le (κ : ℚ) (P Q Pd Qd : ℝ → ℝ) (s : ℚ) (pc : Piece) (ap : AsymPiece)
    (hm : (0 : ℝ) ≤ 1 + κ / (ap.X : ℝ) ^ 2) (hs : 0 ≤ s)
    (hs2 : (1 : ℝ) + κ / (ap.X : ℝ) ^ 2 ≤ (s : ℝ) ^ 2) :
    root0 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 ap.X ≤
      rootE0 κ P Q Pd Qd pc ap.X + jumpAsym0 s pc ap := by
  have h := energy0_shift κ ap.X (P ap.X - pc.fA ap.X) (Q ap.X - pc.fB ap.X)
    (Pd ap.X - pc.fA1 ap.X) (Qd ap.X - pc.fB1 ap.X) (pc.fA ap.X - ap.fA ap.X)
    (pc.fB ap.X - ap.fB ap.X) (pc.fA1 ap.X - ap.fA1 ap.X) (pc.fB1 ap.X - ap.fB1 ap.X) s hm
    (by exact_mod_cast hs) hs2
  simp only [rootE0, root0]
  rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [jumpAsym0, Piece.fA, Piece.fB, Piece.fA1, Piece.fB1, AsymPiece.fA, AsymPiece.fB,
    AsymPiece.fA1, AsymPiece.fB1]
  push_cast [qabs_cast, evalQ_cast]
  ring

theorem jumpAsym1_le (κ : ℚ) (P Q Pd Qd : ℝ → ℝ) (s : ℚ) (pc : Piece) (ap : AsymPiece)
    (hm : (0 : ℝ) < 1 + κ / (ap.X : ℝ) ^ 2) (hs : 0 ≤ s)
    (hs2 : (1 : ℝ) ≤ (1 + κ / (ap.X : ℝ) ^ 2) * (s : ℝ) ^ 2) :
    root1 κ P Q Pd Qd ap.fA ap.fB ap.fA1 ap.fB1 ap.X ≤
      rootE1 κ P Q Pd Qd pc ap.X + jumpAsym1 s pc ap := by
  have h := energy1_shift κ ap.X (P ap.X - pc.fA ap.X) (Q ap.X - pc.fB ap.X)
    (Pd ap.X - pc.fA1 ap.X) (Qd ap.X - pc.fB1 ap.X) (pc.fA ap.X - ap.fA ap.X)
    (pc.fB ap.X - ap.fB ap.X) (pc.fA1 ap.X - ap.fA1 ap.X) (pc.fB1 ap.X - ap.fB1 ap.X) s hm
    (by exact_mod_cast hs) hs2
  simp only [rootE1, root1]
  rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [jumpAsym1, Piece.fA, Piece.fB, Piece.fA1, Piece.fB1, AsymPiece.fA, AsymPiece.fB,
    AsymPiece.fA1, AsymPiece.fB1]
  push_cast [qabs_cast, evalQ_cast]
  ring

/-- Both energies bound the errors themselves. -/
theorem abs_le_root0 (κ x p q p' q' : ℝ) (hκ : 0 ≤ κ) :
    |p| ≤ √(energy0 κ x p q p' q') ∧ |q| ≤ √(energy0 κ x p q p' q') := by
  have hk : 0 ≤ κ / x ^ 2 := div_nonneg hκ (sq_nonneg x)
  have h1 : 0 ≤ κ / x ^ 2 * (p ^ 2 + q ^ 2) := mul_nonneg hk (by positivity)
  constructor <;> apply Real.abs_le_sqrt <;> unfold energy0 <;>
    nlinarith [sq_nonneg (p' - q), sq_nonneg (q' + p), sq_nonneg p, sq_nonneg q]

theorem abs_le_root1 (κ x p q p' q' : ℝ) (hm : 0 < 1 + κ / x ^ 2) :
    |p| ≤ √(energy1 κ x p q p' q') ∧ |q| ≤ √(energy1 κ x p q p' q') := by
  have h1 : 0 ≤ ((p' - q) ^ 2 + (q' + p) ^ 2) / (1 + κ / x ^ 2) := by positivity
  constructor <;> apply Real.abs_le_sqrt <;> unfold energy1 <;>
    nlinarith [sq_nonneg p, sq_nonneg q]

#print axioms asym_bound0
#print axioms asym_bound1
#print axioms chain0_sound
#print axioms chain1_sound
#print axioms jumpAsym0_le
#print axioms jumpAsym1_le

end LeanExe.ProofKit.BesselChain
