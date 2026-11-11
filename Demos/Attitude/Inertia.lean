import Demos.Attitude.Davenport

/-! The inertia certificate of a symmetric 4×4 matrix.  `Sym4.schur`, `Sym3.schur`, and
`Sym2.schur` eliminate the first index: the form of the matrix is its first entry times a square
plus the form of the Schur complement on the remaining indices (`Sym4.form_schur` and its
siblings), which is the step of the symmetric factorization `L D Lᵀ`.  `swap` exchanges the first
index with another on both sides of the matrix, so a factorization that chooses its pivot at each
stage is a sequence of swaps and eliminations, and `pivots` gives its four pivots.

`OnePos` states the inertia that the certificate needs: the form is positive at some vector and
negative at every nonzero vector of some hyperplane.  `onePos_of_pivots` derives it from pivots of
which exactly one is positive and the others negative, by induction over the stages: a negative
pivot keeps `NegDef` or `OnePos` of the Schur complement, and a positive pivot turns `NegDef` of
the Schur complement into `OnePos`. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Rotation Vec

noncomputable section

/-- A symmetric 3×3 matrix by its entries on and above the diagonal. -/
structure Sym3 where
  c00 : ℝ
  c01 : ℝ
  c02 : ℝ
  c11 : ℝ
  c12 : ℝ
  c22 : ℝ

/-- A symmetric 2×2 matrix by its entries on and above the diagonal. -/
structure Sym2 where
  d00 : ℝ
  d01 : ℝ
  d11 : ℝ

def Sym3.form (B : Sym3) (v : Vec) : ℝ :=
  B.c00 * v.x * v.x + 2 * B.c01 * v.x * v.y + 2 * B.c02 * v.x * v.z + B.c11 * v.y * v.y +
    2 * B.c12 * v.y * v.z + B.c22 * v.z * v.z

def Sym2.form (C : Sym2) (x y : ℝ) : ℝ := C.d00 * x * x + 2 * C.d01 * x * y + C.d11 * y * y

/-! ### Elimination -/

/-- The Schur complement of the entry `a00`. -/
def Sym4.schur (A : Sym4) : Sym3 :=
  ⟨A.a11 - A.a01 / A.a00 * A.a01, A.a12 - A.a01 / A.a00 * A.a02, A.a13 - A.a01 / A.a00 * A.a03,
    A.a22 - A.a02 / A.a00 * A.a02, A.a23 - A.a02 / A.a00 * A.a03, A.a33 - A.a03 / A.a00 * A.a03⟩

def Sym3.schur (B : Sym3) : Sym2 :=
  ⟨B.c11 - B.c01 / B.c00 * B.c01, B.c12 - B.c01 / B.c00 * B.c02, B.c22 - B.c02 / B.c00 * B.c02⟩

/-- The last pivot of a 2×2 matrix. -/
def Sym2.schur (C : Sym2) : ℝ := C.d11 - C.d01 / C.d00 * C.d01

theorem Sym4.form_schur (A : Sym4) (h : A.a00 ≠ 0) (q : Quat) :
    A.form q = A.a00 * (q.w + (A.a01 * q.x + A.a02 * q.y + A.a03 * q.z) / A.a00) ^ 2 +
      A.schur.form ⟨q.x, q.y, q.z⟩ := by
  simp only [Sym4.form, qdot, Sym4.apply, Sym4.schur, Sym3.form]
  field_simp
  ring

theorem Sym3.form_schur (B : Sym3) (h : B.c00 ≠ 0) (v : Vec) :
    B.form v = B.c00 * (v.x + (B.c01 * v.y + B.c02 * v.z) / B.c00) ^ 2 + B.schur.form v.y v.z := by
  simp only [Sym3.form, Sym3.schur, Sym2.form]
  field_simp
  ring

theorem Sym2.form_schur (C : Sym2) (h : C.d00 ≠ 0) (x y : ℝ) :
    C.form x y = C.d00 * (x + C.d01 * y / C.d00) ^ 2 + C.schur * y * y := by
  simp only [Sym2.form, Sym2.schur]
  field_simp
  ring

/-! ### Exchanges of the first index -/

/-- `A` with the indices 0 and `p` exchanged for `p` from 1 to 3, and `A` for other `p`. -/
def Sym4.swap (p : UInt64) (A : Sym4) : Sym4 :=
  if p == 1 then ⟨A.a11, A.a01, A.a12, A.a13, A.a00, A.a02, A.a03, A.a22, A.a23, A.a33⟩
  else if p == 2 then ⟨A.a22, A.a12, A.a02, A.a23, A.a11, A.a01, A.a13, A.a00, A.a03, A.a33⟩
  else if p == 3 then ⟨A.a33, A.a13, A.a23, A.a03, A.a11, A.a12, A.a01, A.a22, A.a02, A.a00⟩
  else A

/-- `q` with the components 0 and `p` exchanged. -/
def qswap (p : UInt64) (q : Quat) : Quat :=
  if p == 1 then ⟨q.x, q.w, q.y, q.z⟩
  else if p == 2 then ⟨q.y, q.x, q.w, q.z⟩
  else if p == 3 then ⟨q.z, q.x, q.y, q.w⟩
  else q

def Sym3.swap (p : UInt64) (B : Sym3) : Sym3 :=
  if p == 1 then ⟨B.c11, B.c01, B.c12, B.c00, B.c02, B.c22⟩
  else if p == 2 then ⟨B.c22, B.c12, B.c02, B.c11, B.c01, B.c00⟩
  else B

def vswap (p : UInt64) (v : Vec) : Vec :=
  if p == 1 then ⟨v.y, v.x, v.z⟩ else if p == 2 then ⟨v.z, v.y, v.x⟩ else v

def Sym2.swap (p : UInt64) (C : Sym2) : Sym2 := if p == 1 then ⟨C.d11, C.d01, C.d00⟩ else C

theorem Sym4.form_swap (p : UInt64) (A : Sym4) (q : Quat) :
    (A.swap p).form (qswap p q) = A.form q := by
  unfold Sym4.swap qswap
  split_ifs <;> simp only [Sym4.form, qdot, Sym4.apply] <;> ring

theorem qswap_qswap (p : UInt64) (q : Quat) : qswap p (qswap p q) = q := by
  unfold qswap
  split_ifs <;> rfl

theorem qdot_qswap (p : UInt64) (c q : Quat) : qdot (qswap p c) (qswap p q) = qdot c q := by
  unfold qswap
  split_ifs <;> simp only [qdot] <;> ring

theorem norm2_qswap (p : UInt64) (q : Quat) : Quat.norm2 (qswap p q) = Quat.norm2 q := by
  rw [← qdot_self, ← qdot_self, qdot_qswap]

theorem Sym3.form_swap (p : UInt64) (B : Sym3) (v : Vec) : (B.swap p).form (vswap p v) = B.form v := by
  unfold Sym3.swap vswap
  split_ifs <;> simp only [Sym3.form] <;> ring

theorem vswap_vswap (p : UInt64) (v : Vec) : vswap p (vswap p v) = v := by
  unfold vswap
  split_ifs <;> rfl

theorem dot_vswap (p : UInt64) (c v : Vec) : dot (vswap p c) (vswap p v) = dot c v := by
  unfold vswap
  split_ifs <;> simp only [dot] <;> ring

theorem Sym2.form_swap (p : UInt64) (C : Sym2) (x y : ℝ) :
    (C.swap p).form (if p == 1 then y else x) (if p == 1 then x else y) = C.form x y := by
  unfold Sym2.swap
  split_ifs
  · simp only [Sym2.form]; ring
  · rfl

/-! ### Inertia -/

def Sym4.NegDef (A : Sym4) : Prop := ∀ q, 0 < Quat.norm2 q → A.form q < 0

/-- The form is positive at some vector and negative at every nonzero vector of a hyperplane. -/
def Sym4.OnePos (A : Sym4) : Prop :=
  (∃ u, 0 < A.form u) ∧ ∃ c : Quat, ∀ q, qdot c q = 0 → 0 < Quat.norm2 q → A.form q < 0

def Sym3.NegDef (B : Sym3) : Prop := ∀ v, 0 < dot v v → B.form v < 0

def Sym3.OnePos (B : Sym3) : Prop :=
  (∃ u, 0 < B.form u) ∧ ∃ c : Vec, ∀ v, dot c v = 0 → 0 < dot v v → B.form v < 0

def Sym2.NegDef (C : Sym2) : Prop := ∀ x y, 0 < x * x + y * y → C.form x y < 0

def Sym2.OnePos (C : Sym2) : Prop :=
  (∃ x y, 0 < C.form x y) ∧
    ∃ c1 c2 : ℝ, ∀ x y, c1 * x + c2 * y = 0 → 0 < x * x + y * y → C.form x y < 0

/-! #### Two dimensions -/

theorem Sym2.negDef_of {C : Sym2} (h0 : C.d00 < 0) (hs : C.schur < 0) : C.NegDef := by
  intro x y hxy
  rw [C.form_schur h0.ne]
  have h1 : C.d00 * (x + C.d01 * y / C.d00) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    have hx : 0 < x * x := by simpa using hxy
    simp only [mul_zero, zero_div, add_zero]
    nlinarith
  · have : 0 < y * y := mul_self_pos.mpr hy
    have h2 : C.schur * y * y < 0 := by rw [mul_assoc]; exact mul_neg_of_neg_of_pos hs this
    linarith

theorem Sym2.onePos_of_neg {C : Sym2} (h0 : C.d00 < 0) (hs : 0 < C.schur) : C.OnePos := by
  refine ⟨⟨-(C.d01 / C.d00), 1, ?_⟩, 0, 1, fun x y hc hxy => ?_⟩
  · rw [C.form_schur h0.ne]
    have e : -(C.d01 / C.d00) + C.d01 * 1 / C.d00 = 0 := by ring
    rw [e]; simpa using hs
  · have hy : y = 0 := by linarith
    subst hy
    have hx : 0 < x * x := by simpa using hxy
    simp only [Sym2.form]
    nlinarith

theorem Sym2.onePos_of_pos {C : Sym2} (h0 : 0 < C.d00) (hs : C.schur < 0) : C.OnePos := by
  refine ⟨⟨1, 0, ?_⟩, 1, C.d01 / C.d00, fun x y hc hxy => ?_⟩
  · simp only [Sym2.form]; nlinarith
  · rw [C.form_schur h0.ne']
    have e : x + C.d01 * y / C.d00 = 0 := by rw [← hc]; ring
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have : x = 0 := by simpa using e
      subst this
      simp at hxy
    · rw [e]
      have : 0 < y * y := mul_self_pos.mpr hy
      have h2 : C.schur * y * y < 0 := by rw [mul_assoc]; exact mul_neg_of_neg_of_pos hs this
      simpa using h2

theorem Sym2.negDef_swap {C : Sym2} {p : UInt64} (h : (C.swap p).NegDef) : C.NegDef := by
  intro x y hxy
  rw [← C.form_swap p]
  apply h
  split_ifs <;> linarith

theorem Sym2.onePos_swap {C : Sym2} {p : UInt64} (h : (C.swap p).OnePos) : C.OnePos := by
  obtain ⟨⟨x, y, hu⟩, c1, c2, hc⟩ := h
  refine ⟨⟨if p == 1 then y else x, if p == 1 then x else y, ?_⟩,
    if p == 1 then c2 else c1, if p == 1 then c1 else c2, fun a b hab hpos => ?_⟩
  · rw [← C.form_swap p]
    split_ifs <;> simpa using hu
  · rw [← C.form_swap p]
    apply hc
    · split_ifs at hab ⊢ <;> linarith
    · split_ifs <;> linarith

/-! #### Three dimensions -/

theorem Sym3.negDef_of {B : Sym3} (h0 : B.c00 < 0) (hS : B.schur.NegDef) : B.NegDef := by
  intro v hv
  rw [B.form_schur h0.ne]
  have h1 : B.c00 * (v.x + (B.c01 * v.y + B.c02 * v.z) / B.c00) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
  by_cases hyz : 0 < v.y * v.y + v.z * v.z
  · linarith [hS v.y v.z hyz]
  · have hy : v.y = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
    have hz : v.z = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
    have hx : 0 < v.x * v.x := by simp only [dot, hy, hz] at hv; linarith
    rw [hy, hz]
    simp only [Sym2.form, mul_zero, add_zero, zero_div]
    nlinarith

theorem Sym3.onePos_of_neg {B : Sym3} (h0 : B.c00 < 0) (hS : B.schur.OnePos) : B.OnePos := by
  obtain ⟨⟨x, y, hu⟩, c1, c2, hc⟩ := hS
  refine ⟨⟨⟨-((B.c01 * x + B.c02 * y) / B.c00), x, y⟩, ?_⟩, ⟨0, c1, c2⟩, fun v hcv hv => ?_⟩
  · rw [B.form_schur h0.ne]
    have e : -((B.c01 * x + B.c02 * y) / B.c00) + (B.c01 * x + B.c02 * y) / B.c00 = 0 := by ring
    simp only
    rw [e]; simpa using hu
  · rw [B.form_schur h0.ne]
    have h1 : B.c00 * (v.x + (B.c01 * v.y + B.c02 * v.z) / B.c00) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
    have hc' : c1 * v.y + c2 * v.z = 0 := by simp only [dot] at hcv; linarith
    by_cases hyz : 0 < v.y * v.y + v.z * v.z
    · linarith [hc v.y v.z hc' hyz]
    · have hy : v.y = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
      have hz : v.z = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
      have hx : 0 < v.x * v.x := by simp only [dot, hy, hz] at hv; linarith
      rw [hy, hz]
      simp only [Sym2.form, mul_zero, add_zero, zero_div]
      nlinarith

theorem Sym3.onePos_of_pos {B : Sym3} (h0 : 0 < B.c00) (hS : B.schur.NegDef) : B.OnePos := by
  refine ⟨⟨⟨1, 0, 0⟩, ?_⟩, ⟨1, B.c01 / B.c00, B.c02 / B.c00⟩, fun v hcv hv => ?_⟩
  · simp only [Sym3.form]; nlinarith
  · rw [B.form_schur h0.ne']
    have e : v.x + (B.c01 * v.y + B.c02 * v.z) / B.c00 = 0 := by
      simp only [dot] at hcv; rw [← hcv]; field_simp; ring
    rw [e]
    by_cases hyz : 0 < v.y * v.y + v.z * v.z
    · have := hS v.y v.z hyz
      simpa using this
    · have hy : v.y = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
      have hz : v.z = 0 := by nlinarith [mul_self_nonneg v.y, mul_self_nonneg v.z]
      have hx : v.x = 0 := by rw [hy, hz] at e; simpa using e
      simp only [dot, hx, hy, hz] at hv
      linarith

theorem Sym3.negDef_swap {B : Sym3} {p : UInt64} (h : (B.swap p).NegDef) : B.NegDef := by
  intro v hv
  rw [← B.form_swap p]
  exact h _ (by rw [dot_vswap]; exact hv)

theorem Sym3.onePos_swap {B : Sym3} {p : UInt64} (h : (B.swap p).OnePos) : B.OnePos := by
  obtain ⟨⟨u, hu⟩, c, hc⟩ := h
  refine ⟨⟨vswap p u, ?_⟩, vswap p c, fun v hcv hv => ?_⟩
  · rw [← B.form_swap p, vswap_vswap]; exact hu
  · rw [← B.form_swap p]
    refine hc _ ?_ (by rw [dot_vswap]; exact hv)
    rw [← dot_vswap p, vswap_vswap]; exact hcv

/-! #### Four dimensions -/

theorem Sym4.negDef_of {A : Sym4} (h0 : A.a00 < 0) (hS : A.schur.NegDef) : A.NegDef := by
  intro q hq
  rw [A.form_schur h0.ne]
  have h1 : A.a00 * (q.w + (A.a01 * q.x + A.a02 * q.y + A.a03 * q.z) / A.a00) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
  by_cases hv : 0 < dot ⟨q.x, q.y, q.z⟩ ⟨q.x, q.y, q.z⟩
  · linarith [hS _ hv]
  · simp only [dot] at hv
    have hx : q.x = 0 := by nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
    have hy : q.y = 0 := by nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
    have hz : q.z = 0 := by nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
    have hw : 0 < q.w * q.w := by simp only [Quat.norm2, hx, hy, hz] at hq; linarith
    rw [hx, hy, hz]
    simp only [Sym3.form, mul_zero, add_zero, zero_div]
    nlinarith

theorem Sym4.onePos_of_neg {A : Sym4} (h0 : A.a00 < 0) (hS : A.schur.OnePos) : A.OnePos := by
  obtain ⟨⟨u, hu⟩, c, hc⟩ := hS
  refine ⟨⟨⟨-((A.a01 * u.x + A.a02 * u.y + A.a03 * u.z) / A.a00), u.x, u.y, u.z⟩, ?_⟩,
    ⟨0, c.x, c.y, c.z⟩, fun q hcq hq => ?_⟩
  · rw [A.form_schur h0.ne]
    have e : -((A.a01 * u.x + A.a02 * u.y + A.a03 * u.z) / A.a00) +
        (A.a01 * u.x + A.a02 * u.y + A.a03 * u.z) / A.a00 = 0 := by ring
    simp only
    rw [e]; simpa using hu
  · rw [A.form_schur h0.ne]
    have h1 : A.a00 * (q.w + (A.a01 * q.x + A.a02 * q.y + A.a03 * q.z) / A.a00) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
    have hc' : dot c ⟨q.x, q.y, q.z⟩ = 0 := by simp only [qdot] at hcq; simp only [dot]; linarith
    by_cases hv : 0 < dot ⟨q.x, q.y, q.z⟩ ⟨q.x, q.y, q.z⟩
    · linarith [hc _ hc' hv]
    · simp only [dot] at hv
      have hx : q.x = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hy : q.y = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hz : q.z = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hw : 0 < q.w * q.w := by simp only [Quat.norm2, hx, hy, hz] at hq; linarith
      rw [hx, hy, hz]
      simp only [Sym3.form, mul_zero, add_zero, zero_div]
      nlinarith

theorem Sym4.onePos_of_pos {A : Sym4} (h0 : 0 < A.a00) (hS : A.schur.NegDef) : A.OnePos := by
  refine ⟨⟨⟨1, 0, 0, 0⟩, ?_⟩, ⟨1, A.a01 / A.a00, A.a02 / A.a00, A.a03 / A.a00⟩,
    fun q hcq hq => ?_⟩
  · simp only [Sym4.form, qdot, Sym4.apply]; nlinarith
  · rw [A.form_schur h0.ne']
    have e : q.w + (A.a01 * q.x + A.a02 * q.y + A.a03 * q.z) / A.a00 = 0 := by
      simp only [qdot] at hcq; rw [← hcq]; field_simp; ring
    rw [e]
    by_cases hv : 0 < dot ⟨q.x, q.y, q.z⟩ ⟨q.x, q.y, q.z⟩
    · have := hS _ hv
      simpa using this
    · simp only [dot] at hv
      have hx : q.x = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hy : q.y = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hz : q.z = 0 := by
        nlinarith [mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
      have hw : q.w = 0 := by rw [hx, hy, hz] at e; simpa using e
      simp only [Quat.norm2, hw, hx, hy, hz] at hq
      linarith

theorem Sym4.negDef_swap {A : Sym4} {p : UInt64} (h : (A.swap p).NegDef) : A.NegDef := by
  intro q hq
  rw [← A.form_swap p]
  exact h _ (by rw [norm2_qswap]; exact hq)

theorem Sym4.onePos_swap {A : Sym4} {p : UInt64} (h : (A.swap p).OnePos) : A.OnePos := by
  obtain ⟨⟨u, hu⟩, c, hc⟩ := h
  refine ⟨⟨qswap p u, ?_⟩, qswap p c, fun q hcq hq => ?_⟩
  · rw [← A.form_swap p, qswap_qswap]; exact hu
  · rw [← A.form_swap p]
    refine hc _ ?_ (by rw [norm2_qswap]; exact hq)
    rw [← qdot_qswap p, qswap_qswap]; exact hcq

/-! ### The pivots -/

/-- The pivots of the symmetric factorization of `A` that brings index `p1` of `A` to the front,
then index `p2` of the first Schur complement, then index `p3` of the second. -/
def pivots (p1 p2 p3 : UInt64) (A : Sym4) : ℝ × ℝ × ℝ × ℝ :=
  ((A.swap p1).a00, ((A.swap p1).schur.swap p2).c00,
    (((A.swap p1).schur.swap p2).schur.swap p3).d00,
    (((A.swap p1).schur.swap p2).schur.swap p3).schur)

/-- One of the four reals is positive and the other three are negative. -/
def OneSign (d : ℝ × ℝ × ℝ × ℝ) : Prop :=
  (0 < d.1 ∧ d.2.1 < 0 ∧ d.2.2.1 < 0 ∧ d.2.2.2 < 0) ∨
  (d.1 < 0 ∧ 0 < d.2.1 ∧ d.2.2.1 < 0 ∧ d.2.2.2 < 0) ∨
  (d.1 < 0 ∧ d.2.1 < 0 ∧ 0 < d.2.2.1 ∧ d.2.2.2 < 0) ∨
  (d.1 < 0 ∧ d.2.1 < 0 ∧ d.2.2.1 < 0 ∧ 0 < d.2.2.2)

/-- **The inertia certificate.**  Pivots of which one is positive and three are negative give a
vector with a positive form and a hyperplane on which the form is negative. -/
theorem onePos_of_pivots {p1 p2 p3 : UInt64} {A : Sym4} (h : OneSign (pivots p1 p2 p3 A)) :
    A.OnePos := by
  simp only [OneSign, pivots] at h
  set A' := A.swap p1
  set B := A'.schur.swap p2
  set C := B.schur.swap p3
  apply Sym4.onePos_swap (p := p1)
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Sym4.onePos_of_pos h1 (Sym3.negDef_swap (p := p2) (Sym3.negDef_of h2
      (Sym2.negDef_swap (p := p3) (Sym2.negDef_of h3 h4))))
  · exact Sym4.onePos_of_neg h1 (Sym3.onePos_swap (p := p2) (Sym3.onePos_of_pos h2
      (Sym2.negDef_swap (p := p3) (Sym2.negDef_of h3 h4))))
  · exact Sym4.onePos_of_neg h1 (Sym3.onePos_swap (p := p2) (Sym3.onePos_of_neg h2
      (Sym2.onePos_swap (p := p3) (Sym2.onePos_of_pos h3 h4))))
  · exact Sym4.onePos_of_neg h1 (Sym3.onePos_swap (p := p2) (Sym3.onePos_of_neg h2
      (Sym2.onePos_swap (p := p3) (Sym2.onePos_of_neg h3 h4))))

end

end Demos.Attitude
