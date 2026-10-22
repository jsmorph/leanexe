import Library.Numerics.Float64.Tgamma.TgammaExpr

/-!
Bounds of a polynomial `PolyBound.eval l` on `[-r, r]` that the kernel computes in `ℚ`: the value
is at most `bndQ r l` in magnitude (`eval_bound`), and the polynomial is Lipschitz with constant
`lipQ r l` (`eval_lip`).  The paths of `tgammaWith` evaluate their polynomials at a double that
approximates the exact argument, and `eval_lip` bounds the change.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaPolyLip
open LeanExe.ProofKit PolyBound TgammaExpr

def bndQ (r : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: l => qabs c + r * bndQ r l

def lipQ (r : ℚ) : List ℚ → ℚ
  | [] => 0
  | _ :: l => bndQ r l + r * lipQ r l

theorem bndQ_nonneg (r : ℚ) (hr : 0 ≤ r) : ∀ l : List ℚ, 0 ≤ bndQ r l
  | [] => le_rfl
  | c :: l => by
    have := bndQ_nonneg r hr l
    have : 0 ≤ qabs c := by
      have h : (0 : ℝ) ≤ ((qabs c : ℚ) : ℝ) := by rw [TgammaExpr.qabs_cast]; exact abs_nonneg _
      exact_mod_cast h
    simp only [bndQ]
    positivity

theorem lipQ_nonneg (r : ℚ) (hr : 0 ≤ r) : ∀ l : List ℚ, 0 ≤ lipQ r l
  | [] => le_rfl
  | _ :: l => by
    have := lipQ_nonneg r hr l
    have := bndQ_nonneg r hr l
    simp only [lipQ]
    positivity

theorem eval_bound (r : ℚ) (hr : 0 ≤ r) (a : ℝ) (ha : |a| ≤ r) :
    ∀ l : List ℚ, |eval l a| ≤ bndQ r l
  | [] => by simp [eval, bndQ]
  | c :: l => by
    have ih := eval_bound r hr a ha l
    simp only [eval, bndQ]
    push_cast
    rw [TgammaExpr.qabs_cast]
    calc |(c : ℝ) + a * eval l a| ≤ |(c : ℝ)| + |a| * |eval l a| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + r * bndQ r l := by
          gcongr

theorem eval_lip (r : ℚ) (hr : 0 ≤ r) (a b : ℝ) (ha : |a| ≤ r) (hb : |b| ≤ r) :
    ∀ l : List ℚ, |eval l a - eval l b| ≤ lipQ r l * |a - b|
  | [] => by simp [eval, lipQ]
  | c :: l => by
    have ih := eval_lip r hr a b ha hb l
    have hbd := eval_bound r hr a ha l
    simp only [eval, lipQ]
    push_cast
    have hid : (c : ℝ) + a * eval l a - ((c : ℝ) + b * eval l b) =
        (a - b) * eval l a + b * (eval l a - eval l b) := by ring
    rw [hid]
    have hl0 : (0 : ℝ) ≤ (lipQ r l : ℝ) := by exact_mod_cast lipQ_nonneg r hr l
    calc |(a - b) * eval l a + b * (eval l a - eval l b)|
        ≤ |a - b| * |eval l a| + |b| * |eval l a - eval l b| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a - b| * (bndQ r l : ℝ) + (r : ℝ) * ((lipQ r l : ℝ) * |a - b|) := by
          gcongr
      _ = ((bndQ r l : ℝ) + (r : ℝ) * (lipQ r l : ℝ)) * |a - b| := by ring

#print axioms eval_bound
#print axioms eval_lip

end Library.Numerics.Float64.Tgamma.TgammaPolyLip
