import Mathlib.Tactic

/-!
The rounding error of a left-to-right floating-point sum, for any binary format.  An `Adder`
gives the value and the finiteness of a word, a rounded addition whose error is at most `u` times
the exact sum's magnitude below `bound`, and a zero word to which a finite word below `bound0`
adds exactly.  `sum_approx` bounds the error of `l.foldl (fun acc a => add acc (t a)) zero`, where
each word `t a` lies within `d a` of a real `v a`: the error is at most
`(1 + u) ^ (n - 1) * Σ (|v a| + d a) - Σ |v a|` for a list of `n` terms, since the first addition
is exact and each later one multiplies the error so far by `1 + u`.  `dot_approx` applies it to
rounded products, each within `u |x y| + η` of the exact product.  `gamma_le` gives the closed
form `(1 + u) ^ k - 1 ≤ k u / (1 - k u)`, the `γ_k` of Higham's *Accuracy and Stability of
Numerical Algorithms*, Lemma 3.1.
-/

namespace Library.Numerics.Reductions.SumError

/-- A rounded addition on the words of type `F`: the value `val` and finiteness `fin` of a word,
the addition `add` with relative error at most `u` when the exact sum lies below `bound` in
magnitude, and a word `zero` of value 0 to which a finite word of magnitude at most `bound0` adds
exactly. -/
structure Adder (F : Type) where
  val : F → ℝ
  fin : F → Prop
  add : F → F → F
  zero : F
  u : ℝ
  bound0 : ℝ
  bound : ℝ
  u_nonneg : 0 ≤ u
  zero_fin : fin zero
  zero_val : val zero = 0
  zero_add : ∀ t, fin t → |val t| ≤ bound0 → fin (add zero t) ∧ val (add zero t) = val t
  add_rel : ∀ a b, fin a → fin b → |val a + val b| < bound →
    fin (add a b) ∧ |val (add a b) - (val a + val b)| ≤ u * |val a + val b|

variable {F : Type} (A : Adder F)

/-- The word `w` is finite and its value lies within `e` of `v`. -/
def Adder.Approx (w : F) (v e : ℝ) : Prop := A.fin w ∧ |A.val w - v| ≤ e

theorem Adder.Approx.mono {A : Adder F} {w : F} {v e e' : ℝ} (h : A.Approx w v e) (he : e ≤ e') :
    A.Approx w v e' := ⟨h.1, h.2.trans he⟩

theorem abs_sum_le {α : Type} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun a => |f a|).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (by linarith)

theorem sum_nonneg_of {α : Type} (l : List α) (f : α → ℝ) (h : ∀ a ∈ l, 0 ≤ f a) :
    0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- The error of a left-to-right sum of words, each within `d a` of `v a`. -/
theorem sum_approx {α : Type} (l : List α) (t : α → F) (v d : α → ℝ)
    (ht : ∀ a ∈ l, A.Approx (t a) (v a) (d a))
    (h0 : (l.map fun a => |v a| + d a).sum ≤ A.bound0)
    (h1 : (1 + A.u) ^ (l.length - 1) * (l.map fun a => |v a| + d a).sum < A.bound) :
    A.Approx (l.foldl (fun acc a => A.add acc (t a)) A.zero) (l.map v).sum
      ((1 + A.u) ^ (l.length - 1) * (l.map fun a => |v a| + d a).sum -
        (l.map fun a => |v a|).sum) := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, mul_zero, sub_zero]
    exact ⟨A.zero_fin, by simp [A.zero_val]⟩
  | append_singleton l a ih =>
    have hu := A.u_nonneg
    have ht' : ∀ b ∈ l, A.Approx (t b) (v b) (d b) := fun b hb =>
      ht b (List.mem_append_left _ hb)
    have ha := ht a (List.mem_append_right _ (List.mem_singleton_self a))
    have hda : 0 ≤ d a := (abs_nonneg _).trans ha.2
    have hdl : ∀ b ∈ l, 0 ≤ |v b| + d b := fun b hb =>
      add_nonneg (abs_nonneg _) ((abs_nonneg _).trans (ht' b hb).2)
    have hAl := sum_nonneg_of l (fun b => |v b| + d b) hdl
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, List.length_append, List.length_cons, List.length_nil] at h0 h1 ⊢
    rw [show l.length + (0 + 1) - 1 = l.length by omega] at h1 ⊢
    have hmag : |A.val (t a)| ≤ |v a| + d a := by
      have := abs_sub_abs_le_abs_sub (A.val (t a)) (v a)
      linarith [ha.2]
    by_cases hl : l = []
    · subst hl
      simp only [List.foldl_nil, List.map_nil, List.sum_nil, zero_add, List.length_nil,
        pow_zero, one_mul] at h0 h1 ⊢
      obtain ⟨hf, hv⟩ := A.zero_add (t a) ha.1 (hmag.trans h0)
      refine ⟨hf, ?_⟩
      rw [hv]
      linarith [ha.2]
    · have hlen : 1 ≤ l.length := List.length_pos_iff.mpr hl
      set P := (1 + A.u) ^ (l.length - 1) with hP
      have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
      have hpow : (1 + A.u) ^ l.length = (1 + A.u) * P := by
        rw [hP, ← pow_succ', show l.length - 1 + 1 = l.length by omega]
      rw [hpow] at h1 ⊢
      set Al := (l.map fun b => |v b| + d b).sum
      set Vl := (l.map fun b => |v b|).sum
      have hVl : |(l.map v).sum| ≤ Vl := abs_sum_le l v
      have hX : 0 ≤ |v a| + d a := add_nonneg (abs_nonneg _) hda
      have hk1 : 0 ≤ A.u * P * Al := mul_nonneg (mul_nonneg hu (by linarith)) hAl
      have hk2 : 0 ≤ (1 + A.u) * P * (|v a| + d a) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hX
      have hk3 : 0 ≤ (P - 1) * ((1 + A.u) * (|v a| + d a)) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) hX)
      have hk4 : 0 ≤ A.u * |v a| := mul_nonneg hu (abs_nonneg _)
      have hk5 : 0 ≤ A.u * d a := mul_nonneg hu hda
      have hexp : (1 + A.u) * P * (Al + (|v a| + d a)) =
          P * Al + A.u * P * Al + (1 + A.u) * P * (|v a| + d a) := by ring
      have hexp2 : (1 + A.u) * P * (|v a| + d a) =
          (P - 1) * ((1 + A.u) * (|v a| + d a)) + (1 + A.u) * (|v a| + d a) := by ring
      have ih' := ih ht' (by linarith) (by
        have : P * Al ≤ (1 + A.u) * P * (Al + (|v a| + d a)) := by linarith
        linarith)
      set acc := l.foldl (fun acc a => A.add acc (t a)) A.zero
      set S := (l.map v).sum
      have hacc := ih'.2
      have hta := ha.2
      have hsum : |A.val acc + A.val (t a)| ≤ |S + v a| + (P * Al - Vl + d a) := by
        have := abs_sub_abs_le_abs_sub (A.val acc + A.val (t a)) (S + v a)
        have h2 : |A.val acc + A.val (t a) - (S + v a)| ≤ (P * Al - Vl) + d a := by
          rw [show A.val acc + A.val (t a) - (S + v a) = (A.val acc - S) + (A.val (t a) - v a)
            by ring]
          exact (abs_add_le _ _).trans (add_le_add hacc hta)
        linarith
      have hSa : |S + v a| ≤ Vl + |v a| := (abs_add_le _ _).trans (by linarith)
      have hB : |A.val acc + A.val (t a)| < A.bound := by linarith
      obtain ⟨hf, he⟩ := A.add_rel acc (t a) ih'.1 ha.1 hB
      refine ⟨hf, ?_⟩
      have htri : |A.val (A.add acc (t a)) - (S + v a)| ≤
          A.u * |A.val acc + A.val (t a)| + ((P * Al - Vl) + d a) := by
        rw [show A.val (A.add acc (t a)) - (S + v a) =
          (A.val (A.add acc (t a)) - (A.val acc + A.val (t a))) +
            ((A.val acc - S) + (A.val (t a) - v a)) by ring]
        exact (abs_add_le _ _).trans (add_le_add he ((abs_add_le _ _).trans
          (add_le_add hacc hta)))
      have hmul : A.u * |A.val acc + A.val (t a)| ≤
          A.u * (Vl + |v a| + (P * Al - Vl + d a)) :=
        mul_le_mul_of_nonneg_left (by linarith) hu
      have hexp3 : A.u * (Vl + |v a| + (P * Al - Vl + d a)) =
          A.u * |v a| + A.u * P * Al + A.u * d a := by ring
      linarith

/-- `(1 + u) ^ k (1 - k u) ≤ 1` for `u ≥ 0`. -/
theorem pow_mul_le_one (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : (1 + u) ^ k * (1 - k * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1 + u) ^ k := by positivity
    have e : (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
        (1 + u) ^ k * (1 - k * u) - (1 + u) ^ k * (u ^ 2 * (k + 1)) := by
      push_cast
      ring
    rw [e]
    have : 0 ≤ (1 + u) ^ k * (u ^ 2 * (k + 1)) := by positivity
    linarith

/-- Higham's `γ_k`: `(1 + u) ^ k - 1 ≤ k u / (1 - k u)` for `k u < 1`. -/
theorem gamma_le (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (hk : k * u < 1) :
    (1 + u) ^ k - 1 ≤ k * u / (1 - k * u) := by
  have h := pow_mul_le_one u hu k
  have hpos : 0 < 1 - k * u := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

/-- `γ_k` for the unit roundoff `2 ^ -p`: `(1 + 2 ^ -p) ^ k - 1 ≤ k / (2 ^ p - k)` for
`k < 2 ^ p`. -/
theorem gamma_pow (p k : ℕ) (hk : (k : ℝ) < 2 ^ p) :
    (1 + 1 / 2 ^ p : ℝ) ^ k - 1 ≤ k / (2 ^ p - k) := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have h := gamma_le (1 / 2 ^ p) (by positivity) k (by
    rw [mul_one_div, div_lt_one h2]; exact hk)
  convert h using 1
  field_simp

/-- `(1 + 2 ^ -p) ^ k < 2` for `2 k < 2 ^ p`. -/
theorem pow_le_two (p k : ℕ) (hk : 2 * (k : ℝ) < 2 ^ p) : (1 + 1 / 2 ^ p : ℝ) ^ k < 2 := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hk' : (k : ℝ) < 2 ^ p := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := gamma_pow p k hk'
  have hpos : (0 : ℝ) < 2 ^ p - k := by linarith
  have : (k : ℝ) / (2 ^ p - k) < 1 := by
    rw [div_lt_one hpos]; linarith
  linarith

/-- The error of a left-to-right sum of rounded products `mul (x a) (y a)`, each within
`u |x a y a| + η` of the exact product. -/
theorem dot_approx {α : Type} (l : List α) (x y : α → F) (mul : F → F → F) (η : ℝ)
    (hmul : ∀ a ∈ l, A.Approx (mul (x a) (y a)) (A.val (x a) * A.val (y a))
      (A.u * |A.val (x a) * A.val (y a)| + η))
    (h0 : (1 + A.u) * (l.map fun a => |A.val (x a) * A.val (y a)|).sum + l.length * η ≤
      A.bound0)
    (h1 : (1 + A.u) ^ (l.length - 1) * ((1 + A.u) *
      (l.map fun a => |A.val (x a) * A.val (y a)|).sum + l.length * η) < A.bound) :
    A.Approx (l.foldl (fun acc a => A.add acc (mul (x a) (y a))) A.zero)
      (l.map fun a => A.val (x a) * A.val (y a)).sum
      (((1 + A.u) ^ l.length - 1) * (l.map fun a => |A.val (x a) * A.val (y a)|).sum +
        (1 + A.u) ^ (l.length - 1) * (l.length * η)) := by
  have hsum : (l.map fun a => |A.val (x a) * A.val (y a)| +
      (A.u * |A.val (x a) * A.val (y a)| + η)).sum =
      (1 + A.u) * (l.map fun a => |A.val (x a) * A.val (y a)|).sum + l.length * η := by
    clear hmul h0 h1
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring
  have h := sum_approx A l (fun a => mul (x a) (y a)) (fun a => A.val (x a) * A.val (y a))
    (fun a => A.u * |A.val (x a) * A.val (y a)| + η) hmul (by rw [hsum]; exact h0)
    (by rw [hsum]; exact h1)
  refine h.mono (le_of_eq ?_)
  rw [hsum]
  rcases Nat.eq_zero_or_pos l.length with hl | hl
  · rw [List.length_eq_zero_iff.mp hl]
    simp
  · have hp : (1 + A.u) ^ l.length = (1 + A.u) ^ (l.length - 1) * (1 + A.u) := by
      rw [← pow_succ, show l.length - 1 + 1 = l.length by omega]
    rw [hp]
    ring

end Library.Numerics.Reductions.SumError
