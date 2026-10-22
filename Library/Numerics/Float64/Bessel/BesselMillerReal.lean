import Library.Numerics.Float64.Bessel.BesselSmallSigns

/-!
The real analysis behind the backward recurrence of `jn` (Miller's algorithm) for `0 < x < 2` and
`n ≥ 2`.  The kernel `kern x m M = (π x/2)(Y_m J_M - J_m Y_M)` satisfies 10.6.1 in its first index
as well (`kern_first`), so for `M` fixed it grows from `kern M M = 0` and `kern (M - 1) M = 1` as
`m` decreases while `λ_m ≥ 2` (`kern_grow`).  The quotient `cfrac m = kern m M / kern (m - 1) M`
satisfies the continued fraction `F m = 1/(λ_m - F (m + 1))` with `F M = 0` (`cf_step`), and
with the cross product its value at `m = n` differs from `r = J_n/J_(n-1)` by
`J_M/(J_(n-1) kern (n - 1) M)` (`cf_error`).  The continuant `Q = kern (n - 1) M` is at most the
product `Π` of `λ_n, ..., λ_(M-1)` (`kern_le_prod`), and the series bounds give
`J_M Π ≤ 2.4 J_n` (`tail_ratio`), so the relative error of the truncated fraction is at most
`2.4/Q²`.  The ratios `d_i = J_(i+1)/J_(i-1)` are at most `2/3` from `i = 2` on (`d_le`).
-/

namespace Library.Numerics.Float64.Bessel.BesselMillerReal
open Real Finset LeanExe.ProofKit LeanExe.ProofKit.Bessel BesselOrderN BesselRecur BesselSmallSigns

set_option exponentiation.threshold 2048

/-- 10.6.1 in the first index of the kernel. -/
theorem kern_first (x : ℝ) (hx : x ≠ 0) (m M : ℕ) :
    kern x m M + kern x (m + 2) M = lam x (m + 1) * kern x (m + 1) M := by
  simp only [kern, lam]
  rw [Jn_recur m x hx, Yn_recur]
  push_cast
  ring

/-- For `M` fixed, `kern (M - p) M` grows at least by 1 per step while `λ ≥ 2`. -/
theorem kern_grow (x : ℝ) (hx : 0 < x) (M : ℕ) :
    ∀ p : ℕ, p + 1 ≤ M → (∀ m, M - p ≤ m → m < M → 2 ≤ lam x m) →
      (p : ℝ) ≤ kern x (M - p) M ∧ kern x (M - p) M + 1 ≤ kern x (M - (p + 1)) M := by
  intro p
  induction p with
  | zero =>
    intro hM _
    simp only [Nat.sub_zero, Nat.cast_zero, zero_add]
    rw [kern_self]
    obtain ⟨q, rfl⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
    rw [show q + 1 - 1 = q by omega, kern_succ x hx.ne' q]
    norm_num
  | succ p ih =>
    intro hM hl
    obtain ⟨h1, h2⟩ := ih (by omega) (fun m hm hm' => hl m (by omega) hm')
    have hk := kern_first x hx.ne' (M - (p + 2)) M
    rw [show M - (p + 2) + 2 = M - p by omega, show M - (p + 2) + 1 = M - (p + 1) by omega] at hk
    have hlam := hl (M - (p + 1)) (by omega) (by omega)
    rw [show M - (p + 1 + 1) = M - (p + 2) by omega]
    push_cast
    constructor
    · linarith
    · have : 0 ≤ kern x (M - (p + 1)) M := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
      nlinarith

/-- The continued fraction from `m` up to `M`. -/
noncomputable def cfrac (x : ℝ) (M : ℕ) : ℕ → ℝ := fun m =>
  if m < M then kern x m M / kern x (m - 1) M else 0

/-- The fraction satisfies `F m = 1/(λ_m - F (m + 1))` for `1 ≤ m < M` with `λ ≥ 2` above `m`. -/
theorem cf_step (x : ℝ) (hx : 0 < x) (M m : ℕ) (hm : 1 ≤ m) (hmM : m < M)
    (hl : ∀ i, m ≤ i → i < M → 2 ≤ lam x i) :
    cfrac x M m = 1 / (lam x m - cfrac x M (m + 1)) := by
  have hg := kern_grow x hx M (M - m) (by omega) (fun i hi hi' => hl i (by omega) hi')
  rw [show M - (M - m) = m by omega, show M - (M - m + 1) = m - 1 by omega] at hg
  have hpos : (m + 1 < M ∧ 0 < kern x m M) ∨ m + 1 = M := by
    rcases Nat.lt_or_ge (m + 1) M with h | h
    · left
      refine ⟨h, ?_⟩
      have hg1 := kern_grow x hx M (M - (m + 1)) (by omega) (fun i hi hi' => hl i (by omega) hi')
      rw [show M - (M - (m + 1)) = m + 1 by omega, show M - (M - (m + 1) + 1) = m by omega] at hg1
      have : (0 : ℝ) ≤ ((M - (m + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · right; omega
  have hk := kern_first x hx.ne' (m - 1) M
  rw [show m - 1 + 2 = m + 1 by omega, show m - 1 + 1 = m by omega] at hk
  have hden : 0 < kern x (m - 1) M := by
    have : (0 : ℝ) ≤ ((M - m : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [hg.1, hg.2]
  unfold cfrac
  rw [if_pos hmM]
  rcases hpos with ⟨hlt, h⟩ | h
  · rw [if_pos hlt, show m + 1 - 1 = m by omega]
    have hK : kern x (m - 1) M = lam x m * kern x m M - kern x (m + 1) M := by linarith
    have hm0 : kern x m M ≠ 0 := h.ne'
    have e : lam x m - kern x (m + 1) M / kern x m M =
        (lam x m * kern x m M - kern x (m + 1) M) / kern x m M := by
      field_simp
    rw [e, one_div_div, ← hK]
  · rw [if_neg (by omega), sub_zero, ← h]
    have hk1 : kern x m (m + 1) = 1 := kern_succ x hx.ne' m
    rw [← h] at hk
    rw [hk1, kern_self] at hk
    rw [hk1]
    have : kern x (m - 1) (m + 1) = lam x m := by linarith
    rw [this]

/-- The fraction at `n` against `J_n/J_(n-1)`. -/
theorem cf_error (x : ℝ) (hx : x ≠ 0) (n M : ℕ) (hn : 1 ≤ n) :
    Jn (n - 1) x * kern x n M - Jn n x * kern x (n - 1) M = -Jn M x := by
  have hc := cross x hx (n - 1)
  rw [show n - 1 + 1 = n by omega] at hc
  simp only [kern]
  have hpi : π ≠ 0 := pi_ne_zero
  have e : π * x / 2 * (2 / (π * x)) = 1 := by field_simp <;> ring
  linear_combination (-(π * x / 2) * Jn M x) * hc - Jn M x * e

/-- The product `λ_n ⋯ λ_(n+k)`. -/
noncomputable def lprod (x : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => lam x n
  | k + 1 => lprod x n k * lam x (n + k + 1)

theorem lprod_eq (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) : ∀ k,
    lprod x n k = (2 / x) ^ (k + 1) * ((n + k).factorial : ℝ) / ((n - 1).factorial : ℝ) := by
  have hf : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
  intro k
  induction k with
  | zero =>
    simp only [lprod, lam, zero_add, add_zero, pow_one]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega, Nat.factorial_succ]
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    have hx' : x ≠ 0 := hx.ne'
    push_cast
    field_simp <;> ring
  | succ k ih =>
    rw [lprod, ih, show n + (k + 1) = n + k + 1 by ring, Nat.factorial_succ (n + k),
      pow_succ (2 / x) (k + 1)]
    unfold lam
    push_cast
    ring

/-- The continuant `kern (n - 1) (n + k + 1)` is at most `λ_n ⋯ λ_(n+k)`, given `λ ≥ 2` there. -/
theorem kern_le_prod (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n)
    (hl : ∀ i, n ≤ i → 2 ≤ lam x i) : ∀ k,
      kern x (n - 1) (n + k) ≤ kern x (n - 1) (n + k + 1) ∧
        kern x (n - 1) (n + k + 1) ≤ lprod x n k ∧ 0 ≤ kern x (n - 1) (n + k) := by
  have h0 : kern x (n - 1) n = 1 := by
    have := kern_succ x hx.ne' (n - 1); rwa [show n - 1 + 1 = n by omega] at this
  have h1 : kern x (n - 1) (n + 1) = lam x n := by
    have := kern_recur x hx.ne' (n - 1) (n - 1)
    rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega, kern_self, h0] at this
    linarith
  intro k
  induction k with
  | zero =>
    rw [add_zero, h0, h1]
    simp only [lprod]
    have := hl n le_rfl
    exact ⟨by linarith, le_rfl, by norm_num⟩
  | succ k ih =>
    obtain ⟨a1, a2, a3⟩ := ih
    rw [show n + k + 1 = n + (k + 1) by ring] at a1 a2
    have hr := kern_recur x hx.ne' (n - 1) (n + k)
    rw [show n + k + 2 = n + (k + 1) + 1 by ring, show n + k + 1 = n + (k + 1) by ring] at hr
    have hlam := hl (n + (k + 1)) (by omega)
    have hpos : 0 ≤ kern x (n - 1) (n + (k + 1)) := by linarith
    refine ⟨?_, ?_, hpos⟩
    · rw [hr]; nlinarith
    · rw [hr]
      simp only [lprod]
      rw [show n + k + 1 = n + (k + 1) by ring]
      have : lam x (n + (k + 1)) * kern x (n - 1) (n + (k + 1)) ≤ lam x (n + (k + 1)) * lprod x n k :=
        mul_le_mul_of_nonneg_left a2 (by linarith)
      nlinarith

/-- `J_(n+k+1) λ_n ⋯ λ_(n+k) ≤ 2.4 J_n` for `0 < x ≤ 2` and `n ≥ 2`. -/
theorem tail_ratio (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 2) (n k : ℕ) (hn : 2 ≤ n) :
    Jn (n + k + 1) x * lprod x n k ≤ 12 / 5 * Jn n x := by
  have hb1 := (Jn_bounds (n + k + 1) x hx.le hx2).2
  have hb2 := (Jn_bounds n x hx.le hx2).1
  have hz : x ^ 2 / 4 ≤ 1 := by nlinarith
  have hz0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hx' : x ≠ 0 := hx.ne'
  have hfM : (0 : ℝ) < (n + k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hfk : (0 : ℝ) < (n + k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hfn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hf1 : (0 : ℝ) < (n - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have eM1 : ((n + k + 1 + 1).factorial : ℝ) = ((n : ℝ) + k + 2) * (n + k + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have en1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have eM : ((n + k + 1).factorial : ℝ) = ((n : ℝ) + k + 1) * (n + k).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have en : (n.factorial : ℝ) = (n : ℝ) * (n - 1).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega, Nat.factorial_succ]; push_cast; ring
  -- `J_M ≤ (4/3) (x/2)^M/M!` and `J_n ≥ (5/9) (x/2)^n/n!`
  have hJM : Jn (n + k + 1) x ≤ 4 / 3 * ((x / 2) ^ (n + k + 1) / (n + k + 1).factorial) := by
    have h3 : 4 / 3 * (x ^ 2 / 4) / ((n + k + 1 + 1).factorial : ℝ) ≤
        1 / 3 * (1 / ((n + k + 1).factorial : ℝ)) := by
      rw [eM1, div_le_iff₀ (by positivity)]
      have e : 1 / 3 * (1 / ((n + k + 1).factorial : ℝ)) * (((n : ℝ) + k + 2) * (n + k + 1).factorial) =
          ((n : ℝ) + k + 2) / 3 := by field_simp <;> ring
      rw [e]; linarith
    have hp : 0 ≤ (x / 2) ^ (n + k + 1) := by positivity
    calc Jn (n + k + 1) x ≤ _ := hb1
      _ ≤ (x / 2) ^ (n + k + 1) * (1 / ((n + k + 1).factorial : ℝ) +
          1 / 3 * (1 / ((n + k + 1).factorial : ℝ))) := mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 4 / 3 * ((x / 2) ^ (n + k + 1) / (n + k + 1).factorial) := by ring
  have hJn : 5 / 9 * ((x / 2) ^ n / n.factorial) ≤ Jn n x := by
    have h3 : 4 / 3 * (x ^ 2 / 4) / ((n + 1).factorial : ℝ) ≤ 4 / 9 * (1 / (n.factorial : ℝ)) := by
      rw [en1, div_le_iff₀ (by positivity)]
      have e : 4 / 9 * (1 / (n.factorial : ℝ)) * (((n : ℝ) + 1) * n.factorial) = 4 / 9 * ((n : ℝ) + 1) := by
        field_simp <;> ring
      rw [e]; nlinarith
    have hp : 0 ≤ (x / 2) ^ n := by positivity
    calc 5 / 9 * ((x / 2) ^ n / n.factorial) =
        (x / 2) ^ n * (1 / (n.factorial : ℝ) - 4 / 9 * (1 / (n.factorial : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hp
      _ ≤ Jn n x := hb2
  rw [lprod_eq x hx n (by omega) k]
  have hpow : (x / 2) ^ (n + k + 1) * (2 / x) ^ (k + 1) = (x / 2) ^ n := by
    rw [show n + k + 1 = n + (k + 1) by ring, pow_add, mul_assoc, ← mul_pow,
      show x / 2 * (2 / x) = 1 by field_simp, one_pow, mul_one]
  have key : (x / 2) ^ (n + k + 1) / (n + k + 1).factorial *
      ((2 / x) ^ (k + 1) * ((n + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) =
      (x / 2) ^ n / n.factorial * ((n : ℝ) / ((n : ℝ) + k + 1)) := by
    rw [← hpow, eM, en]
    have h1 : ((n : ℝ) + k + 1) ≠ 0 := by positivity
    have h2 : (n : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  have hlp : 0 ≤ (2 / x) ^ (k + 1) * ((n + k).factorial : ℝ) / ((n - 1).factorial : ℝ) := by
    positivity
  have hq : (n : ℝ) / ((n : ℝ) + k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hA : 0 ≤ (x / 2) ^ n / (n.factorial : ℝ) := by positivity
  calc Jn (n + k + 1) x * ((2 / x) ^ (k + 1) * ((n + k).factorial : ℝ) / ((n - 1).factorial : ℝ))
      ≤ 4 / 3 * ((x / 2) ^ (n + k + 1) / (n + k + 1).factorial) *
          ((2 / x) ^ (k + 1) * ((n + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hJM hlp
    _ = 4 / 3 * ((x / 2) ^ n / n.factorial * ((n : ℝ) / ((n : ℝ) + k + 1))) := by rw [mul_assoc, key]
    _ ≤ 4 / 3 * ((x / 2) ^ n / n.factorial * 1) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hq hA
    _ ≤ 12 / 5 * Jn n x := by linarith

/-- `d_i = J_(i+1)/J_(i-1) ≤ 2/3` for `i ≥ 2` and `0 < x ≤ 2`. -/
theorem d_le (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 2) (i : ℕ) (hi : 2 ≤ i) :
    Jn (i + 1) x ≤ 2 / 3 * Jn (i - 1) x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by ring]
  have hb1 := (Jn_bounds (m + 2) x hx.le hx2).2
  have hb2 := (Jn_bounds m x hx.le hx2).1
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hz : x ^ 2 / 4 ≤ 1 := by nlinarith
  have hz0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hF : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have f1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * m.factorial) := by
    rw [show m + 2 = (m + 1) + 1 by ring, Nat.factorial_succ]; push_cast; rw [f1]; ring
  have f3 : ((m + 2 + 1).factorial : ℝ) =
      ((m : ℝ) + 3) * (((m : ℝ) + 2) * (((m : ℝ) + 1) * m.factorial)) := by
    rw [Nat.factorial_succ]; push_cast; rw [f2]; ring
  have hp : (x / 2) ^ (m + 2) = (x / 2) ^ m * (x ^ 2 / 4) := by rw [pow_add]; ring
  rw [f1] at hb2
  rw [f2, f3, hp] at hb1
  obtain ⟨z, hzd⟩ : ∃ z, z = x ^ 2 / 4 := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = (x / 2) ^ m := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F, F = (m.factorial : ℝ) := ⟨_, rfl⟩
  rw [← hzd, ← hPd, ← hFd] at hb1 hb2
  rw [← hzd] at hz hz0
  rw [← hFd] at hF
  have hP : 0 < P := by rw [hPd]; positivity
  set c := (m : ℝ) with hc
  have h1 : 0 < c + 1 := by linarith
  have h2 : 0 < c + 2 := by linarith
  have h3 : 0 < c + 3 := by linarith
  -- both bounds over the common denominator `3 (c + 1) (c + 2) (c + 3) F`
  have hF' : F ≠ 0 := hF.ne'
  have h1' : c + 1 ≠ 0 := h1.ne'
  have h2' : c + 2 ≠ 0 := h2.ne'
  have h3' : c + 3 ≠ 0 := h3.ne'
  have e1 : P * z * (1 / ((c + 2) * ((c + 1) * F)) + 4 / 3 * z / ((c + 3) * ((c + 2) * ((c + 1) * F)))) =
      P * (z * (3 * (c + 3) + 4 * z) * 3) / (9 * (c + 1) * (c + 2) * (c + 3) * F) := by
    field_simp <;> ring
  have e2 : 2 / 3 * (P * (1 / F - 4 / 3 * z / ((c + 1) * F))) =
      P * (2 * (c + 2) * (c + 3) * (3 * (c + 1) - 4 * z)) / (9 * (c + 1) * (c + 2) * (c + 3) * F) := by
    field_simp <;> ring
  have poly : z * (3 * (c + 3) + 4 * z) * 3 ≤ 2 * (c + 2) * (c + 3) * (3 * (c + 1) - 4 * z) := by
    have hc0 : 0 ≤ c := by linarith
    have hm' : 0 ≤ c - 1 := by linarith
    have hz' : 0 ≤ 1 - z := by linarith
    nlinarith [mul_nonneg (mul_nonneg hm' hc0) hc0, mul_nonneg hm' hc0, mul_nonneg (mul_nonneg hz' hc0) hc0,
      mul_nonneg hz' hc0, mul_nonneg hz' hz0]
  have hD : 0 < 9 * (c + 1) * (c + 2) * (c + 3) * F := by positivity
  have hle : P * (z * (3 * (c + 3) + 4 * z) * 3) / (9 * (c + 1) * (c + 2) * (c + 3) * F) ≤
      P * (2 * (c + 2) * (c + 3) * (3 * (c + 1) - 4 * z)) / (9 * (c + 1) * (c + 2) * (c + 3) * F) := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact mul_le_mul_of_nonneg_left poly hP.le
  calc Jn (m + 2) x ≤ _ := hb1
    _ = _ := e1
    _ ≤ _ := hle
    _ = 2 / 3 * (P * (1 / F - 4 / 3 * z / ((c + 1) * F))) := e2.symm
    _ ≤ 2 / 3 * Jn m x := mul_le_mul_of_nonneg_left hb2 (by norm_num)

#print axioms kern_grow
#print axioms cf_step
#print axioms cf_error
#print axioms kern_le_prod
#print axioms tail_ratio
#print axioms d_le

end Library.Numerics.Float64.Bessel.BesselMillerReal
