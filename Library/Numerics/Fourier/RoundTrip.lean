import Library.Numerics.Fourier.Master
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
The round trip of the discrete Fourier transform.  For a signal of `n` complex values
`x_j = a_j + i b_j` and `θ_jk = 2 π j k / n`, `inversion` states the exact identity
`Σ_k X_k e ^ (i θ_km) = n x_m` for `X_k = Σ_j x_j e ^ (-i θ_jk)`, from the orthogonality of the
factors, `sum_cos_sin`.  `roundtrip_real` composes it with the errors of the forward and inverse
transforms that `dft_spec` and `inverse_spec` state, and `inverse_dft` applies it to the program's
`inverse` and `dft`: for `M = Σ_j (|a_j| + |b_j|) ≤ 2 ^ 960`, each float of `inverse (dft xs)` lies
within `(n + 512) M / 2 ^ 51 + 2 ^ -1040` of the float of `xs` at its index.
-/

namespace Library.Numerics.Fourier

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-- For `j, m < n`, `Σ_k cos (2 π k (j - m) / n)` is `n` when `j = m` and `0` otherwise, and
`Σ_k sin (2 π k (j - m) / n) = 0`. -/
theorem sum_cos_sin (n j m : ℕ) (hj : j < n) (hm : m < n) :
    ∑ k ∈ Finset.range n, Real.cos (2 * Real.pi * k * ((j : ℝ) - m) / n) =
        (if j = m then (n : ℝ) else 0) ∧
      ∑ k ∈ Finset.range n, Real.sin (2 * Real.pi * k * ((j : ℝ) - m) / n) = 0 := by
  by_cases hjm : j = m
  · subst hjm
    simp
  rw [ite_eq_right hjm]
  have hn : (n : ℂ) ≠ 0 := by
    have : 0 < n := by omega
    exact_mod_cast this.ne'
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  set t : ℝ := 2 * Real.pi * ((j : ℝ) - m) / n with ht
  have hk : ∀ k : ℕ, Complex.exp (((2 * Real.pi * k * ((j : ℝ) - m) / n : ℝ) : ℂ) * Complex.I) =
      Complex.exp (t * Complex.I) ^ k := fun k => by
    rw [← Complex.exp_nat_mul, ht]
    congr 1
    push_cast
    ring
  have hz : Complex.exp (t * Complex.I) ≠ 1 := by
    intro h
    obtain ⟨N, hN⟩ := Complex.exp_eq_one_iff.mp h
    have h1 : (t : ℂ) * Complex.I = (((N : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hN]
      push_cast
      ring
    have h2 : t = N * (2 * Real.pi) := by exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
    have h3 : (2 * Real.pi) * ((j : ℝ) - m) = (2 * Real.pi) * (N * n) := by
      have : t * n = 2 * Real.pi * ((j : ℝ) - m) := by
        rw [ht, div_mul_cancel₀ _ hnr]
      rw [← this, h2]
      ring
    have h4 : (j : ℤ) - m = N * n := by
      exact_mod_cast mul_left_cancel₀ (by positivity) h3
    rcases lt_trichotomy N 0 with hN0 | hN0 | hN0
    · have : N * (n : ℤ) ≤ -n := by nlinarith
      omega
    · rw [hN0, zero_mul] at h4
      omega
    · have : (n : ℤ) ≤ N * n := by nlinarith
      omega
  have hzn : Complex.exp (t * Complex.I) ^ n = 1 := by
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_int_mul_two_pi_mul_I ((j : ℤ) - m) using 2
    rw [ht]
    push_cast
    field_simp
  have hsum := geom_sum_eq hz n
  rw [hzn, sub_self, zero_div] at hsum
  simp_rw [← hk] at hsum
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  rw [Complex.re_sum] at hre
  rw [Complex.im_sum] at him
  simp only [Complex.exp_ofReal_mul_I_re, Complex.zero_re] at hre
  simp only [Complex.exp_ofReal_mul_I_im, Complex.zero_im] at him
  exact ⟨hre, him⟩

/-- The exact inversion: for `X_k = Σ_j (a_j + i b_j) e ^ (-i θ_jk)` with `θ_jk = 2 π j k / n`,
`Σ_k X_k e ^ (i θ_km) = n (a_m + i b_m)`, in real and imaginary parts. -/
theorem inversion (n : ℕ) (a b : ℕ → ℝ) (m : ℕ) (hm : m < n) :
    ∑ k ∈ Finset.range n,
        ((∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
            b j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n) -
          (∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
            a j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n)) =
      n * a m ∧
    ∑ k ∈ Finset.range n,
        ((∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
            b j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n) +
          (∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
            a j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n)) =
      n * b m := by
  have hd : ∀ j k : ℕ, 2 * Real.pi * j * k / n - 2 * Real.pi * k * m / n =
      2 * Real.pi * k * ((j : ℝ) - m) / n := fun j k => by ring
  have hre : ∀ k : ℕ,
      (∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
          b j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n) -
        (∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
          a j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n) =
      ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * k * ((j : ℝ) - m) / n) +
        b j * Real.sin (2 * Real.pi * k * ((j : ℝ) - m) / n)) := fun k => by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hd, Real.cos_sub, Real.sin_sub]
    ring
  have him : ∀ k : ℕ,
      (∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
          b j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n) +
        (∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
          a j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n) =
      ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * k * ((j : ℝ) - m) / n) -
        a j * Real.sin (2 * Real.pi * k * ((j : ℝ) - m) / n)) := fun k => by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hd, Real.cos_sub, Real.sin_sub]
    ring
  simp_rw [hre, him]
  constructor
  · rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j hj => show ∑ k ∈ Finset.range n,
        (a j * Real.cos (2 * Real.pi * k * ((j : ℝ) - m) / n) +
          b j * Real.sin (2 * Real.pi * k * ((j : ℝ) - m) / n)) = if j = m then n * a j else 0 by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        (sum_cos_sin n j m (Finset.mem_range.mp hj) hm).1,
        (sum_cos_sin n j m (Finset.mem_range.mp hj) hm).2]
      split_ifs <;> ring]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hm)]
  · rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j hj => show ∑ k ∈ Finset.range n,
        (b j * Real.cos (2 * Real.pi * k * ((j : ℝ) - m) / n) -
          a j * Real.sin (2 * Real.pi * k * ((j : ℝ) - m) / n)) = if j = m then n * b j else 0 by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        (sum_cos_sin n j m (Finset.mem_range.mp hj) hm).1,
        (sum_cos_sin n j m (Finset.mem_range.mp hj) hm).2]
      split_ifs <;> ring]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr hm)]

/-- Values `Yr_k` and `Yi_k` within `E` of the real and imaginary parts of the transform of
`a + i b` have `Σ_k (|Yr_k| + |Yi_k|) ≤ 2 n (M + E)` for `M = Σ_j (|a_j| + |b_j|)`. -/
theorem dft_mass (n : ℕ) (a b Yr Yi : ℕ → ℝ) (M E : ℝ)
    (hM : ∑ j ∈ Finset.range n, (|a j| + |b j|) = M)
    (hY : ∀ k < n,
      |Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
          b j * Real.sin (2 * Real.pi * j * k / n))| ≤ E ∧
      |Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
          a j * Real.sin (2 * Real.pi * j * k / n))| ≤ E) :
    ∑ k ∈ Finset.range n, (|Yr k| + |Yi k|) ≤ 2 * n * (M + E) := by
  subst hM
  calc ∑ k ∈ Finset.range n, (|Yr k| + |Yi k|)
      ≤ ∑ k ∈ Finset.range n, 2 * (∑ j ∈ Finset.range n, (|a j| + |b j|) + E) :=
        Finset.sum_le_sum fun k hk => by
          obtain ⟨h0, h1⟩ := hY k (Finset.mem_range.mp hk)
          have hX := abs_sum_trig n a b (fun j => Real.cos (2 * Real.pi * j * k / n))
            (fun j => -Real.sin (2 * Real.pi * j * k / n)) (fun _ => Real.abs_cos_le_one _)
            (fun _ => by rw [abs_neg]; exact Real.abs_sin_le_one _)
          have e0 : ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) -
              b j * -Real.sin (2 * Real.pi * j * k / n)) =
              ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
                b j * Real.sin (2 * Real.pi * j * k / n)) :=
            Finset.sum_congr rfl fun j _ => by ring
          have e1 : ∑ j ∈ Finset.range n, (a j * -Real.sin (2 * Real.pi * j * k / n) +
              b j * Real.cos (2 * Real.pi * j * k / n)) =
              ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
                a j * Real.sin (2 * Real.pi * j * k / n)) :=
            Finset.sum_congr rfl fun j _ => by ring
          obtain ⟨x0, x1⟩ := hX
          rw [e0] at x0
          rw [e1] at x1
          have := abs_sub_abs_le_abs_sub (Yr k) (∑ j ∈ Finset.range n,
            (a j * Real.cos (2 * Real.pi * j * k / n) + b j * Real.sin (2 * Real.pi * j * k / n)))
          have := abs_sub_abs_le_abs_sub (Yi k) (∑ j ∈ Finset.range n,
            (b j * Real.cos (2 * Real.pi * j * k / n) - a j * Real.sin (2 * Real.pi * j * k / n)))
          linarith
    _ = 2 * n * (∑ j ∈ Finset.range n, (|a j| + |b j|) + E) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- `γ_(n-1) = (n - 1) / (2 ^ 53 - (n - 1))` lies between `0` and `(n - 1) / 2 ^ 53 + 2 ^ -47`
for `n ≤ 2 ^ 29`. -/
theorem gamma_le (n : ℕ) (hn : n ≤ 2 ^ 29) :
    0 ≤ ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) ∧
      ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) ≤ ((n - 1 : ℕ) : ℝ) / 2 ^ 53 + 1 / 2 ^ 47 := by
  have hN : ((n - 1 : ℕ) : ℝ) ≤ 2 ^ 29 := by exact_mod_cast (show n - 1 ≤ 2 ^ 29 by omega)
  have hN0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) < 2 ^ 53 - (n - 1 : ℕ) := by linarith
  refine ⟨div_nonneg hN0 hd.le, ?_⟩
  rw [div_le_iff₀ hd]
  nlinarith

/-- For `n ≤ 2 ^ 29` and `M = Σ_j (|a_j| + |b_j|)`, values `Yr_k` and `Yi_k` within
`E = (γ_(n-1) + 2 ^ -46) M + n / 2 ^ 1071` of the parts of the transform of `a + i b`, and values
`zr_m` and `zi_m` within `(γ_(n-1) + 2 ^ -45) Σ_k (|Yr_k| + |Yi_k|) / n + 2 ^ -1069` of the parts of
the inverse transform of `Yr + i Yi`, lie within `(n + 512) M / 2 ^ 51 + 2 ^ -1040` of `a_m` and
`b_m`. -/
theorem roundtrip_real (n : ℕ) (hn : n ≤ 2 ^ 29) (a b Yr Yi zr zi : ℕ → ℝ) (M : ℝ)
    (hM : ∑ j ∈ Finset.range n, (|a j| + |b j|) = M)
    (hY : ∀ k < n,
      |Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
          b j * Real.sin (2 * Real.pi * j * k / n))| ≤
        (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) * M + n / 2 ^ 1071 ∧
      |Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
          a j * Real.sin (2 * Real.pi * j * k / n))| ≤
        (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) * M + n / 2 ^ 1071)
    (hz : ∀ m < n,
      |zr m - (∑ k ∈ Finset.range n, (Yr k * Real.cos (2 * Real.pi * k * m / n) -
          Yi k * Real.sin (2 * Real.pi * k * m / n))) / n| ≤
        (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 45) *
          (∑ k ∈ Finset.range n, (|Yr k| + |Yi k|)) / n + 1 / 2 ^ 1069 ∧
      |zi m - (∑ k ∈ Finset.range n, (Yr k * Real.sin (2 * Real.pi * k * m / n) +
          Yi k * Real.cos (2 * Real.pi * k * m / n))) / n| ≤
        (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 45) *
          (∑ k ∈ Finset.range n, (|Yr k| + |Yi k|)) / n + 1 / 2 ^ 1069) :
    ∀ m < n, |zr m - a m| ≤ ((n : ℝ) + 512) / 2 ^ 51 * M + 1 / 2 ^ 1040 ∧
      |zi m - b m| ≤ ((n : ℝ) + 512) / 2 ^ 51 * M + 1 / 2 ^ 1040 := by
  intro m hm
  obtain ⟨hγ0, hγ1⟩ := gamma_le n hn
  set γ := ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) with hγ
  set E := (γ + 1 / 2 ^ 46) * M + n / 2 ^ 1071 with hE
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn29 : (n : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hn
  have hN : ((n - 1 : ℕ) : ℝ) ≤ 2 ^ 29 := by exact_mod_cast (show n - 1 ≤ 2 ^ 29 by omega)
  have hnN : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hM0 : 0 ≤ M := hM ▸ Finset.sum_nonneg fun _ _ => by positivity
  have hE0 : 0 ≤ E := add_nonneg (mul_nonneg (by linarith) hM0) (by positivity)
  have hMY := dft_mass n a b Yr Yi M E hM fun k hk => hY k hk
  have hMYn : (∑ k ∈ Finset.range n, (|Yr k| + |Yi k|)) / n ≤ 2 * (M + E) := by
    rw [div_le_iff₀ hnr]
    linarith
  have hδ : ∑ k ∈ Finset.range n,
      (|Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
          b j * Real.sin (2 * Real.pi * j * k / n))| +
        |Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
          a j * Real.sin (2 * Real.pi * j * k / n))|) ≤ n * (2 * E) := by
    calc _ ≤ ∑ k ∈ Finset.range n, 2 * E := Finset.sum_le_sum fun k hk => by
            have := hY k (Finset.mem_range.mp hk)
            linarith [this.1, this.2]
      _ = n * (2 * E) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD := abs_sum_trig n
    (fun k => Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
      b j * Real.sin (2 * Real.pi * j * k / n)))
    (fun k => Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
      a j * Real.sin (2 * Real.pi * j * k / n)))
    (fun k => Real.cos (2 * Real.pi * k * m / n)) (fun k => Real.sin (2 * Real.pi * k * m / n))
    (fun _ => Real.abs_cos_le_one _) (fun _ => Real.abs_sin_le_one _)
  obtain ⟨i0, i1⟩ := inversion n a b m hm
  have hT0 : |(∑ k ∈ Finset.range n, (Yr k * Real.cos (2 * Real.pi * k * m / n) -
      Yi k * Real.sin (2 * Real.pi * k * m / n))) / n - a m| ≤ 2 * E := by
    have hsplit : ∑ k ∈ Finset.range n, (Yr k * Real.cos (2 * Real.pi * k * m / n) -
        Yi k * Real.sin (2 * Real.pi * k * m / n)) = n * a m +
        ∑ k ∈ Finset.range n,
          ((Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
              b j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n) -
            (Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
              a j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n)) := by
      rw [← i0, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, add_div, mul_div_cancel_left₀ _ hnr.ne', add_sub_cancel_left, abs_div,
      abs_of_pos hnr, div_le_iff₀ hnr]
    exact (hD.1.trans hδ).trans (le_of_eq (by ring))
  have hT1 : |(∑ k ∈ Finset.range n, (Yr k * Real.sin (2 * Real.pi * k * m / n) +
      Yi k * Real.cos (2 * Real.pi * k * m / n))) / n - b m| ≤ 2 * E := by
    have hsplit : ∑ k ∈ Finset.range n, (Yr k * Real.sin (2 * Real.pi * k * m / n) +
        Yi k * Real.cos (2 * Real.pi * k * m / n)) = n * b m +
        ∑ k ∈ Finset.range n,
          ((Yr k - ∑ j ∈ Finset.range n, (a j * Real.cos (2 * Real.pi * j * k / n) +
              b j * Real.sin (2 * Real.pi * j * k / n))) * Real.sin (2 * Real.pi * k * m / n) +
            (Yi k - ∑ j ∈ Finset.range n, (b j * Real.cos (2 * Real.pi * j * k / n) -
              a j * Real.sin (2 * Real.pi * j * k / n))) * Real.cos (2 * Real.pi * k * m / n)) := by
      rw [← i1, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, add_div, mul_div_cancel_left₀ _ hnr.ne', add_sub_cancel_left, abs_div,
      abs_of_pos hnr, div_le_iff₀ hnr]
    exact (hD.2.trans hδ).trans (le_of_eq (by ring))
  have hsmall : γ + 1 / 2 ^ 45 ≤ 1 / 2 ^ 23 := by
    have : ((n - 1 : ℕ) : ℝ) / 2 ^ 53 ≤ 2 ^ 29 / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have : (2 : ℝ) ^ 29 / 2 ^ 53 + 1 / 2 ^ 47 + 1 / 2 ^ 45 ≤ 1 / 2 ^ 23 := by norm_num
    linarith
  have hc : 4 * γ + 3 / 2 ^ 45 + 2 * (γ + 1 / 2 ^ 45) * (γ + 1 / 2 ^ 46) ≤
      ((n : ℝ) + 512) / 2 ^ 51 := by
    have hp : 2 * (γ + 1 / 2 ^ 45) * (γ + 1 / 2 ^ 46) ≤ 2 * (1 / 2 ^ 23) * (1 / 2 ^ 23) := by
      have h46 : γ + 1 / 2 ^ 46 ≤ 1 / 2 ^ 23 := by
        have : (1 : ℝ) / 2 ^ 46 ≤ 1 / 2 ^ 45 := by norm_num
        linarith
      have := mul_le_mul hsmall h46 (by linarith) (by norm_num)
      linarith
    have : (2 : ℝ) * (1 / 2 ^ 23) * (1 / 2 ^ 23) = 1 / 2 ^ 45 := by norm_num
    rw [hnN]
    have : ((n - 1 : ℕ) : ℝ) / 2 ^ 53 * 4 = ((n - 1 : ℕ) : ℝ) / 2 ^ 51 := by ring
    have : ((((n - 1 : ℕ) : ℝ) + 1) + 512) / 2 ^ 51 =
        ((n - 1 : ℕ) : ℝ) / 2 ^ 51 + 513 / 2 ^ 51 := by ring
    have : (1 : ℝ) / 2 ^ 47 * 4 + 3 / 2 ^ 45 + 1 / 2 ^ 45 ≤ 513 / 2 ^ 51 := by norm_num
    linarith
  have hK : 2 * (γ + 1 / 2 ^ 45) * (n / 2 ^ 1071) + 2 * (n / 2 ^ 1071) + 1 / 2 ^ 1069 ≤
      1 / 2 ^ 1040 := by
    have h1 : (n : ℝ) / 2 ^ 1071 ≤ 2 ^ 29 / 2 ^ 1071 :=
      div_le_div_of_nonneg_right hn29 (by positivity)
    have h2 : 2 * (γ + 1 / 2 ^ 45) * (n / 2 ^ 1071) ≤ 2 * (1 / 2 ^ 23) * (2 ^ 29 / 2 ^ 1071) :=
      mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
    have : (2 : ℝ) * (1 / 2 ^ 23) * (2 ^ 29 / 2 ^ 1071) + 2 * (2 ^ 29 / 2 ^ 1071) +
        1 / 2 ^ 1069 ≤ 1 / 2 ^ 1040 := by norm_num
    linarith
  have htotal : 2 * E + ((γ + 1 / 2 ^ 45) * (2 * (M + E)) + 1 / 2 ^ 1069) ≤
      ((n : ℝ) + 512) / 2 ^ 51 * M + 1 / 2 ^ 1040 := by
    have e : 2 * E + ((γ + 1 / 2 ^ 45) * (2 * (M + E)) + 1 / 2 ^ 1069) =
        (4 * γ + 3 / 2 ^ 45 + 2 * (γ + 1 / 2 ^ 45) * (γ + 1 / 2 ^ 46)) * M +
          (2 * (γ + 1 / 2 ^ 45) * (n / 2 ^ 1071) + 2 * (n / 2 ^ 1071) + 1 / 2 ^ 1069) := by
      rw [hE]
      ring
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_right hc hM0) hK
  have hinv : (γ + 1 / 2 ^ 45) * (∑ k ∈ Finset.range n, (|Yr k| + |Yi k|)) / n + 1 / 2 ^ 1069 ≤
      (γ + 1 / 2 ^ 45) * (2 * (M + E)) + 1 / 2 ^ 1069 := by
    rw [mul_div_assoc]
    have : 0 ≤ γ + 1 / 2 ^ 45 := by linarith
    have := mul_le_mul_of_nonneg_left hMYn this
    linarith
  obtain ⟨z0, z1⟩ := hz m hm
  constructor
  · calc |zr m - a m| ≤ |zr m - (∑ k ∈ Finset.range n, (Yr k * Real.cos (2 * Real.pi * k * m / n) -
            Yi k * Real.sin (2 * Real.pi * k * m / n))) / n| +
          |(∑ k ∈ Finset.range n, (Yr k * Real.cos (2 * Real.pi * k * m / n) -
            Yi k * Real.sin (2 * Real.pi * k * m / n))) / n - a m| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · calc |zi m - b m| ≤ |zi m - (∑ k ∈ Finset.range n, (Yr k * Real.sin (2 * Real.pi * k * m / n) +
            Yi k * Real.cos (2 * Real.pi * k * m / n))) / n| +
          |(∑ k ∈ Finset.range n, (Yr k * Real.sin (2 * Real.pi * k * m / n) +
            Yi k * Real.cos (2 * Real.pi * k * m / n))) / n - b m| := abs_sub_le _ _ _
      _ ≤ _ := by linarith

/-- `inverse (dft xs)`, for an array `xs` of fewer than `2 ^ 30` finite floats holding
`n = ⌊xs.size / 2⌋` complex values with `M = Σ_j (|a_j| + |b_j|) ≤ 2 ^ 960`, has `2 n` floats,
each finite and within `(n + 512) M / 2 ^ 51 + 2 ^ -1040` of the float of `xs` at its index. -/
theorem inverse_dft (xs : Array Float) (hs : xs.size < 2 ^ 30) (hf : ∀ v ∈ xs, Finite v.toBits)
    (hM : ∑ j ∈ Finset.range (xs.size / 2),
      (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) ≤ 2 ^ 960) :
    (inverse (dft xs)).size = 2 * (xs.size / 2) ∧ ∀ i < 2 * (xs.size / 2),
      Finite (inverse (dft xs))[i]!.toBits ∧
      |value (inverse (dft xs))[i]!.toBits - value xs[i]!.toBits| ≤
        ((xs.size / 2 : ℕ) + 512) / 2 ^ 51 *
          ∑ j ∈ Finset.range (xs.size / 2),
            (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) +
          1 / 2 ^ 1040 := by
  obtain ⟨hysz, hY⟩ := dft_spec xs hs hf (hM.trans (by norm_num))
  set n := xs.size / 2 with hn
  set M := ∑ j ∈ Finset.range n, (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)
    with hMdef
  set ys := dft xs with hys
  have hyn : ys.size / 2 = n := by omega
  have hn29 : n ≤ 2 ^ 29 := by omega
  have hyf : ∀ v ∈ ys, Finite v.toBits := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hv
    rw [← getElem!_pos ys i hi]
    obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega⟩
    · exact (hY k (by omega)).1.1
    · exact (hY k (by omega)).2.1
  have hmass := dft_mass n (fun j => value xs[2 * j]!.toBits)
    (fun j => value xs[2 * j + 1]!.toBits) (fun k => value ys[2 * k]!.toBits)
    (fun k => value ys[2 * k + 1]!.toBits) M _ rfl fun k hk => ⟨(hY k hk).1.2, (hY k hk).2.2⟩
  have hYM : ∑ j ∈ Finset.range (ys.size / 2),
      (|value ys[2 * j]!.toBits| + |value ys[2 * j + 1]!.toBits|) ≤ 2 ^ 1000 := by
    rw [hyn]
    refine hmass.trans ?_
    obtain ⟨hγ0, hγ1⟩ := gamma_le n hn29
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => by positivity
    have hn29r : (n : ℝ) ≤ 2 ^ 29 := by exact_mod_cast hn29
    have hN : ((n - 1 : ℕ) : ℝ) / 2 ^ 53 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : ((n - 1 : ℕ) : ℝ) ≤ 2 ^ 29 := by exact_mod_cast (show n - 1 ≤ 2 ^ 29 by omega)
      linarith
    have hE : (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) * M +
        (n : ℝ) / 2 ^ 1071 ≤ 3 * 2 ^ 960 + 1 := by
      have h1 : ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46 ≤ 3 := by
        have : (1 : ℝ) / 2 ^ 47 + 1 / 2 ^ 46 ≤ 1 := by norm_num
        linarith
      have h2 : (n : ℝ) / 2 ^ 1071 ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [show (2 : ℝ) ^ 29 ≤ 2 ^ 1071 by norm_num]
      have := mul_le_mul h1 hM hM0 (by norm_num)
      linarith
    have hE0 : 0 ≤ (((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) * M +
        (n : ℝ) / 2 ^ 1071 := add_nonneg (mul_nonneg (by linarith) hM0) (by positivity)
    have h3 : M + ((((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) * M +
        (n : ℝ) / 2 ^ 1071) ≤ 4 * 2 ^ 960 + 1 := by linarith
    have := mul_le_mul (show 2 * (n : ℝ) ≤ 2 * 2 ^ 29 by linarith) h3 (by linarith)
      (by norm_num)
    have : (2 : ℝ) * 2 ^ 29 * (4 * 2 ^ 960 + 1) ≤ 2 ^ 1000 := by norm_num
    linarith
  obtain ⟨hzsz, hz⟩ := inverse_spec ys (by omega) hyf hYM
  rw [hyn] at hzsz hz
  have hr := roundtrip_real n hn29 (fun j => value xs[2 * j]!.toBits)
    (fun j => value xs[2 * j + 1]!.toBits) (fun k => value ys[2 * k]!.toBits)
    (fun k => value ys[2 * k + 1]!.toBits) (fun m => value (inverse ys)[2 * m]!.toBits)
    (fun m => value (inverse ys)[2 * m + 1]!.toBits) M rfl
    (fun k hk => ⟨(hY k hk).1.2, (hY k hk).2.2⟩) (fun m hm => ⟨(hz m hm).1.2, (hz m hm).2.2⟩)
  refine ⟨hzsz, fun i hi => ?_⟩
  obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega⟩
  · exact ⟨(hz k (by omega)).1.1, (hr k (by omega)).1⟩
  · exact ⟨(hz k (by omega)).2.1, (hr k (by omega)).2⟩

#print axioms inverse_dft

end Library.Numerics.Fourier
