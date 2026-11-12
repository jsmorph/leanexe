import Library.Numerics.Fourier.Transform
import Verified.Master

/-!
The master theorems of the discrete Fourier transform.  A signal of `n` complex values
`x_j = a_j + i b_j` is the array `xs` of `2 n` floats `a_0, b_0, a_1, b_1, …`, and
`θ_jk = 2 π j k / n`.
-/

namespace Library.Numerics.Fourier

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit LeanExe.ProofKit.F64Approx
open Library.Numerics.Reductions.Binary64 (toFloat_exact)

set_option exponentiation.threshold 4096

theorem twiddle_export :
    ({ name := "twiddle", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem dft_export :
    ({ name := "dft", funcIdx := 21 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem inverse_export :
    ({ name := "inverse", funcIdx := 22 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem powerSpectrum_export :
    ({ name := "powerSpectrum", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem size_lt {xs : Array Float} (h : (xs.map Float.toBits).size < 536870912) :
    xs.size < 536870912 := by
  simpa using h

/-- The export `twiddle`, called on words `n` and `m` with `0 ≤ m < n ≤ 2 ^ 53`, returns two finite
floats within `2 ^ -48` of `cos (2 π m / n)` and `sin (2 π m / n)`. -/
theorem twiddle_master :
    Verified.Master compiled.module compiled.tables "twiddle" compiled.twiddle.bound
      (fun x : UInt64 × UInt64 => 0 < x.1.toNat ∧ x.2.toNat < x.1.toNat ∧ x.1.toNat ≤ 2 ^ 53)
      (fun x (y : Float × Float) => Finite y.1.toBits ∧ Finite y.2.toBits ∧
        |value y.1.toBits - Real.cos (2 * Real.pi * x.2.toNat / x.1.toNat)| ≤ 1 / 2 ^ 48 ∧
        |value y.2.toBits - Real.sin (2 * Real.pi * x.2.toNat / x.1.toNat)| ≤ 1 / 2 ^ 48) :=
  .of_trapFree compiled.twiddle.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    twiddle_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hD => twiddle_spec x.1 x.2 hD.1 hD.2.1 hD.2.2

#print axioms twiddle_master

/-- The export `dft`, called on an array `xs` of finite floats holding `n = ⌊xs.size / 2⌋`
complex values with `Σ_j (|a_j| + |b_j|) ≤ 2 ^ 1000`, returns `2 n` floats, the pair `2 k`,
`2 k + 1` finite and within `(γ_(n-1) + 2 ^ -46) Σ_j (|a_j| + |b_j|) + n / 2 ^ 1071` of the real
and imaginary parts of `X_k = Σ_j x_j e ^ (-i θ_jk)`, where `γ_k = k / (2 ^ 53 - k)`. -/
theorem dft_master :
    Verified.Master compiled.module compiled.tables "dft" compiled.dft.bound
      (fun xs : Array Float => (∀ v ∈ xs, Finite v.toBits) ∧
        ∑ j ∈ Finset.range (xs.size / 2),
          (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) ≤ 2 ^ 1000)
      (fun xs (y : Array Float) => y.size = 2 * (xs.size / 2) ∧ ∀ k < xs.size / 2,
        Finite y[2 * k]!.toBits ∧ Finite y[2 * k + 1]!.toBits ∧
        |value y[2 * k]!.toBits - ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) +
              value xs[2 * j + 1]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))| ≤
          (((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 46) *
            ∑ j ∈ Finset.range (xs.size / 2),
              (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) +
            (xs.size / 2 : ℕ) / 2 ^ 1071 ∧
        |value y[2 * k + 1]!.toBits - ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
              value xs[2 * j]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))| ≤
          (((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 46) *
            ∑ j ∈ Finset.range (xs.size / 2),
              (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) +
            (xs.size / 2 : ℕ) / 2 ^ 1071) :=
  .of_trapFree compiled.dft.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    dft_export (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hD => by
      have hs : xs.size < 2 ^ 30 := by have := size_lt hxs.values.size_lt_memory32; omega
      have hdft : dft xs = transformWith Library.Numerics.Float64.Trig.invPi
          Library.Numerics.Float64.Trig.halfPi (-1.0) xs := rfl
      rw [hdft]
      obtain ⟨hsz, hg⟩ := transform_get (-1.0) xs hs
      refine ⟨hsz, fun k hk => ?_⟩
      obtain ⟨e0, e1⟩ := hg k hk
      obtain ⟨h0, h1⟩ := transform_spec (-1.0) (-1) neg_one_approx (by norm_num) xs hs hD.1
        hD.2 k hk
      rw [e0, e1]
      refine ⟨h0.1, h1.1, ?_, ?_⟩
      · have heq : ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) +
              value xs[2 * j + 1]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) =
            ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
              value xs[2 * j + 1]!.toBits *
                (-1 * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        exact h0.2
      · have heq : ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
              value xs[2 * j]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) =
            ∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * (-1 * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) +
              value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [heq]
        exact h1.2

#print axioms dft_master

/-- The inverse transform divides each sum by `n`: within `(γ_(n-1) + 2 ^ -45) M / n + 2 ^ -1069`
of the exact quotient, for the bound `(γ_(n-1) + 2 ^ -46) M + n / 2 ^ 1071` of the sum. -/
theorem div_bound (Y : Float) (nf : Float) (V M γ : ℝ) (n : ℕ) (hn : 0 < n) (hnf : FApprox nf n 0)
    (hY : FApprox Y V ((γ + 1 / 2 ^ 46) * M + n / 2 ^ 1071)) (hVM : |V| ≤ M) (hM : M ≤ 2 ^ 1000)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hn52 : (n : ℝ) ≤ 2 ^ 52) :
    FApprox (Y / nf) (V / n) ((γ + 1 / 2 ^ 45) * M / n + 1 / 2 ^ 1069) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hVM
  set E := (γ + 1 / 2 ^ 46) * M + n / 2 ^ 1071 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEM : E ≤ 2 * M + 2 ^ 52 / 2 ^ 1071 := by
    have : (γ + 1 / 2 ^ 46) * M ≤ 2 * M := mul_le_mul_of_nonneg_right (by
      have : (1 : ℝ) / 2 ^ 46 ≤ 1 := by norm_num
      linarith) hM0
    have : (n : ℝ) / 2 ^ 1071 ≤ 2 ^ 52 / 2 ^ 1071 := div_le_div_of_nonneg_right hn52 (by positivity)
    linarith
  have hB : (M + E) / n < 2 ^ 1022 := by
    have h1 : (M + E) / n ≤ M + E := div_le_self (by positivity) hn1
    have : (2 : ℝ) ^ 1000 + (2 * 2 ^ 1000 + 2 ^ 52 / 2 ^ 1071) < 2 ^ 1022 := by norm_num
    linarith
  have hd := fapprox_div hY hnf M n hVM (by rw [abs_of_pos hnr]) hnr ((M + E) / n)
    (by rw [sub_zero]) hB
  refine hd.mono ?_
  simp only [mul_zero, zero_div, add_zero, sub_zero]
  have key : E + (M + E) / 2 ^ 53 ≤ (γ + 1 / 2 ^ 45) * M + n * (1 / 2 ^ 1070) := by
    rw [hE]
    have : γ * M / 2 ^ 53 ≤ M / 2 ^ 53 := div_le_div_of_nonneg_right
      (by nlinarith) (by positivity)
    have : (n : ℝ) / 2 ^ 1071 / 2 ^ 53 ≤ n / 2 ^ 1071 := div_le_self (by positivity) (by norm_num)
    have : (2 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 1070 := by norm_num
    nlinarith
  have e1 : E / n + (M + E) / n / 2 ^ 53 = (E + (M + E) / 2 ^ 53) / n := by
    field_simp
  rw [e1]
  have e2 : (E + (M + E) / 2 ^ 53) / n ≤ ((γ + 1 / 2 ^ 45) * M + n * (1 / 2 ^ 1070)) / n :=
    div_le_div_of_nonneg_right key hnr.le
  have e3 : ((γ + 1 / 2 ^ 45) * M + n * (1 / 2 ^ 1070)) / n =
      (γ + 1 / 2 ^ 45) * M / n + 1 / 2 ^ 1070 := by
    field_simp
  have e4 : (1 : ℝ) / 2 ^ 1070 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 1069 := by norm_num
  linarith

theorem abs_sum_trig (n : ℕ) (a b C S : ℕ → ℝ) (hC : ∀ j, |C j| ≤ 1) (hS : ∀ j, |S j| ≤ 1) :
    |∑ j ∈ Finset.range n, (a j * C j - b j * S j)| ≤ ∑ j ∈ Finset.range n, (|a j| + |b j|) ∧
      |∑ j ∈ Finset.range n, (a j * S j + b j * C j)| ≤ ∑ j ∈ Finset.range n, (|a j| + |b j|) := by
  have hab : ∀ x y : ℝ, ∀ j, |x * C j| + |y * S j| ≤ |x| + |y| := fun x y j => by
    rw [abs_mul, abs_mul]
    nlinarith [hC j, hS j, abs_nonneg x, abs_nonneg y, abs_nonneg (C j), abs_nonneg (S j)]
  constructor
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc |a j * C j - b j * S j| ≤ |a j * C j| + |b j * S j| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ |a j| + |b j| := hab _ _ j
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc |a j * S j + b j * C j| ≤ |b j * C j| + |a j * S j| := by
          rw [add_comm]; exact abs_add_le _ _
      _ ≤ |b j| + |a j| := hab _ _ j
      _ = |a j| + |b j| := by ring

/-- The export `inverse`, called on an array `xs` of finite floats holding `n = ⌊xs.size / 2⌋`
complex values with `Σ_j (|a_j| + |b_j|) ≤ 2 ^ 1000`, returns `2 n` floats, the pair `2 k`,
`2 k + 1` finite and within `(γ_(n-1) + 2 ^ -45) Σ_j (|a_j| + |b_j|) / n + 2 ^ -1069` of the real
and imaginary parts of `(1 / n) Σ_j x_j e ^ (i θ_jk)`, where `γ_k = k / (2 ^ 53 - k)`. -/
theorem inverse_master :
    Verified.Master compiled.module compiled.tables "inverse" compiled.inverse.bound
      (fun xs : Array Float => (∀ v ∈ xs, Finite v.toBits) ∧
        ∑ j ∈ Finset.range (xs.size / 2),
          (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) ≤ 2 ^ 1000)
      (fun xs (y : Array Float) => y.size = 2 * (xs.size / 2) ∧ ∀ k < xs.size / 2,
        Finite y[2 * k]!.toBits ∧ Finite y[2 * k + 1]!.toBits ∧
        |value y[2 * k]!.toBits - (∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
              value xs[2 * j + 1]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))) /
            (xs.size / 2 : ℕ)| ≤
          (((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 45) *
            (∑ j ∈ Finset.range (xs.size / 2),
              (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)) / (xs.size / 2 : ℕ) +
            1 / 2 ^ 1069 ∧
        |value y[2 * k + 1]!.toBits - (∑ j ∈ Finset.range (xs.size / 2),
            (value xs[2 * j]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) +
              value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))) /
            (xs.size / 2 : ℕ)| ≤
          (((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 45) *
            (∑ j ∈ Finset.range (xs.size / 2),
              (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)) / (xs.size / 2 : ℕ) +
            1 / 2 ^ 1069) :=
  .of_trapFree compiled.inverse.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    inverse_export (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hD => by
      have hs : xs.size < 2 ^ 30 := by have := size_lt hxs.values.size_lt_memory32; omega
      set ys := transformWith Library.Numerics.Float64.Trig.invPi
        Library.Numerics.Float64.Trig.halfPi 1.0 xs with hys
      have hinv : inverse xs = LeanExe.loop ys.size.toUInt64 ys fun i acc =>
          acc.set! i.toNat (acc[i.toNat]! / (xs.size.toUInt64 / 2).toFloat) := rfl
      obtain ⟨hsz, hg⟩ := transform_get 1.0 xs hs
      obtain ⟨hmsz, hmg⟩ := map_loop ys (fun v => v / (xs.size.toUInt64 / 2).toFloat)
        (by rw [hsz]; omega)
      rw [hinv]
      refine ⟨by rw [hmsz, hsz], fun k hk => ?_⟩
      rw [hmg (2 * k) (by rw [hsz]; omega), hmg (2 * k + 1) (by rw [hsz]; omega)]
      obtain ⟨e0, e1⟩ := hg k hk
      rw [e0, e1]
      obtain ⟨h0, h1⟩ := transform_spec 1.0 1 one_approx (by norm_num) xs hs hD.1 hD.2 k hk
      have hN := half_toNat xs (by omega)
      have hnf : FApprox (xs.size.toUInt64 / 2).toFloat ((xs.size / 2 : ℕ) : ℝ) 0 := by
        have := toFloat_exact (xs.size.toUInt64 / 2) (by rw [hN]; omega)
        rwa [hN] at this
      have hn0 : 0 < xs.size / 2 := by omega
      have hn52 : ((xs.size / 2 : ℕ) : ℝ) ≤ 2 ^ 52 := by exact_mod_cast (show xs.size / 2 ≤ 2 ^ 52 by omega)
      have hγ0 : 0 ≤ ((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) :=
        div_nonneg (Nat.cast_nonneg _) (by
          have : ((xs.size / 2 - 1 : ℕ) : ℝ) ≤ 2 ^ 52 := by
            exact_mod_cast (show xs.size / 2 - 1 ≤ 2 ^ 52 by omega)
          linarith)
      have hγ1 : ((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) ≤ 1 := by
        have : ((xs.size / 2 - 1 : ℕ) : ℝ) ≤ 2 ^ 52 := by
          exact_mod_cast (show xs.size / 2 - 1 ≤ 2 ^ 52 by omega)
        rw [div_le_one (by linarith)]
        linarith
      have hsum := abs_sum_trig (xs.size / 2) (fun j => value xs[2 * j]!.toBits)
        (fun j => value xs[2 * j + 1]!.toBits)
        (fun j => Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))
        (fun j => Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))
        (fun _ => Real.abs_cos_le_one _) (fun _ => Real.abs_sin_le_one _)
      have heq0 : ∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
            value xs[2 * j + 1]!.toBits * (1 * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))) =
          ∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
            value xs[2 * j + 1]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) :=
        Finset.sum_congr rfl fun j _ => by ring
      have heq1 : ∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * (1 * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) +
            value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) =
          ∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) +
            value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [heq0] at h0
      rw [heq1] at h1
      have d0 := div_bound _ _ _ _ _ _ hn0 hnf h0 hsum.1 hD.2 hγ0 hγ1 hn52
      have d1 := div_bound _ _ _ _ _ _ hn0 hnf h1 hsum.2 hD.2 hγ0 hγ1 hn52
      exact ⟨d0.1, d1.1, d0.2, d1.2⟩

#print axioms inverse_master

/-! ### `powerSpectrum` -/

/-- `a ⊗ a ⊕ b ⊗ b` for `a` and `b` within `E` of `A` and `B`, `|A|, |B| ≤ M`. -/
theorem square_sum (a b : Float) (A B M E : ℝ) (ha : FApprox a A E) (hb : FApprox b B E)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hM : M ≤ 2 ^ 500) (hE0 : 0 ≤ E) (hE : E ≤ 2 * M + 1) :
    FApprox (a * a + b * b) (A ^ 2 + B ^ 2)
      (5 * M * E + 3 * E ^ 2 + 5 * M ^ 2 / 2 ^ 53 + 3 / 2 ^ 1075) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hA
  have hME : M + E ≤ 2 ^ 502 := by
    have : (3 : ℝ) * 2 ^ 500 + 1 ≤ 2 ^ 502 := by norm_num
    linarith
  have hsq : (M + E) * (M + E) ≤ 2 ^ 1004 := by
    have := mul_le_mul hME hME (by linarith) (by positivity)
    have e : (2 : ℝ) ^ 502 * 2 ^ 502 = 2 ^ 1004 := by norm_num
    linarith
  have hsa := fapprox_mul ha ha M M hA hA ((M + E) * (M + E)) le_rfl (by
    have : (2 : ℝ) ^ 1004 < 2 ^ 1022 := by norm_num
    linarith)
  have hsb := fapprox_mul hb hb M M hB hB ((M + E) * (M + E)) le_rfl (by
    have : (2 : ℝ) ^ 1004 < 2 ^ 1022 := by norm_num
    linarith)
  set e := E * M + M * E + E * E + (M + E) * (M + E) / 2 ^ 53 + 1 / 2 ^ 1075 with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 2 ^ 1006 := by
    have h1 : E * M + M * E + E * E ≤ (M + E) * (M + E) := by nlinarith
    have h2 : (M + E) * (M + E) / 2 ^ 53 ≤ (M + E) * (M + E) :=
      div_le_self (by positivity) (by norm_num)
    have : (2 : ℝ) * 2 ^ 1004 + 1 / 2 ^ 1075 ≤ 2 ^ 1006 := by norm_num
    linarith
  have hAB : |A * A + B * B| ≤ 2 * (M * M) := by
    have h1 : |A * A| ≤ M * M := by rw [abs_mul]; exact mul_le_mul hA hA (abs_nonneg _) hM0
    have h2 : |B * B| ≤ M * M := by rw [abs_mul]; exact mul_le_mul hB hB (abs_nonneg _) hM0
    linarith [abs_add_le (A * A) (B * B)]
  have hMM : M * M ≤ 2 ^ 1000 := by
    have := mul_le_mul hM hM hM0 (by positivity)
    have e : (2 : ℝ) ^ 500 * 2 ^ 500 = 2 ^ 1000 := by norm_num
    linarith
  have hadd := fapprox_add hsa hsb (2 * (M * M) + 2 * e) (by linarith) (by
    have : (2 : ℝ) * 2 ^ 1000 + 2 * 2 ^ 1006 < 2 ^ 1023 := by norm_num
    linarith)
  have hval : A * A + B * B = A ^ 2 + B ^ 2 := by ring
  rw [hval] at hadd
  refine hadd.mono ?_
  have hME0 : 0 ≤ M * E := mul_nonneg hM0 hE0
  have hE2 : 0 ≤ E * E := mul_nonneg hE0 hE0
  have hM2 : 0 ≤ M * M := mul_nonneg hM0 hM0
  rw [he]
  nlinarith

/-- The interleaved signal of real samples, with zero imaginary parts. -/
theorem interleave (s : Array Float) (h : s.size < 2 ^ 29) (hf : ∀ v ∈ s, Finite v.toBits) :
    let xs := LeanExe.build (2 * s.size.toUInt64) fun i =>
      if i % 2 == 0 then s[(i / 2).toNat]! else 0.0
    xs.size = 2 * s.size ∧ (∀ j < s.size, xs[2 * j]! = s[j]! ∧ xs[2 * j + 1]! = 0.0) ∧
      ∀ v ∈ xs, Finite v.toBits := by
  intro xs
  have h64 : ∀ c, c < 2 ^ 31 → (UInt64.ofNat c).toNat = c := fun c hc =>
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hsz : (2 * s.size.toUInt64).toNat = 2 * s.size := by
    rw [UInt64.toNat_mul, LeanExe.Dialect.size_toUInt64 s (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have hxs : xs.size = 2 * s.size := by
    show (LeanExe.build _ _).size = _
    rw [LeanExe.Dialect.build_size, hsz]
  have hget : ∀ i < 2 * s.size, xs[i]! = if i % 2 = 0 then s[i / 2]! else 0.0 := by
    intro i hi
    show (LeanExe.build _ _)[i]! = _
    rw [LeanExe.Dialect.build_get (by rw [hsz]; exact hi)]
    have hm : (UInt64.ofNat i % 2).toNat = i % 2 := by
      rw [UInt64.toNat_mod, h64 i (by omega)]; rfl
    have hd : (UInt64.ofNat i / 2).toNat = i / 2 := by
      rw [UInt64.toNat_div, h64 i (by omega)]; rfl
    by_cases h2 : i % 2 = 0
    · have : (UInt64.ofNat i % 2 == 0) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hm, h2]; rfl
      simp only [this, ↓reduceIte, hd, h2]
    · have : (UInt64.ofNat i % 2 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro he; apply h2
        have := congrArg UInt64.toNat he; rw [hm] at this; exact this
      simp only [this, h2, Bool.false_eq_true, ↓reduceIte]
  refine ⟨hxs, fun j hj => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · rw [hget (2 * j) (by omega), ite_eq_left (by omega), show 2 * j / 2 = j by omega]
  · rw [hget (2 * j + 1) (by omega), ite_eq_right (by omega)]
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hv
    rw [← getElem!_pos xs i hi, hget i (by omega)]
    split
    · exact Library.Numerics.Reductions.Binary64.finite_get s hf _
    · show Finite (0.0 : Float).toBits
      rw [Library.Numerics.Reductions.Binary64.zero_bits]
      exact Library.Numerics.Reductions.Binary64.finite_zero

/-- The export `powerSpectrum`, called on an array of `n` finite floats `s_j` with
`M = Σ_j |s_j| ≤ 2 ^ 500`, returns `n / 2 + 1` finite floats (none for `n = 0`), the float `k`
within `5 M E + 3 E ^ 2 + 5 M ^ 2 / 2 ^ 53 + 3 / 2 ^ 1075` of `|X_k| ^ 2 =
(Σ_j s_j cos θ_jk) ^ 2 + (Σ_j s_j sin θ_jk) ^ 2`, where `E = (γ_(n-1) + 2 ^ -46) M + n / 2 ^ 1071`
is the error of the transform and `γ_k = k / (2 ^ 53 - k)`. -/
theorem powerSpectrum_master :
    Verified.Master compiled.module compiled.tables "powerSpectrum" compiled.powerSpectrum.bound
      (fun s : Array Float => (∀ v ∈ s, Finite v.toBits) ∧
        ∑ j ∈ Finset.range s.size, |value s[j]!.toBits| ≤ 2 ^ 500)
      (fun s (y : Array Float) =>
        let M := ∑ j ∈ Finset.range s.size, |value s[j]!.toBits|
        let E := (((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) + 1 / 2 ^ 46) * M +
          s.size / 2 ^ 1071
        y.size = (if s.size = 0 then 0 else s.size / 2 + 1) ∧ ∀ k < y.size,
          Finite y[k]!.toBits ∧
          |value y[k]!.toBits -
              ((∑ j ∈ Finset.range s.size,
                  value s[j]!.toBits * Real.cos (2 * Real.pi * j * k / s.size)) ^ 2 +
                (∑ j ∈ Finset.range s.size,
                  value s[j]!.toBits * Real.sin (2 * Real.pi * j * k / s.size)) ^ 2)| ≤
            5 * M * E + 3 * E ^ 2 + 5 * M ^ 2 / 2 ^ 53 + 3 / 2 ^ 1075) :=
  .of_trapFree compiled.powerSpectrum.trapFree (Verified.tables_at [0, 1] (by decide) rfl)
    powerSpectrum_export (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ s ⟨_, _, hss⟩ hD => by
      have hs := size_lt hss.values.size_lt_memory32
      obtain ⟨hxsz, hxget, hxf⟩ := interleave s hs hD.1
      set xs := LeanExe.build (2 * s.size.toUInt64) fun i =>
        if i % 2 == 0 then s[(i / 2).toNat]! else 0.0 with hxs
      set ys := transformWith Library.Numerics.Float64.Trig.invPi
        Library.Numerics.Float64.Trig.halfPi (-1.0) xs with hys
      have hps : powerSpectrum s = LeanExe.build
          (if s.size.toUInt64 == 0 then 0 else s.size.toUInt64 / 2 + 1) fun k =>
            ys[(2 * k).toNat]! * ys[(2 * k).toNat]! +
              ys[(2 * k + 1).toNat]! * ys[(2 * k + 1).toNat]! := rfl
      have hhalf : xs.size / 2 = s.size := by rw [hxsz]; omega
      have hxs2 : xs.size < 2 ^ 30 := by rw [hxsz]; omega
      have hcount : (if s.size.toUInt64 == 0 then (0 : UInt64) else s.size.toUInt64 / 2 + 1).toNat =
          if s.size = 0 then 0 else s.size / 2 + 1 := by
        have hN := LeanExe.Dialect.size_toUInt64 s (by omega)
        by_cases hz : s.size = 0
        · have : s.size.toUInt64 = 0 := UInt64.toNat_inj.mp (by rw [hN, hz]; rfl)
          simp [hz]
        · have : (s.size.toUInt64 == 0) = false := by
            rw [beq_eq_false_iff_ne]; intro h0
            have := congrArg UInt64.toNat h0; rw [hN] at this; exact hz this
          simp only [this, Bool.false_eq_true, ↓reduceIte, hz]
          rw [UInt64.toNat_add, UInt64.toNat_div, hN]
          simp only [UInt64.reduceToNat]
          omega
      dsimp only
      rw [hps]
      refine ⟨by rw [LeanExe.Dialect.build_size, hcount], fun k hk => ?_⟩
      rw [LeanExe.Dialect.build_size, hcount] at hk
      have hs0 : s.size ≠ 0 := by intro hz; rw [ite_eq_left hz] at hk; omega
      rw [ite_eq_right hs0] at hk
      have hkN : k < s.size := by omega
      have hk64 : (UInt64.ofNat k).toNat = k :=
        UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
      have i0 : (2 * UInt64.ofNat k).toNat = 2 * k := by
        rw [UInt64.toNat_mul, hk64]; simp only [UInt64.reduceToNat]; omega
      have i1 : (2 * UInt64.ofNat k + 1).toNat = 2 * k + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, hk64]; simp only [UInt64.reduceToNat]; omega
      rw [LeanExe.Dialect.build_get (by rw [hcount, ite_eq_right hs0]; exact hk)]
      simp only [i0, i1]
      obtain ⟨hysz, hyg⟩ := transform_get (-1.0) xs hxs2
      obtain ⟨e0, e1⟩ := hyg k (by rw [hhalf]; exact hkN)
      have hMx : ∑ j ∈ Finset.range (xs.size / 2),
          (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) =
          ∑ j ∈ Finset.range s.size, |value s[j]!.toBits| := by
        rw [hhalf]
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨g0, g1⟩ := hxget j (Finset.mem_range.mp hj)
        rw [g0, g1, Library.Numerics.Reductions.Binary64.zero_bits,
          Library.Numerics.Reductions.Binary64.value_zero, abs_zero, add_zero]
      obtain ⟨h0, h1⟩ := transform_spec (-1.0) (-1) neg_one_approx (by norm_num) xs hxs2 hxf
        (by rw [hMx]; exact hD.2.trans (by norm_num)) k (by rw [hhalf]; exact hkN)
      rw [hMx, hhalf] at h0 h1
      rw [hhalf] at e0 e1
      rw [← e0] at h0
      rw [← e1] at h1
      have hA : ∑ j ∈ Finset.range s.size,
          (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / s.size) -
            value xs[2 * j + 1]!.toBits * (-1 * Real.sin (2 * Real.pi * j * k / s.size))) =
          ∑ j ∈ Finset.range s.size, value s[j]!.toBits * Real.cos (2 * Real.pi * j * k / s.size) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨g0, g1⟩ := hxget j (Finset.mem_range.mp hj)
        rw [g0, g1, Library.Numerics.Reductions.Binary64.zero_bits,
          Library.Numerics.Reductions.Binary64.value_zero]
        ring
      have hB : ∑ j ∈ Finset.range s.size,
          (value xs[2 * j]!.toBits * (-1 * Real.sin (2 * Real.pi * j * k / s.size)) +
            value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / s.size)) =
          -∑ j ∈ Finset.range s.size,
            value s[j]!.toBits * Real.sin (2 * Real.pi * j * k / s.size) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨g0, g1⟩ := hxget j (Finset.mem_range.mp hj)
        rw [g0, g1, Library.Numerics.Reductions.Binary64.zero_bits,
          Library.Numerics.Reductions.Binary64.value_zero]
        ring
      rw [hA] at h0
      rw [hB] at h1
      set M := ∑ j ∈ Finset.range s.size, |value s[j]!.toBits|
      have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hAM : |∑ j ∈ Finset.range s.size,
          value s[j]!.toBits * Real.cos (2 * Real.pi * j * k / s.size)| ≤ M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        nlinarith [Real.abs_cos_le_one (2 * Real.pi * j * k / s.size),
          abs_nonneg (value s[j]!.toBits),
          abs_nonneg (Real.cos (2 * Real.pi * j * k / s.size))]
      have hBM : |-∑ j ∈ Finset.range s.size,
          value s[j]!.toBits * Real.sin (2 * Real.pi * j * k / s.size)| ≤ M := by
        rw [abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        nlinarith [Real.abs_sin_le_one (2 * Real.pi * j * k / s.size),
          abs_nonneg (value s[j]!.toBits),
          abs_nonneg (Real.sin (2 * Real.pi * j * k / s.size))]
      have hγ1 : ((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) ≤ 1 := by
        have : ((s.size - 1 : ℕ) : ℝ) ≤ 2 ^ 52 := by
          exact_mod_cast (show s.size - 1 ≤ 2 ^ 52 by omega)
        rw [div_le_one (by linarith)]
        linarith
      have hγ0 : 0 ≤ ((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) :=
        div_nonneg (Nat.cast_nonneg _) (by
          have : ((s.size - 1 : ℕ) : ℝ) ≤ 2 ^ 52 := by
            exact_mod_cast (show s.size - 1 ≤ 2 ^ 52 by omega)
          linarith)
      have hE0 : 0 ≤ (((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) + 1 / 2 ^ 46) * M +
          (s.size : ℝ) / 2 ^ 1071 := by positivity
      have hE : (((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) + 1 / 2 ^ 46) * M +
          (s.size : ℝ) / 2 ^ 1071 ≤ 2 * M + 1 := by
        have h1 : (((s.size - 1 : ℕ) : ℝ) / (2 ^ 53 - (s.size - 1 : ℕ)) + 1 / 2 ^ 46) * M ≤
            2 * M := mul_le_mul_of_nonneg_right (by
              have : (1 : ℝ) / 2 ^ 46 ≤ 1 := by norm_num
              linarith) hM0
        have h2 : (s.size : ℝ) / 2 ^ 1071 ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (s.size : ℝ) ≤ 2 ^ 29 := by exact_mod_cast (show s.size ≤ 2 ^ 29 by omega)
          linarith [show (2 : ℝ) ^ 29 ≤ 2 ^ 1071 by norm_num]
        linarith
      have hsq := square_sum _ _ _ _ M _ h0 h1 hAM hBM hD.2 hE0 hE
      rw [neg_sq] at hsq
      exact ⟨hsq.1, hsq.2⟩

#print axioms powerSpectrum_master

end Library.Numerics.Fourier
