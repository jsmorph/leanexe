import Library.Numerics.Fourier.Twiddle
import LeanExe.Dialect.ArrayLemmas
import LeanExe.Dialect.Lemmas

/-!
The accuracy of `transformWith Trig.invPi Trig.halfPi dir xs` for `dir = ∓1`.  For a signal of
`n` complex values `x_j = a_j + i b_j`, interleaved in `xs`, the output holds `2 n` floats, and
the pair `(2 k, 2 k + 1)` is the left-to-right sum over `j` of the rounded terms
`a c - b d` and `a d + b c`, where `(c, d / dir)` is the twiddle of `j k mod n`.  `term_re` and
`term_im` bound the error of one term by `(|a| + |b|) / 2 ^ 47 + 2 ^ -1072`, from the twiddle's
error `2 ^ -48` and four roundings, and `sum_terms` bounds the error of the sum by
`(γ_(n-1) + 2 ^ -46) Σ (|a_j| + |b_j|) + n / 2 ^ 1071`.
-/

namespace Library.Numerics.Fourier

open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx LeanExe.Dialect
open Library.Numerics.Reductions.Binary64 Library.Numerics.Reductions.SumError

set_option exponentiation.threshold 4096

/-! ### One term -/

theorem neg_one_approx : FApprox (-1.0 : Float) (-1) 0 := by
  have h : (-1.0 : Float).toBits = 0xBFF0000000000000 := by decide +kernel
  have hv : value 0xBFF0000000000000 = -1 := by
    have : Wasm.IEEE64.scaledValue 0xBFF0000000000000 = -(2 ^ 1074) := by decide +kernel
    rw [value, this, Int.cast_neg, Int.cast_pow, Int.cast_ofNat, neg_div,
      div_self (by positivity)]
  refine ⟨by rw [h]; unfold CodeLib.IEEE64.Finite; decide, ?_⟩
  rw [h, hv]; simp

theorem one_approx : FApprox (1.0 : Float) 1 0 := by
  have h : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
  have hv : value 0x3FF0000000000000 = 1 := by
    have : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 := by decide +kernel
    rw [value, this, Int.cast_pow, Int.cast_ofNat, div_self (by positivity)]
  refine ⟨by rw [h]; unfold CodeLib.IEEE64.Finite; decide, ?_⟩
  rw [h, hv]; simp

/-- The real part of one term: `a c - b (dir s)` within `(|a| + |b|) / 2 ^ 47 + 2 ^ -1072` of
`a C - b σ S`. -/
theorem term_re (a b c s dir : Float) (σ C S : ℝ) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (1 / 2 ^ 48)) (hs : FApprox s S (1 / 2 ^ 48)) (hdir : FApprox dir σ 0)
    (hσ : |σ| = 1) (hC : |C| ≤ 1) (hS : |S| ≤ 1)
    (hab : |value a.toBits| + |value b.toBits| ≤ 2 ^ 1000) :
    FApprox (a * c - b * (dir * s)) (value a.toBits * C - value b.toBits * (σ * S))
      ((|value a.toBits| + |value b.toBits|) / 2 ^ 47 + 1 / 2 ^ 1072) := by
  set A := |value a.toBits|
  set B := |value b.toBits|
  have hA : 0 ≤ A := abs_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  have hσS : |σ * S| ≤ 1 := by rw [abs_mul, hσ, one_mul]; exact hS
  have hd := fapprox_mul hdir hs 1 1 (le_of_eq hσ) hS 2 (by norm_num) (by norm_num)
  have hd' : FApprox (dir * s) (σ * S) (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    hd.mono (le_of_eq (by ring))
  have hp1 := fapprox_mul (approx_self _ ha) hc A 1 le_rfl hC (2 * A)
    (by nlinarith [show (1 : ℝ) / 2 ^ 48 ≤ 1 by norm_num]) (by
      have : (2 : ℝ) * 2 ^ 1000 < 2 ^ 1022 := by norm_num
      linarith)
  have hp2 := fapprox_mul (approx_self _ hb) hd' B 1 le_rfl hσS (2 * B)
    (by nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 by norm_num]) (by
      have : (2 : ℝ) * 2 ^ 1000 < 2 ^ 1022 := by norm_num
      linarith)
  set e1 := 0 * 1 + A * (1 / 2 ^ 48) + 0 * (1 / 2 ^ 48) + 2 * A / 2 ^ 53 + 1 / 2 ^ 1075
  set e2 := 0 * 1 + B * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) +
    0 * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) + 2 * B / 2 ^ 53 + 1 / 2 ^ 1075
  have he12 : e1 + e2 ≤ A + B + 2 / 2 ^ 1075 := by
    simp only [e1, e2]
    have : A * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ A := by
      nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 by norm_num]
    have : B * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ B / 2 := by
      nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 by norm_num]
    nlinarith
  have hv : |value a.toBits * C - value b.toBits * (σ * S)| ≤ A + B := by
    calc _ ≤ |value a.toBits * C| + |value b.toBits * (σ * S)| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ A * 1 + B * 1 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hC hA)
            (mul_le_mul_of_nonneg_left hσS hB)
      _ = A + B := by ring
  have hsub := fapprox_sub hp1 hp2 (2 * (A + B) + 2 / 2 ^ 1075) (by linarith) (by
    have : (2 : ℝ) * (2 ^ 1000) + 2 / 2 ^ 1075 < 2 ^ 1023 := by norm_num
    linarith)
  refine hsub.mono ?_
  simp only [e1, e2]
  have hb1 : B * (1 / 2 ^ 1075 : ℝ) ≤ B / 2 ^ 53 := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_left hB (by positivity) (by norm_num)
  have : (A + B) * (1 / 2 ^ 48 + 5 / 2 ^ 53) ≤ (A + B) / 2 ^ 47 := by
    rw [div_eq_mul_one_div (A + B)]
    exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
  have hc : (2 : ℝ) / 2 ^ 1075 + 2 / 2 ^ 1075 / 2 ^ 53 ≤ 1 / 2 ^ 1072 := by norm_num
  linarith

/-- The imaginary part of one term: `a (dir s) + b c` within `(|a| + |b|) / 2 ^ 47 + 2 ^ -1072`
of `a σ S + b C`. -/
theorem term_im (a b c s dir : Float) (σ C S : ℝ) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (hc : FApprox c C (1 / 2 ^ 48)) (hs : FApprox s S (1 / 2 ^ 48)) (hdir : FApprox dir σ 0)
    (hσ : |σ| = 1) (hC : |C| ≤ 1) (hS : |S| ≤ 1)
    (hab : |value a.toBits| + |value b.toBits| ≤ 2 ^ 1000) :
    FApprox (a * (dir * s) + b * c) (value a.toBits * (σ * S) + value b.toBits * C)
      ((|value a.toBits| + |value b.toBits|) / 2 ^ 47 + 1 / 2 ^ 1072) := by
  set A := |value a.toBits|
  set B := |value b.toBits|
  have hA : 0 ≤ A := abs_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  have hσS : |σ * S| ≤ 1 := by rw [abs_mul, hσ, one_mul]; exact hS
  have hd := fapprox_mul hdir hs 1 1 (le_of_eq hσ) hS 2 (by norm_num) (by norm_num)
  have hd' : FApprox (dir * s) (σ * S) (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) :=
    hd.mono (le_of_eq (by ring))
  have hp1 := fapprox_mul (approx_self _ ha) hd' A 1 le_rfl hσS (2 * A)
    (by nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 by norm_num]) (by
      have : (2 : ℝ) * 2 ^ 1000 < 2 ^ 1022 := by norm_num
      linarith)
  have hp2 := fapprox_mul (approx_self _ hb) hc B 1 le_rfl hC (2 * B)
    (by nlinarith [show (1 : ℝ) / 2 ^ 48 ≤ 1 by norm_num]) (by
      have : (2 : ℝ) * 2 ^ 1000 < 2 ^ 1022 := by norm_num
      linarith)
  set e1 := 0 * 1 + A * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) +
    0 * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) + 2 * A / 2 ^ 53 + 1 / 2 ^ 1075
  set e2 := 0 * 1 + B * (1 / 2 ^ 48) + 0 * (1 / 2 ^ 48) + 2 * B / 2 ^ 53 + 1 / 2 ^ 1075
  have he12 : e1 + e2 ≤ A + B + 2 / 2 ^ 1075 := by
    simp only [e1, e2]
    have : A * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ A / 2 := by
      nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 by norm_num]
    have : B * (1 / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ B := by
      nlinarith [show (1 : ℝ) / 2 ^ 48 + 2 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 by norm_num]
    nlinarith
  have hv : |value a.toBits * (σ * S) + value b.toBits * C| ≤ A + B := by
    calc _ ≤ |value a.toBits * (σ * S)| + |value b.toBits * C| := abs_add_le _ _
      _ ≤ A * 1 + B * 1 := by
          rw [abs_mul (value a.toBits) (σ * S), abs_mul (value b.toBits) C]
          exact add_le_add (mul_le_mul_of_nonneg_left hσS hA)
            (mul_le_mul_of_nonneg_left hC hB)
      _ = A + B := by ring
  have hadd := fapprox_add hp1 hp2 (2 * (A + B) + 2 / 2 ^ 1075) (by linarith) (by
    have : (2 : ℝ) * (2 ^ 1000) + 2 / 2 ^ 1075 < 2 ^ 1023 := by norm_num
    linarith)
  refine hadd.mono ?_
  simp only [e1, e2]
  have ha1 : A * (1 / 2 ^ 1075 : ℝ) ≤ A / 2 ^ 53 := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_left hA (by positivity) (by norm_num)
  have : (A + B) * (1 / 2 ^ 48 + 5 / 2 ^ 53) ≤ (A + B) / 2 ^ 47 := by
    rw [div_eq_mul_one_div (A + B)]
    exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
  have hc : (2 : ℝ) / 2 ^ 1075 + 2 / 2 ^ 1075 / 2 ^ 53 ≤ 1 / 2 ^ 1072 := by norm_num
  linarith

/-! ### The sum of the terms -/

/-- A left-to-right sum of `n < 2 ^ 52` words, the word `j` within `m_j / 2 ^ 47 + 2 ^ -1072` of
`v_j` with `|v_j| ≤ m_j` and `Σ m_j ≤ 2 ^ 1000`, lies within
`(γ_(n-1) + 2 ^ -46) Σ m_j + n / 2 ^ 1071` of `Σ v_j`. -/
theorem sum_terms (n : ℕ) (t : ℕ → Float) (v m : ℕ → ℝ) (hn : n < 2 ^ 52)
    (ht : ∀ j < n, FApprox (t j) (v j) (m j / 2 ^ 47 + 1 / 2 ^ 1072))
    (hvm : ∀ j < n, |v j| ≤ m j) (hM : ∑ j ∈ Finset.range n, m j ≤ 2 ^ 1000) :
    FApprox ((List.range n).foldl (fun acc j => acc + t j) 0.0) (∑ j ∈ Finset.range n, v j)
      ((((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) + 1 / 2 ^ 46) *
        ∑ j ∈ Finset.range n, m j + n / 2 ^ 1071) := by
  have hm0 : ∀ j < n, 0 ≤ m j := fun j hj => (abs_nonneg _).trans (hvm j hj)
  have hA' : ((List.range n).map fun j => |v j| + (m j / 2 ^ 47 + 1 / 2 ^ 1072)).sum =
      (∑ j ∈ Finset.range n, |v j|) + ((∑ j ∈ Finset.range n, m j) / 2 ^ 47 + n / 2 ^ 1072) := by
    rw [range_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hV' : ((List.range n).map fun j => |v j|).sum = ∑ j ∈ Finset.range n, |v j| :=
    range_sum _ _
  have hVM : ∑ j ∈ Finset.range n, |v j| ≤ ∑ j ∈ Finset.range n, m j :=
    Finset.sum_le_sum fun j hj => hvm j (Finset.mem_range.mp hj)
  have hV0 : 0 ≤ ∑ j ∈ Finset.range n, |v j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM0 : 0 ≤ ∑ j ∈ Finset.range n, m j :=
    Finset.sum_nonneg fun j hj => hm0 j (Finset.mem_range.mp hj)
  set M := ∑ j ∈ Finset.range n, m j
  set V := ∑ j ∈ Finset.range n, |v j|
  have hnr : (n : ℝ) ≤ 2 ^ 52 := by exact_mod_cast hn.le
  have hk : 2 * ((n - 1 : ℕ) : ℝ) < 2 ^ 53 := by
    have : ((n - 1 : ℕ) : ℝ) < 2 ^ 52 := by exact_mod_cast (Nat.sub_le _ _).trans_lt hn
    linarith
  have h2 := pow_le_two 53 (n - 1) hk
  have hg := gamma_pow 53 (n - 1) (by linarith [Nat.cast_nonneg (α := ℝ) (n - 1)])
  have hAb : V + (M / 2 ^ 47 + n / 2 ^ 1072) ≤ 2 ^ 1001 := by
    have : M / 2 ^ 47 ≤ 2 ^ 1000 / 2 ^ 47 := div_le_div_of_nonneg_right hM (by positivity)
    have : (n : ℝ) / 2 ^ 1072 ≤ 2 ^ 52 / 2 ^ 1072 := div_le_div_of_nonneg_right hnr (by positivity)
    have : (2 : ℝ) ^ 1000 + (2 ^ 1000 / 2 ^ 47 + 2 ^ 52 / 2 ^ 1072) ≤ 2 ^ 1001 := by norm_num
    linarith
  have h := sum_approx f64 (List.range n) t v (fun j => m j / 2 ^ 47 + 1 / 2 ^ 1072)
    (fun j hj => ht j (List.mem_range.mp hj)) (by
      rw [hA']; exact hAb.trans (show (2 : ℝ) ^ 1001 ≤ 2 ^ 1022 by norm_num)) (by
      rw [hA', f64_u, List.length_range]
      show _ < (2 : ℝ) ^ 1023
      have hp : 0 ≤ (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) := by positivity
      calc (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) * (V + (M / 2 ^ 47 + n / 2 ^ 1072)) ≤
            (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) * 2 ^ 1001 := mul_le_mul_of_nonneg_left hAb hp
        _ < 2 * 2 ^ 1001 := by gcongr
        _ ≤ 2 ^ 1023 := by norm_num)
  beta_reduce at h
  rw [hA', hV', f64_u, List.length_range, range_sum] at h
  refine h.mono ?_
  have hd0 : 0 ≤ M / 2 ^ 47 + n / 2 ^ 1072 := by positivity
  have hγ0 : 0 ≤ ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (n - 1)])
  have e1 : ((1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) - 1) * V ≤
      ((n - 1 : ℕ) : ℝ) / (2 ^ 53 - (n - 1 : ℕ)) * M :=
    (mul_le_mul_of_nonneg_right hg hV0).trans (mul_le_mul_of_nonneg_left hVM hγ0)
  have e2 : (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) * (M / 2 ^ 47 + n / 2 ^ 1072) ≤
      2 * (M / 2 ^ 47 + n / 2 ^ 1072) := mul_le_mul_of_nonneg_right h2.le hd0
  have e3 : (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) * (V + (M / 2 ^ 47 + n / 2 ^ 1072)) - V =
      ((1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) - 1) * V +
        (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1) * (M / 2 ^ 47 + n / 2 ^ 1072) := by ring
  have e4 : (2 : ℝ) * (M / 2 ^ 47 + n / 2 ^ 1072) = 1 / 2 ^ 46 * M + n / 2 ^ 1071 := by ring
  rw [e3]
  linarith

/-! ### The structure of the transform -/

theorem pair_foldl (l : List ℕ) (f g : ℕ → Float) (a0 b0 : Float) :
    l.foldl (fun acc j => (acc.1 + f j, acc.2 + g j)) (a0, b0) =
      (l.foldl (fun a j => a + f j) a0, l.foldl (fun b j => b + g j) b0) := by
  induction l generalizing a0 b0 with
  | nil => rfl
  | cons j l ih => simp only [List.foldl_cons]; exact ih _ _

/-- The inner loop of `transformWith Trig.invPi Trig.halfPi dir xs` for the output pair `k`. -/
def innerLoop (dir : Float) (xs : Array Float) (k : UInt64) : Float × Float :=
  LeanExe.loop (xs.size.toUInt64 / 2) ((0.0 : Float), (0.0 : Float)) fun j acc =>
    let t := (LeanExe.build (xs.size.toUInt64 / 2) fun m =>
      twiddle (xs.size.toUInt64 / 2) m)[(j * k % (xs.size.toUInt64 / 2)).toNat]!
    let c := t.1
    let d := dir * t.2
    let a := xs[(2 * j).toNat]!
    let b := xs[(2 * j + 1).toNat]!
    (acc.1 + (a * c - b * d), acc.2 + (a * d + b * c))

theorem transform_loop (dir : Float) (xs : Array Float) :
    transformWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi dir xs =
      LeanExe.loop (xs.size.toUInt64 / 2) (LeanExe.build (2 * (xs.size.toUInt64 / 2)) fun _ => 0.0)
        fun k out => (out.set! (2 * k).toNat (innerLoop dir xs k).1).set! (2 * k + 1).toNat
          (innerLoop dir xs k).2 := rfl

/-- The twiddle of `r` for a signal of `xs.size / 2` values. -/
def tw (xs : Array Float) (r : ℕ) : Float × Float :=
  twiddle (xs.size.toUInt64 / 2) (UInt64.ofNat r)

/-- The real part of term `j` of output `k`. -/
def termRe (dir : Float) (xs : Array Float) (k j : ℕ) : Float :=
  xs[2 * j]! * (tw xs (j * k % (xs.size / 2))).1 -
    xs[2 * j + 1]! * (dir * (tw xs (j * k % (xs.size / 2))).2)

/-- The imaginary part of term `j` of output `k`. -/
def termIm (dir : Float) (xs : Array Float) (k j : ℕ) : Float :=
  xs[2 * j]! * (dir * (tw xs (j * k % (xs.size / 2))).2) +
    xs[2 * j + 1]! * (tw xs (j * k % (xs.size / 2))).1

theorem half_toNat (xs : Array Float) (h : xs.size < 2 ^ 64) :
    (xs.size.toUInt64 / 2).toNat = xs.size / 2 := by
  rw [UInt64.toNat_div, size_toUInt64 xs h]
  rfl

theorem innerLoop_eq (dir : Float) (xs : Array Float) (h : xs.size < 2 ^ 30) (k : ℕ)
    (hk : k < xs.size / 2) :
    innerLoop dir xs (UInt64.ofNat k) =
      ((List.range (xs.size / 2)).foldl (fun a j => a + termRe dir xs k j) 0.0,
        (List.range (xs.size / 2)).foldl (fun b j => b + termIm dir xs k j) 0.0) := by
  have hN := half_toNat xs (by omega)
  unfold innerLoop
  rw [loop_eq_foldl, hN, ← pair_foldl]
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  have hj' : j < xs.size / 2 := List.mem_range.mp hj
  have h64 : ∀ c, c < 2 ^ 30 → (UInt64.ofNat c).toNat = c := fun c hc =>
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hjk : j * k < 2 ^ 58 := by
    have : j * k < 2 ^ 29 * 2 ^ 29 := Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  have hi1 : (UInt64.ofNat j * UInt64.ofNat k % (xs.size.toUInt64 / 2)).toNat =
      j * k % (xs.size / 2) := by
    rw [UInt64.toNat_mod, UInt64.toNat_mul, hN, h64 j (by omega), h64 k (by omega),
      Nat.mod_eq_of_lt (show j * k < 2 ^ 64 by omega)]
  have hi2 : (2 * UInt64.ofNat j).toNat = 2 * j := by
    rw [UInt64.toNat_mul, h64 j (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have hi3 : (2 * UInt64.ofNat j + 1).toNat = 2 * j + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, h64 j (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have hw : (LeanExe.build (xs.size.toUInt64 / 2) fun m =>
      twiddle (xs.size.toUInt64 / 2) m)[j * k % (xs.size / 2)]! = tw xs (j * k % (xs.size / 2)) :=
    build_get (by rw [hN]; exact Nat.mod_lt _ (by omega))
  simp only [hi1, hi2, hi3, hw, termRe, termIm]

theorem transform_get (dir : Float) (xs : Array Float) (h : xs.size < 2 ^ 30) :
    (transformWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi dir
      xs).size = 2 * (xs.size / 2) ∧
    ∀ k < xs.size / 2,
      (transformWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi dir
        xs)[2 * k]! = (List.range (xs.size / 2)).foldl (fun a j => a + termRe dir xs k j) 0.0 ∧
      (transformWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi dir
        xs)[2 * k + 1]! = (List.range (xs.size / 2)).foldl (fun b j => b + termIm dir xs k j) 0.0 := by
  have hN := half_toNat xs (by omega)
  set n := xs.size / 2 with hn
  have h64 : ∀ c, c < 2 ^ 30 → (UInt64.ofNat c).toNat = c := fun c hc =>
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have h2N : (2 * (xs.size.toUInt64 / 2)).toNat = 2 * n := by
    rw [UInt64.toNat_mul, hN]
    simp only [UInt64.reduceToNat]
    omega
  rw [transform_loop, loop_eq_foldl, hN]
  set body := fun (out : Array Float) (i : ℕ) =>
    (out.set! (2 * UInt64.ofNat i).toNat (innerLoop dir xs (UInt64.ofNat i)).1).set!
      (2 * UInt64.ofNat i + 1).toNat (innerLoop dir xs (UInt64.ofNat i)).2 with hbody
  suffices hK : ∀ K ≤ n, ((List.range K).foldl body
      (LeanExe.build (2 * (xs.size.toUInt64 / 2)) fun _ => 0.0)).size = 2 * n ∧
      ∀ i < 2 * n, ((List.range K).foldl body
        (LeanExe.build (2 * (xs.size.toUInt64 / 2)) fun _ => 0.0))[i]! =
        if i / 2 < K then
          (if i % 2 = 0 then (innerLoop dir xs (UInt64.ofNat (i / 2))).1
            else (innerLoop dir xs (UInt64.ofNat (i / 2))).2)
        else 0.0 by
    obtain ⟨hs, hg⟩ := hK n le_rfl
    refine ⟨hs, fun k hk => ?_⟩
    have e0 := hg (2 * k) (by omega)
    have e1 := hg (2 * k + 1) (by omega)
    rw [ite_eq_left (show 2 * k / 2 < n by omega), ite_eq_left (show 2 * k % 2 = 0 by omega),
      show 2 * k / 2 = k by omega] at e0
    rw [ite_eq_left (show (2 * k + 1) / 2 < n by omega), ite_eq_right (show ¬ (2 * k + 1) % 2 = 0 by omega),
      show (2 * k + 1) / 2 = k by omega] at e1
    rw [e0, e1, innerLoop_eq dir xs h k hk]
    exact ⟨rfl, rfl⟩
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨by rw [List.range_zero, List.foldl_nil, build_size, h2N], fun i hi => ?_⟩
    rw [List.range_zero, List.foldl_nil, build_get (by rw [h2N]; exact hi)]
    simp
  | succ K ih =>
    intro hK
    obtain ⟨hs, hg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range K).foldl body (LeanExe.build (2 * (xs.size.toUInt64 / 2)) fun _ => 0.0)
    have hK2 : (2 * UInt64.ofNat K).toNat = 2 * K := by
      rw [UInt64.toNat_mul, h64 K (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hK3 : (2 * UInt64.ofNat K + 1).toNat = 2 * K + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, h64 K (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hbK : body acc K = (acc.set! (2 * K) (innerLoop dir xs (UInt64.ofNat K)).1).set!
        (2 * K + 1) (innerLoop dir xs (UInt64.ofNat K)).2 := by
      rw [hbody]; simp only [hK2, hK3]
    rw [hbK]
    have hs1 : (acc.set! (2 * K) (innerLoop dir xs (UInt64.ofNat K)).1).size = 2 * n := by
      simp [hs]
    refine ⟨by simp [hs], fun i hi => ?_⟩
    rw [get_set _ _ _ _ (by rw [hs1]; omega), get_set _ _ _ _ (by rw [hs]; omega)]
    by_cases h1 : i = 2 * K + 1
    · rw [ite_eq_left h1, ite_eq_left (show i / 2 < K + 1 by omega), ite_eq_right (show ¬ i % 2 = 0 by omega),
        show i / 2 = K by omega]
    · rw [ite_eq_right h1]
      by_cases h0 : i = 2 * K
      · rw [ite_eq_left h0, ite_eq_left (show i / 2 < K + 1 by omega), ite_eq_left (show i % 2 = 0 by omega),
          show i / 2 = K by omega]
      · rw [ite_eq_right h0, hg i hi]
        by_cases hl : i / 2 < K
        · rw [ite_eq_left hl, ite_eq_left (show i / 2 < K + 1 by omega)]
        · rw [ite_eq_right hl, ite_eq_right (show ¬ i / 2 < K + 1 by omega)]

/-! ### Accuracy of the transform -/

theorem angle_mod (n j k : ℕ) (hn : 0 < n) :
    2 * Real.pi * j * k / n =
      2 * Real.pi * ((j * k % n : ℕ) : ℝ) / n + ((j * k / n : ℕ) : ℝ) * (2 * Real.pi) := by
  have hjk : (j : ℝ) * k = n * ((j * k / n : ℕ) : ℝ) + ((j * k % n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (j * k) n).symm
  have hnr : (n : ℝ) ≠ 0 := by positivity
  calc 2 * Real.pi * j * k / n = 2 * Real.pi * ((j : ℝ) * k) / n := by ring
    _ = 2 * Real.pi * (n * ((j * k / n : ℕ) : ℝ) + ((j * k % n : ℕ) : ℝ)) / n := by rw [hjk]
    _ = _ := by field_simp; ring

theorem cos_mod (n j k : ℕ) (hn : 0 < n) :
    Real.cos (2 * Real.pi * ((j * k % n : ℕ) : ℝ) / n) = Real.cos (2 * Real.pi * j * k / n) := by
  rw [angle_mod n j k hn, Real.cos_add_nat_mul_two_pi]

theorem sin_mod (n j k : ℕ) (hn : 0 < n) :
    Real.sin (2 * Real.pi * ((j * k % n : ℕ) : ℝ) / n) = Real.sin (2 * Real.pi * j * k / n) := by
  rw [angle_mod n j k hn, Real.sin_add_nat_mul_two_pi]

/-- The twiddle of `j k mod n` approximates `cos` and `sin` of `2 π j k / n`. -/
theorem tw_approx (xs : Array Float) (h : xs.size < 2 ^ 30) (j k : ℕ) (hn : 0 < xs.size / 2) :
    FApprox (tw xs (j * k % (xs.size / 2))).1
        (Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) (1 / 2 ^ 48) ∧
      FApprox (tw xs (j * k % (xs.size / 2))).2
        (Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) (1 / 2 ^ 48) := by
  have hN := half_toNat xs (by omega)
  have hr : j * k % (xs.size / 2) < xs.size / 2 := Nat.mod_lt _ hn
  have hr64 : (UInt64.ofNat (j * k % (xs.size / 2))).toNat = j * k % (xs.size / 2) :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have ht := twiddle_spec (xs.size.toUInt64 / 2) (UInt64.ofNat (j * k % (xs.size / 2)))
    (by rw [hN]; exact hn) (by rw [hN, hr64]; exact hr) (by rw [hN]; omega)
  rw [hr64, hN, cos_mod _ _ _ hn, sin_mod _ _ _ hn] at ht
  exact ⟨⟨ht.1, ht.2.2.1⟩, ⟨ht.2.1, ht.2.2.2⟩⟩

/-- Each output pair of the transform with the sign `σ = value dir`, `|σ| = 1`, lies within
`(γ_(n-1) + 2 ^ -46) Σ (|a_j| + |b_j|) + n / 2 ^ 1071` of
`Σ_j (a_j cos θ_jk - σ b_j sin θ_jk)` and `Σ_j (σ a_j sin θ_jk + b_j cos θ_jk)`,
`θ_jk = 2 π j k / n`. -/
theorem transform_spec (dir : Float) (σ : ℝ) (hdir : FApprox dir σ 0) (hσ : |σ| = 1)
    (xs : Array Float) (h : xs.size < 2 ^ 30) (hf : ∀ v ∈ xs, Finite v.toBits)
    (hM : ∑ j ∈ Finset.range (xs.size / 2),
      (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) ≤ 2 ^ 1000)
    (k : ℕ) (hk : k < xs.size / 2) :
    FApprox ((List.range (xs.size / 2)).foldl (fun a j => a + termRe dir xs k j) 0.0)
        (∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ)) -
            value xs[2 * j + 1]!.toBits *
              (σ * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))))
        ((((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 46) *
          ∑ j ∈ Finset.range (xs.size / 2),
            (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) +
          (xs.size / 2 : ℕ) / 2 ^ 1071) ∧
    FApprox ((List.range (xs.size / 2)).foldl (fun b j => b + termIm dir xs k j) 0.0)
        (∑ j ∈ Finset.range (xs.size / 2),
          (value xs[2 * j]!.toBits * (σ * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))) +
            value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))))
        ((((xs.size / 2 - 1 : ℕ) : ℝ) / (2 ^ 53 - (xs.size / 2 - 1 : ℕ)) + 1 / 2 ^ 46) *
          ∑ j ∈ Finset.range (xs.size / 2),
            (|value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|) +
          (xs.size / 2 : ℕ) / 2 ^ 1071) := by
  have hn : 0 < xs.size / 2 := by omega
  have hab : ∀ j < xs.size / 2,
      |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits| ≤ 2 ^ 1000 := fun j hj =>
    (Finset.single_le_sum (f := fun j => |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr hj)).trans hM
  have hC : ∀ j, |Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))| ≤ 1 := fun _ =>
    Real.abs_cos_le_one _
  have hS : ∀ j, |Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))| ≤ 1 := fun _ =>
    Real.abs_sin_le_one _
  have hσS : ∀ j, |σ * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ))| ≤ 1 := fun j => by
    rw [abs_mul, hσ, one_mul]; exact hS j
  have hn52 : xs.size / 2 < 2 ^ 52 := by omega
  constructor
  · refine sum_terms _ _ _ (fun j => |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)
      hn52 (fun j hj => ?_) (fun j hj => ?_) hM
    · obtain ⟨hc, hs⟩ := tw_approx xs h j k hn
      exact term_re _ _ _ _ dir σ _ _ (finite_get xs hf _) (finite_get xs hf _) hc hs hdir hσ
        (hC j) (hS j) (hab j hj)
    · calc _ ≤ |value xs[2 * j]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))| +
            |value xs[2 * j + 1]!.toBits *
              (σ * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))| := by
            rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ ≤ |value xs[2 * j]!.toBits| * 1 + |value xs[2 * j + 1]!.toBits| * 1 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left (hC j) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hσS j) (abs_nonneg _))
        _ = _ := by ring
  · refine sum_terms _ _ _ (fun j => |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits|)
      hn52 (fun j hj => ?_) (fun j hj => ?_) hM
    · obtain ⟨hc, hs⟩ := tw_approx xs h j k hn
      exact term_im _ _ _ _ dir σ _ _ (finite_get xs hf _) (finite_get xs hf _) hc hs hdir hσ
        (hC j) (hS j) (hab j hj)
    · calc _ ≤ |value xs[2 * j]!.toBits *
              (σ * Real.sin (2 * Real.pi * j * k / (xs.size / 2 : ℕ)))| +
            |value xs[2 * j + 1]!.toBits * Real.cos (2 * Real.pi * j * k / (xs.size / 2 : ℕ))| :=
            abs_add_le _ _
        _ ≤ |value xs[2 * j]!.toBits| * 1 + |value xs[2 * j + 1]!.toBits| * 1 := by
            rw [abs_mul (value xs[2 * j]!.toBits), abs_mul (value xs[2 * j + 1]!.toBits)]
            exact add_le_add (mul_le_mul_of_nonneg_left (hσS j) (abs_nonneg _))
              (mul_le_mul_of_nonneg_left (hC j) (abs_nonneg _))
        _ = _ := by ring

/-- A loop that replaces each element of `ys` by `f` of it. -/
theorem map_loop (ys : Array Float) (f : Float → Float) (h : ys.size < 2 ^ 64) :
    (LeanExe.loop ys.size.toUInt64 ys fun i acc => acc.set! i.toNat (f acc[i.toNat]!)).size =
      ys.size ∧
    ∀ j < ys.size,
      (LeanExe.loop ys.size.toUInt64 ys fun i acc => acc.set! i.toNat (f acc[i.toNat]!))[j]! =
        f ys[j]! := by
  have h1 : (LeanExe.loop ys.size.toUInt64 ys fun i acc => acc.set! i.toNat (f acc[i.toNat]!)) =
      (List.range ys.size.toUInt64.toNat).foldl (fun acc i => acc.set! i (f acc[i]!)) ys :=
    loop_toNat _ _ (fun (j : ℕ) (acc : Array Float) => acc.set! j (f acc[j]!))
  rw [h1, size_toUInt64 ys h]
  suffices hk : ∀ k ≤ ys.size,
      ((List.range k).foldl (fun acc i => acc.set! i (f acc[i]!)) ys).size = ys.size ∧
      ∀ j < ys.size, ((List.range k).foldl (fun acc i => acc.set! i (f acc[i]!)) ys)[j]! =
        if j < k then f ys[j]! else ys[j]! by
    obtain ⟨hs, hg⟩ := hk ys.size le_rfl
    exact ⟨hs, fun j hj => by rw [hg j hj, ite_eq_left hj]⟩
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hs, hg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range k).foldl (fun acc i => acc.set! i (f acc[i]!)) ys
    have hk' : k < acc.size := by rw [hs]; omega
    refine ⟨by simp [hs], fun j hj => ?_⟩
    rw [get_set acc k _ j hk', hg k (by omega), ite_eq_right (lt_irrefl k)]
    by_cases hjk : j = k
    · rw [ite_eq_left hjk, ite_eq_left (show j < k + 1 by omega), hjk]
    · rw [ite_eq_right hjk, hg j hj]
      by_cases hjl : j < k
      · rw [ite_eq_left hjl, ite_eq_left (show j < k + 1 by omega)]
      · rw [ite_eq_right hjl, ite_eq_right (show ¬ j < k + 1 by omega)]

end Library.Numerics.Fourier
