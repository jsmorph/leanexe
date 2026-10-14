import Verified.Examples.BesselOrderEnergy
import LeanExe.ProofKit.F64Approx

/-!
The forward recurrence 10.6.1 in floating point for `2 n ≤ x` and `4 ≤ x ≤ 2^302`.  A sequence of
floats `f_k` that starts within `10 u M₀` and `12 u M₁` of a solution `F` of the recurrence, and
whose steps each add a local error `δ_k` of at most `u (3.01 λ_(k+1) |f_(k+1)| + |f_k|)` plus
`2^-1070`, stays within `(17 + 12 m) u M_m` of `F_m` for `m ≤ n` (`forward`).  The error of `f_m`
is `BesselRecur.resp`, the kernel is at most `(π x/2) M_k M_m` (`BesselRecur.kern_le`), and
`BesselOrderEnergy.modn_bound` bounds `(π x/2) M_k²` by `2.6 x/(x - k)`.  The starting errors
contribute `22 · 1.3 u M_m`; step `k` contributes at most `2.6 (1 + 2^-18) (1 + 14.04 (k + 1)/x)`
units (`term_bound`), whose sum over `k < m - 1` is at most `11.73 (m - 1)` units for `2 m ≤ x`.
-/

namespace Verified.Examples.BesselForward
open Real Finset CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselOrderN BesselRecur
  BesselOrderEnergy

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

set_option maxHeartbeats 1000000 in
/-- The contribution of one step. -/
theorem term_bound {x j Mj Mj1 Mm a b d : ℝ} (hx : 4 ≤ x) (hxb : x ≤ 2 ^ 302) (hj1 : 1 ≤ j)
    (hj : 2 * j ≤ x) (hMj : 0 ≤ Mj) (hMj1 : 0 ≤ Mj1) (hMm : 0 ≤ Mm) (hMj' : Mj ≤ 1)
    (hcj : π * x / 2 * Mj ^ 2 * (x - j) ≤ 13 / 5 * x)
    (hcj1 : π * x / 2 * Mj1 ^ 2 * (x - (j - 1)) ≤ 13 / 5 * x)
    (ha : |a| ≤ (1 + 1 / 2 ^ 18) * Mj) (hb : |b| ≤ (1 + 1 / 2 ^ 18) * Mj1)
    (hd : |d| ≤ 𝐮 * (301 / 100 * (2 * j / x) * |a| + |b|) + 1 / 2 ^ 1070) :
    |d| * (π * x / 2 * (Mj * Mm)) ≤
      𝐮 * Mm * (13 / 5 * (1 + 1 / 2 ^ 18) * (1 + 1404 / 100 * (j / x)) + 1 / 2 ^ 700) := by
  have hx0 : 0 < x := by linarith
  have hpi : 3 < π := pi_gt_three
  have hpi4 : π ≤ 4 := pi_le_four
  set P := π * x / 2 with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  have hP2 : P ≤ 2 ^ 303 := by
    rw [hPdef]
    have : π * x ≤ 4 * 2 ^ 302 := by nlinarith
    linarith [show (4 : ℝ) * 2 ^ 302 / 2 = 2 ^ 303 by norm_num]
  set t := j / x with htdef
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hx0.le
  have ht : t ≤ 1 / 2 := by rw [htdef, div_le_iff₀ hx0]; linarith
  have hx' : x ≠ 0 := hx0.ne'
  have hjt : j = t * x := by rw [htdef]; field_simp
  have hxj : 0 < x - j := by linarith
  -- the two squares, times `x - j`
  have hs1 : P * Mj ^ 2 * (x - j) ≤ 13 / 5 * x := hcj
  have hs2 : P * Mj1 ^ 2 * (x - j) ≤ 13 / 5 * x := by
    have : P * Mj1 ^ 2 * (x - j) ≤ P * Mj1 ^ 2 * (x - (j - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hP.le (sq_nonneg _))
    linarith
  set S := 602 / 100 * t * (P * Mj ^ 2) + P * (Mj1 * Mj) with hSdef
  have hSA : S * (x - j) ≤ 15652 / 1000 * j + 13 / 5 * x := by
    have h1 : 602 / 100 * t * (P * Mj ^ 2) * (x - j) ≤ 602 / 100 * t * (13 / 5 * x) := by
      have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 602 / 100) ht0)
      linarith
    have h2 : P * (Mj1 * Mj) * (x - j) ≤ 13 / 5 * x := by
      have hq : 2 * (Mj1 * Mj) ≤ Mj1 ^ 2 + Mj ^ 2 := by nlinarith [sq_nonneg (Mj1 - Mj)]
      have := mul_le_mul_of_nonneg_left hq (mul_nonneg hP.le hxj.le)
      nlinarith
    have e : 602 / 100 * t * (13 / 5 * x) = 15652 / 1000 * j := by rw [hjt]; ring
    rw [hSdef]
    nlinarith
  have hSB : S ≤ 13 / 5 * (1 + 1404 / 100 * t) := by
    have hx1 : x - j = (1 - t) * x := by rw [hjt]; ring
    rw [hx1] at hSA
    have hA : S * (1 - t) ≤ 15652 / 1000 * t + 13 / 5 := by
      rw [hjt] at hSA
      have : S * (1 - t) * x ≤ (15652 / 1000 * t + 13 / 5) * x := by linarith
      exact le_of_mul_le_mul_right this hx0
    have hB : 15652 / 1000 * t + 13 / 5 ≤ 13 / 5 * (1 + 1404 / 100 * t) * (1 - t) := by nlinarith
    have hpos : 0 < 1 - t := by linarith
    exact le_of_mul_le_mul_right (by linarith) hpos
  -- the step's error, times `P Mj`
  have hd1 : |d| * (P * Mj) ≤ 𝐮 * (1 + 1 / 2 ^ 18) * S + 1 / 2 ^ 1070 * (P * Mj) := by
    have hu : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
    have hlam : 301 / 100 * (2 * j / x) = 602 / 100 * t := by rw [htdef]; ring
    rw [hlam] at hd
    have hab : 602 / 100 * t * |a| + |b| ≤ (1 + 1 / 2 ^ 18) * (602 / 100 * t * Mj + Mj1) := by
      have := mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num : (0 : ℝ) ≤ 602 / 100) ht0)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hd (mul_nonneg hP.le hMj)
    have h2 : 𝐮 * (602 / 100 * t * |a| + |b|) * (P * Mj) ≤
        𝐮 * ((1 + 1 / 2 ^ 18) * (602 / 100 * t * Mj + Mj1)) * (P * Mj) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hP.le hMj)
      exact mul_le_mul_of_nonneg_left hab hu
    have e : 𝐮 * ((1 + 1 / 2 ^ 18) * (602 / 100 * t * Mj + Mj1)) * (P * Mj) =
        𝐮 * (1 + 1 / 2 ^ 18) * S := by rw [hSdef]; ring
    linarith
  have hη : 1 / 2 ^ 1070 * (P * Mj) ≤ 𝐮 * (1 / 2 ^ 700) := by
    have : P * Mj ≤ 2 ^ 303 := by nlinarith
    have h := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ 1 / 2 ^ 1070 by positivity)
    have e : (1 : ℝ) / 2 ^ 1070 * 2 ^ 303 ≤ 𝐮 * (1 / 2 ^ 700) := by norm_num [unitRoundoff64]
    linarith
  have hfin : |d| * (P * Mj) ≤ 𝐮 * (13 / 5 * (1 + 1 / 2 ^ 18) * (1 + 1404 / 100 * t) + 1 / 2 ^ 700) := by
    have hu : (0 : ℝ) ≤ 𝐮 * (1 + 1 / 2 ^ 18) := by norm_num [unitRoundoff64]
    have := mul_le_mul_of_nonneg_left hSB hu
    nlinarith
  have e : |d| * (P * (Mj * Mm)) = |d| * (P * Mj) * Mm := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hfin hMm
  linarith

theorem sum_linear (A B : ℝ) : ∀ N : ℕ,
    ∑ k ∈ range N, (A + B * ((k : ℝ) + 1)) = A * N + B * (N * (N + 1) / 2)
  | 0 => by simp
  | N + 1 => by
    rw [sum_range_succ, sum_linear A B N]
    push_cast
    ring

/-- The forward recurrence with bounded local errors, for `2 n ≤ x`. -/
theorem forward (x : ℝ) (hx : 4 ≤ x) (hxb : x ≤ 2 ^ 302) (F : ℕ → ℝ)
    (hF : ∀ k, F (k + 2) = lam x (k + 1) * F (k + 1) - F k) (hFM : ∀ k, |F k| ≤ modn x k)
    (f : ℕ → Float) (n : ℕ) (hn : 2 * (n : ℝ) ≤ x) (hn2 : n ≤ 2 ^ 31)
    (h0 : Finite (f 0).toBits ∧ |value (f 0).toBits - F 0| ≤ 10 * 𝐮 * modn x 0)
    (h1 : Finite (f 1).toBits ∧ |value (f 1).toBits - F 1| ≤ 12 * 𝐮 * modn x 1)
    (hstep : ∀ k, k + 2 ≤ n → Finite (f k).toBits → Finite (f (k + 1)).toBits →
      |value (f k).toBits| ≤ 1 → |value (f (k + 1)).toBits| ≤ 1 →
      Finite (f (k + 2)).toBits ∧
        |value (f (k + 2)).toBits -
            (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)| ≤
          𝐮 * (301 / 100 * lam x (k + 1) * |value (f (k + 1)).toBits| + |value (f k).toBits|) +
            1 / 2 ^ 1070) :
    ∀ m, m ≤ n → Finite (f m).toBits ∧
      |value (f m).toBits - F m| ≤ (17 + 12 * (m : ℝ)) * 𝐮 * modn x m := by
  have hx0 : 0 < x := by linarith
  have hu : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  have hrec : ∀ k, value (f (k + 2)).toBits - F (k + 2) =
      lam x (k + 1) * (value (f (k + 1)).toBits - F (k + 1)) - (value (f k).toBits - F k) +
        (value (f (k + 2)).toBits -
          (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) := by
    intro k; rw [hF k]; ring
  have hform : ∀ m, value (f m).toBits - F m = resp x (value (f 0).toBits - F 0)
      (value (f 1).toBits - F 1) (fun k => value (f (k + 2)).toBits -
        (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) m :=
    error_formula x hx0.ne' (fun k => value (f k).toBits - F k) (fun k => value (f (k + 2)).toBits -
        (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) hrec
  have hM0 : ∀ j : ℕ, 0 ≤ modn x j := fun j => Real.sqrt_nonneg _
  have hMle : ∀ j : ℕ, j ≤ n → modn x j ≤ 92 / 100 := by
    intro j hj
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    exact modn_le x hx j (by linarith)
  have hMb : ∀ j : ℕ, j ≤ n → π * x / 2 * modn x j ^ 2 * (x - j) ≤ 13 / 5 * x := by
    intro j hj
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    exact modn_bound x (by linarith) j (by linarith)
  have hcoef : ∀ j : ℕ, j ≤ n → (17 + 12 * (j : ℝ)) * 𝐮 ≤ 1 / 2 ^ 18 := by
    intro j hj
    have : (j : ℝ) ≤ 2 ^ 31 := by exact_mod_cast le_trans hj hn2
    rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
    nlinarith
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | h2
    · refine ⟨h0.1, le_trans h0.2 ?_⟩
      have : 10 * 𝐮 ≤ (17 + 12 * ((0 : ℕ) : ℝ)) * 𝐮 := by
        push_cast; nlinarith
      exact mul_le_mul_of_nonneg_right this (hM0 0)
    · refine ⟨h1.1, le_trans h1.2 ?_⟩
      have : 12 * 𝐮 ≤ (17 + 12 * ((1 : ℕ) : ℝ)) * 𝐮 := by
        push_cast; nlinarith
      exact mul_le_mul_of_nonneg_right this (hM0 1)
    · obtain ⟨N, rfl⟩ : ∃ N, m = N + 2 := ⟨m - 2, by omega⟩
      have hprev : ∀ j, j < N + 2 → Finite (f j).toBits ∧
          |value (f j).toBits| ≤ (1 + 1 / 2 ^ 18) * modn x j ∧ |value (f j).toBits| ≤ 1 := by
        intro j hj
        obtain ⟨hf, he'⟩ := ih j hj (by omega)
        have hc := hcoef j (by omega)
        have hF' := hFM j
        have hvj : |value (f j).toBits| ≤ |F j| + |value (f j).toBits - F j| := by
          have := abs_add_le (F j) (value (f j).toBits - F j)
          rw [show F j + (value (f j).toBits - F j) = value (f j).toBits by ring] at this
          exact this
        have hb : |value (f j).toBits| ≤ (1 + 1 / 2 ^ 18) * modn x j := by
          have := mul_le_mul_of_nonneg_right hc (hM0 j)
          nlinarith
        refine ⟨hf, hb, ?_⟩
        have := hMle j (by omega)
        nlinarith
      obtain ⟨fa, ba, ma⟩ := hprev N (by omega)
      obtain ⟨fb, bb, mb⟩ := hprev (N + 1) (by omega)
      obtain ⟨hfin, -⟩ := hstep N (by omega) fa fb ma mb
      refine ⟨hfin, ?_⟩
      rw [hform (N + 2)]
      unfold resp
      rw [show N + 2 - 1 = N + 1 by omega]
      try dsimp only
      have hMm0 : 0 ≤ modn x (N + 2) := hM0 _
      -- the starting errors
      have he0 : |value (f 0).toBits - F 0| ≤ 10 * 𝐮 * modn x 0 := h0.2
      have he1 : |value (f 1).toBits - F 1| ≤ 12 * 𝐮 * modn x 1 := h1.2
      have hk0 := kern_le x hx0 0 (N + 2)
      have hk1 := kern_le x hx0 1 (N + 2)
      have hbp := base_product x (by linarith)
      have hstart : |(value (f 1).toBits - F 1) * kern x 0 (N + 2) -
          (value (f 0).toBits - F 0) * kern x 1 (N + 2)| ≤ 286 / 10 * 𝐮 * (modn x (N + 2)) := by
        have := abs_sub ((value (f 1).toBits - F 1) * kern x 0 (N + 2))
          ((value (f 0).toBits - F 0) * kern x 1 (N + 2))
        rw [abs_mul, abs_mul] at this
        have a1 := mul_le_mul he1 hk0 (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hu) (hM0 1))
        have a2 := mul_le_mul he0 hk1 (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hu) (hM0 0))
        have e1 : 12 * 𝐮 * modn x 1 * (π * x / 2 * (modn x 0 * (modn x (N + 2)))) +
            10 * 𝐮 * modn x 0 * (π * x / 2 * (modn x 1 * (modn x (N + 2)))) =
            22 * 𝐮 * (modn x (N + 2)) * (π * x / 2 * (modn x 0 * modn x 1)) := by ring
        have a3 := mul_le_mul_of_nonneg_left hbp
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 22) hu) hMm0)
        linarith
      -- the steps
      have hterm : ∀ k ∈ range (N + 1), |(value (f (k + 2)).toBits -
          (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) * kern x (k + 1) (N + 2)| ≤
          𝐮 * (modn x (N + 2)) * (13 / 5 * (1 + 1 / 2 ^ 18) + 1 / 2 ^ 700 +
            13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x * ((k : ℝ) + 1)) := by
        intro k hk
        rw [mem_range] at hk
        obtain ⟨fk, bk, mk⟩ := hprev k (by omega)
        obtain ⟨fk1, bk1, mk1⟩ := hprev (k + 1) (by omega)
        obtain ⟨-, hdk⟩ := hstep k (by omega) fk fk1 mk mk1
        have hkl := kern_le x hx0 (k + 1) (N + 2)
        rw [abs_mul]
        have hkn : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
        have hcj1 : π * x / 2 * modn x k ^ 2 * (x - (((k + 1 : ℕ) : ℝ) - 1)) ≤ 13 / 5 * x := by
          have := hMb k (by omega)
          have e : x - (((k + 1 : ℕ) : ℝ) - 1) = x - k := by push_cast <;> ring
          rw [e]
          exact this
        have h := term_bound (j := ((k + 1 : ℕ) : ℝ)) (Mm := modn x (N + 2))
          (a := value (f (k + 1)).toBits) (b := value (f k).toBits)
          (d := value (f (k + 2)).toBits -
            (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) hx hxb
          (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by linarith) (hM0 _)
          (hM0 _) hMm0 (by linarith [hMle (k + 1) (by omega)]) (hMb (k + 1) (by omega)) hcj1
          bk1 bk hdk
        have e1 : 𝐮 * (modn x (N + 2)) * (13 / 5 * (1 + 1 / 2 ^ 18) * (1 + 1404 / 100 * (((k + 1 : ℕ) : ℝ) / x)) +
            1 / 2 ^ 700) = 𝐮 * (modn x (N + 2)) * (13 / 5 * (1 + 1 / 2 ^ 18) + 1 / 2 ^ 700 +
              13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x * ((k : ℝ) + 1)) := by
          push_cast <;> ring
        have := mul_le_mul_of_nonneg_left hkl (abs_nonneg (value (f (k + 2)).toBits -
          (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)))
        linarith
      have hS : |∑ k ∈ range (N + 1), (value (f (k + 2)).toBits -
          (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) * kern x (k + 1) (N + 2)| ≤
          𝐮 * (modn x (N + 2)) * ((13 / 5 * (1 + 1 / 2 ^ 18) + 1 / 2 ^ 700) * ((N + 1 : ℕ) : ℝ) +
            13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x *
              (((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1) / 2)) :=
        calc _ ≤ ∑ k ∈ range (N + 1), |(value (f (k + 2)).toBits -
              (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) *
                kern x (k + 1) (N + 2)| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ range (N + 1), 𝐮 * (modn x (N + 2)) * (13 / 5 * (1 + 1 / 2 ^ 18) + 1 / 2 ^ 700 +
              13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x * ((k : ℝ) + 1)) := sum_le_sum hterm
          _ = _ := by rw [← mul_sum, sum_linear]
      -- the arithmetic
      have hNx : 2 * ((N : ℝ) + 2) ≤ x := by
        have : ((N + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
        push_cast at this
        linarith
      have hB : 13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x * (((N + 1 : ℕ) : ℝ) *
          (((N + 1 : ℕ) : ℝ) + 1) / 2) ≤ 13 / 5 * (1 + 1 / 2 ^ 18) * (351 / 100) * ((N : ℝ) + 1) := by
        push_cast
        have h1 : ((N : ℝ) + 1 + 1) / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
        have e : 13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) / x * (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1) / 2) =
            13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) * ((N : ℝ) + 1) / 2 * (((N : ℝ) + 1 + 1) / x) := by
          ring
        rw [e]
        have := mul_le_mul_of_nonneg_left h1
          (show 0 ≤ 13 / 5 * (1 + 1 / 2 ^ 18) * (1404 / 100) * ((N : ℝ) + 1) / 2 by positivity)
        linarith
      have hum : 0 ≤ 𝐮 * (modn x (N + 2)) := mul_nonneg hu hMm0
      have h3 := mul_le_mul_of_nonneg_left hB hum
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h4 : 286 / 10 + ((13 / 5 * (1 + 1 / 2 ^ 18) + 1 / 2 ^ 700) * ((N : ℝ) + 1) +
          13 / 5 * (1 + 1 / 2 ^ 18) * (351 / 100) * ((N : ℝ) + 1)) ≤ 17 + 12 * ((N : ℝ) + 2) := by
        linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hum
      have habs := abs_add_le ((value (f 1).toBits - F 1) * kern x 0 (N + 2) -
          (value (f 0).toBits - F 0) * kern x 1 (N + 2))
        (∑ k ∈ range (N + 1), (value (f (k + 2)).toBits -
          (lam x (k + 1) * value (f (k + 1)).toBits - value (f k).toBits)) * kern x (k + 1) (N + 2))
      push_cast at hS h3 ⊢
      linarith

#print axioms term_bound
#print axioms forward

end Verified.Examples.BesselForward
