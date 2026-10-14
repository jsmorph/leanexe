import Verified.Examples.TgammaPolyDDD
import Verified.Examples.Lgamma

/-!
**`Lgamma.polyDDDFst`**, the double-double Horner scheme of `Lgamma`, against the exact Horner values
`horner (cDD tab o) N L x m` of `TgammaPolyDDD`.  The loop is that of `Tgamma.polyDDD` with
`fastSum` in place of `sumDD`, so the proof is `TgammaPolyDDD.polyDDD_damped_core` with one more
hypothesis: each coefficient that `fastSum` adds dominates the product before it (`hdom`), which
gives `fastSum` the order of `fastTwoSum` (`polyFst_damped_core`, `polyFst_spec`).
-/

namespace Verified.Examples.LgammaPolyFst
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD
open Verified.Examples.Lgamma (polyDDDFst)

set_option exponentiation.threshold 4096

/-- `polyDDDFst` within `X ^ (N - 1) (el + (tB + Cl)/2^53) + (N - 1) polyEps` of the exact Horner
value, when each coefficient that `fastSum` adds dominates the product. -/
theorem polyFst_damped_core (hF : FmaSpec.FmaNearest) (tab : Array UInt64) (o n : UInt64) (x l : Float)
    (hn1 : 1 ≤ n.toNat) (hon : o.toNat + 2 * n.toNat < 2 ^ 63)
    (hfh : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k]!).toBits)
    (hfl : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits)
    (X M Ch Cl Λ L el Lb tB : ℝ)
    (hx : Finite x.toBits) (hX : |value x.toBits| ≤ X) (hX1 : X ≤ 1)
    (hCh : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k]!).toBits| ≤ Ch)
    (hCl : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits| ≤ Cl)
    (hl : Finite l.toBits) (hlL : |value l.toBits - L| ≤ el) (hLb : |value l.toBits| ≤ Lb)
    (htop : |value l.toBits| ≤ |value (Float.ofBits tab[o.toNat + 2 * (n.toNat - 1)]!).toBits|)
    (hM : ∀ m, m + 1 ≤ n.toNat → |horner (cDD tab o) n.toNat L (value x.toBits) m| ≤ M)
    (htBh : Lb ≤ tB ∨ polyT Ch Lb ≤ tB) (htB0 : 0 ≤ tB) (htBs : tB ≤ 2 ^ 797)
    (hcap : (tB + Cl) * (1 + 1 / 2 ^ 53) + (n.toNat - 1 : ℕ) * polyGrow M Ch Cl Λ ≤ Λ)
    (hsmall : el + (tB + Cl) / 2 ^ 53 + (n.toNat - 1 : ℕ) * polyEps X M Ch Cl Λ + Λ ≤ 1)
    (hsize : Ch + M + 2 ≤ 2 ^ 797) (hLb1 : Lb + Cl ≤ 2 ^ 797) (hΛpos : 0 ≤ Λ)
    (hdom : ∀ k, k + 2 ≤ n.toNat → (M + 1) * X * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      |value (Float.ofBits tab[o.toNat + 2 * k]!).toBits|) :
    Finite (polyDDDFst tab o n x l).1.toBits ∧ Finite (polyDDDFst tab o n x l).2.toBits ∧
      |value (polyDDDFst tab o n x l).1.toBits + value (polyDDDFst tab o n x l).2.toBits -
          horner (cDD tab o) n.toNat L (value x.toBits) (n.toNat - 1)| ≤
        X ^ (n.toNat - 1) * (el + (tB + Cl) / 2 ^ 53) + (n.toNat - 1 : ℕ) * polyEps X M Ch Cl Λ ∧
      |value (polyDDDFst tab o n x l).2.toBits| ≤ Λ := by
  set N := n.toNat with hN
  set vx := value x.toBits with hvx
  set ε := polyEps X M Ch Cl Λ with hε
  set g := polyGrow M Ch Cl Λ with hg
  set E0 := el + (tB + Cl) / 2 ^ 53 with hE0
  set Λ0 := (tB + Cl) * (1 + 1 / 2 ^ 53) with hΛ0
  obtain ⟨hit1, hit2, hn1eq⟩ := idx_top o n hn1 hon
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hX
  have hLb0' : 0 ≤ Lb := (abs_nonneg _).trans hLb
  have hCh0' : 0 ≤ Ch := (abs_nonneg _).trans (hCh 0 (by omega))
  have htB0' : 0 ≤ tB := htB0
  have hCh0 : 0 ≤ Ch := (abs_nonneg _).trans (hCh 0 (by omega))
  have hCl0 : 0 ≤ Cl := (abs_nonneg _).trans (hCl 0 (by omega))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by omega))
  have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans hLb
  have hel0 : 0 ≤ el := (abs_nonneg _).trans hlL
  have hg0 : 0 ≤ g := by
    rw [hg, polyGrow]
    positivity
  have hε0 : 0 ≤ ε := by
    rw [hε, polyEps, polyLow]
    positivity
  have hΛ1 : Λ ≤ 1 := by
    have : 0 ≤ ((N - 1 : ℕ) : ℝ) * ε := by positivity
    have : 0 ≤ E0 := add_nonneg hel0 (div_nonneg (add_nonneg htB0' hCl0) (by positivity))
    linarith
  -- the loop
  obtain ⟨f, hf⟩ : ∃ f : UInt64 → Float × Float → Float × Float, f = fun j s =>
      let i := n - 2 - j
      let (ch, cl) := mulDDD x s.1 s.2
      fastSum (entry tab (o + 2 * i)) (entry tab (o + 2 * i + 1)) ch cl := ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init : Float × Float, init =
      ((fastTwoSum (entry tab (o + 2 * (n - 1))) l).1,
        (fastTwoSum (entry tab (o + 2 * (n - 1))) l).2 + entry tab (o + 2 * (n - 1) + 1)) :=
    ⟨_, rfl⟩
  have hdef : polyDDDFst tab o n x l = LeanExe.loop (n - 1) init f := by
    rw [hf, hinit]
    rfl
  have key : ∀ m, m + 1 ≤ N →
      Finite (LeanExe.loop (UInt64.ofNat m) init f).1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat m) init f).2.toBits ∧
      |value (LeanExe.loop (UInt64.ofNat m) init f).1.toBits +
          value (LeanExe.loop (UInt64.ofNat m) init f).2.toBits - horner (cDD tab o) N L vx m| ≤
        X ^ m * E0 + m * ε ∧
      |value (LeanExe.loop (UInt64.ofNat m) init f).2.toBits| ≤ Λ0 + m * g := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : LeanExe.loop (UInt64.ofNat 0) init f = init := by simp [LeanExe.loop]
      rw [h0]
      have he1 : entry tab (o + 2 * (n - 1)) = Float.ofBits tab[o.toNat + 2 * (N - 1)]! :=
        entry_eq _ _ _ hit1
      have he2 : entry tab (o + 2 * (n - 1) + 1) = Float.ofBits tab[o.toNat + 2 * (N - 1) + 1]! :=
        entry_eq _ _ _ hit2
      rw [hinit, he1, he2]
      have hhi := hfh (N - 1) (by omega)
      have hlo := hfl (N - 1) (by omega)
      have hChi := hCh (N - 1) (by omega)
      have hClo := hCl (N - 1) (by omega)
      obtain ⟨hsf, htf, hsum, htb4, htb5⟩ := fastTwoSum_spec _ l hhi hl htop
        (by linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 900)])
      have hsb := high_bound _ _ _ hsum htb5
      set t := (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).2
      set lo := Float.ofBits tab[o.toNat + 2 * (N - 1) + 1]!
      have htb' : |value t.toBits| ≤ tB := by
        rcases htBh with hb | hb
        · exact htb4.trans (hLb.trans hb)
        refine le_trans ?_ hb
        have h1 := abs_add_le (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits)
          (value l.toBits)
        have h2 := mul_le_mul_of_nonneg_right
          (show |value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value l.toBits| ≤ Ch + Lb
            by linarith) (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
        rw [polyT]
        have h3 : |value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits| / 2 ^ 52 ≤
            ((Ch + Lb) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 :=
          div_le_div_of_nonneg_right (by linarith) (by norm_num)
        linarith
      have hw0 := fapprox_add (fapprox_self t htf) (fapprox_self lo hlo) (tB + Cl)
        (by
          simp only [add_zero]
          exact (abs_add_le _ _).trans (by linarith))
        (by linarith [(by norm_num : (2 : ℝ) ^ 797 + 2 ^ 797 < 2 ^ 1023)])
      have hw : |value (t + lo).toBits - (value t.toBits + value lo.toBits)| ≤ (tB + Cl) / 2 ^ 53 := by
        have := hw0.2
        simp only [zero_add] at this
        exact this
      refine ⟨hsf, hw0.1, ?_, ?_⟩
      · simp only [horner, Nat.cast_zero, zero_mul, add_zero, cDD, pow_zero, one_mul]
        rw [show value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits +
            value (t + lo).toBits -
            (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value lo.toBits + L) =
          (value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits + value t.toBits -
            (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value l.toBits)) +
          (value (t + lo).toBits - (value t.toBits + value lo.toBits)) + (value l.toBits - L) by ring,
          hsum, sub_self, zero_add]
        exact (abs_add_le _ _).trans (by rw [hE0]; linarith)
      · simp only [Nat.cast_zero, zero_mul, add_zero]
        have h1 := abs_sub_abs_le_abs_sub (value (t + lo).toBits) (value t.toBits + value lo.toBits)
        have h2 := abs_add_le (value t.toBits) (value lo.toBits)
        rw [hΛ0]
        linarith
    | succ m ih =>
      intro hm
      obtain ⟨hs1, hs2, hse, hsl⟩ := ih (by omega)
      rw [loop_succ m (by omega) init f]
      generalize LeanExe.loop (UInt64.ofNat m) init f = s at hs1 hs2 hse hsl ⊢
      obtain ⟨hi1, hi2⟩ := idx o n m (by omega) hon
      set i := N - 2 - m with hidef
      have hstep : f (UInt64.ofNat m) s = fastSum (Float.ofBits tab[o.toNat + 2 * i]!)
          (Float.ofBits tab[o.toNat + 2 * i + 1]!) (mulDDD x s.1 s.2).1 (mulDDD x s.1 s.2).2 := by
        rw [hf, ← entry_eq _ _ _ hi1, ← entry_eq _ _ _ hi2]
      rw [hstep]
      have hhi := hfh i (by omega)
      have hlo := hfl i (by omega)
      have hChi := hCh i (by omega)
      have hClo := hCl i (by omega)
      -- bounds on the state
      have hmN : (m : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ N - 1)
      have hE0nn : 0 ≤ E0 := add_nonneg hel0 (div_nonneg (add_nonneg htB0' hCl0) (by positivity))
      have hXm : X ^ m ≤ 1 := pow_le_one₀ hX0 hX1
      have hEm : X ^ m * E0 + m * ε ≤ E0 + (N - 1 : ℕ) * ε := by
        have := mul_le_mul_of_nonneg_right hmN hε0
        have := mul_le_mul_of_nonneg_right hXm hE0nn
        linarith
      have hΛm : Λ0 + m * g ≤ Λ := by
        have := mul_le_mul_of_nonneg_right hmN hg0
        linarith
      have hTm := hM m (by omega)
      have hs1b : |value s.1.toBits| ≤ M + 1 := by
        have h1 := abs_sub_abs_le_abs_sub (value s.1.toBits)
          (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m)
        rw [show value s.1.toBits -
            (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m) =
          horner (cDD tab o) N L vx m - value s.2.toBits by ring] at h1
        have h2 := abs_sub (horner (cDD tab o) N L vx m) (value s.2.toBits)
        linarith
      set Λm := Λ0 + m * g with hΛmdef
      have hH : |value s.1.toBits| * |vx| ≤ (M + 1) * X :=
        mul_le_mul hs1b hX (abs_nonneg _) (by linarith)
      have hL : |value s.2.toBits| * |vx| ≤ Λm * X :=
        mul_le_mul hsl hX (abs_nonneg _) (le_trans (abs_nonneg _) hsl)
      have hHmax : (M + 1) * X ≤ 2 ^ 900 := by
        have : (M + 1) * X ≤ M + 1 := mul_le_of_le_one_right (by linarith) hX1
        linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 900)]
      have hLmax : Λm * X ≤ 2 ^ 900 := by
        have : Λm * X ≤ Λm := mul_le_of_le_one_right (le_trans (abs_nonneg _) hsl) hX1
        linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)]
      obtain ⟨hm1f, hm2f, hme, hm2b, hm1b⟩ := mulDDD_spec hF x s.1 s.2 hx hs1 hs2 _ _ hH hL
        hHmax hLmax
      generalize mulDDD x s.1 s.2 = mm at hm1f hm2f hme hm2b hm1b ⊢
      obtain ⟨m1, m2⟩ := mm
      simp only at hm1f hm2f hme hm2b hm1b ⊢
      set Lm := Cl + (Λm * X * (1 + 1 / 2 ^ 51) + (M + 1) * X / 2 ^ 52 + 1 / 2 ^ 1071) with hLm
      have hLsum : |value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits| + |value m2.toBits| ≤ Lm := by
        rw [hLm]; linarith
      have hMX : (M + 1) * X ≤ M + 1 := mul_le_of_le_one_right (by linarith) hX1
      have hLmle : Lm ≤ polyLow X M Cl Λ := by
        have h1 : Λm * X ≤ Λ * X := mul_le_mul_of_nonneg_right hΛm hX0
        have h2 : Λm * X * (1 + 1 / 2 ^ 51) ≤ Λ * X * (1 + 1 / 2 ^ 51) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        rw [hLm, polyLow]
        linarith
      have hpolyLow : polyLow X M Cl Λ ≤ 2 ^ 800 := by
        rw [polyLow]
        have h1 : Λ * X ≤ 1 := mul_le_one₀ hΛ1 hX0 hX1
        have h2 : Λ * X * (1 + 1 / 2 ^ 51) ≤ 1 * (1 + 1 / 2 ^ 51) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h4 : (M + 1) * X / 2 ^ 52 ≤ (M + 1) * X := div_le_self (by positivity) (by norm_num)
        linarith [(by norm_num : (2 : ℝ) ^ 797 + 2 + 2 ^ 797 + 1 ≤ 2 ^ 800)]
      have h5 : (M + 1) * X * (1 + 1 / 2 ^ 53) ≤ (M + 1) * (1 + 1 / 2 ^ 53) :=
        mul_le_mul_of_nonneg_right hMX (by positivity)
      have hm1lim : |value m1.toBits| < 2 ^ 898 := by
        linarith [(by norm_num : (2 : ℝ) ^ 797 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 < 2 ^ 898)]
      have hdomi := hdom i (by omega)
      have hm1c : |value m1.toBits| ≤ |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits| := by
        have : (M + 1) * X * (1 + 1 / 2 ^ 53) ≥ |value s.1.toBits| * |vx| * (1 + 1 / 2 ^ 53) :=
          mul_le_mul_of_nonneg_right hH (by positivity)
        linarith
      obtain ⟨htf, htlf, hte, htlb⟩ := fastSum_spec _ _ m1 m2 hhi hlo hm1f hm2f hm1c
        (by linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 898)]) Lm hLsum
        (hLmle.trans hpolyLow)
      have ht1b : |value (fastSum (Float.ofBits tab[o.toNat + 2 * i]!)
          (Float.ofBits tab[o.toNat + 2 * i + 1]!) m1 m2).1.toBits| ≤
          |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits + value m1.toBits| * (1 + 1 / 2 ^ 51) +
            1 / 2 ^ 1073 := by
        obtain ⟨-, -, hs, -, hsl⟩ := fastTwoSum_spec _ m1 hhi hm1f hm1c
          (by linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 900)])
        exact high_bound _ _ _ hs hsl
      generalize fastSum (Float.ofBits tab[o.toNat + 2 * i]!) (Float.ofBits tab[o.toNat + 2 * i + 1]!)
        m1 m2 = tt at htf htlf hte htlb ht1b ⊢
      obtain ⟨t1, t2⟩ := tt
      simp only at htf htlf hte htlb ht1b ⊢
      have ht1 : |value t1.toBits| ≤ 2 * (Ch + M + 1) := by
        have h1 : |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits + value m1.toBits| ≤
            Ch + ((M + 1) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075) := by
          have := abs_add_le (value (Float.ofBits tab[o.toNat + 2 * i]!).toBits) (value m1.toBits)
          linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
        linarith
      refine ⟨htf, htlf, ?_, ?_⟩
      · -- the error
        have hhor : horner (cDD tab o) N L vx (m + 1) =
            value (Float.ofBits tab[o.toNat + 2 * i]!).toBits +
              value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits + vx * horner (cDD tab o) N L vx m := by
          simp only [horner, cDD, hidef]
        rw [hhor]
        have hsplit : value t1.toBits + value t2.toBits -
            (value (Float.ofBits tab[o.toNat + 2 * i]!).toBits +
              value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits + vx * horner (cDD tab o) N L vx m) =
            (value t1.toBits + value t2.toBits -
              (value (Float.ofBits tab[o.toNat + 2 * i]!).toBits +
                value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits +
                (value m1.toBits + value m2.toBits))) +
            (value m1.toBits + value m2.toBits - vx * (value s.1.toBits + value s.2.toBits)) +
            vx * (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m) := by ring
        rw [hsplit]
        have hprop : |vx * (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m)| ≤
            X ^ (m + 1) * E0 + m * ε := by
          rw [abs_mul]
          have hE : 0 ≤ X ^ m * E0 + m * ε := le_trans (abs_nonneg _) hse
          have hmε : 0 ≤ (m : ℝ) * ε := by positivity
          calc |vx| * |value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m|
              ≤ X * (X ^ m * E0 + m * ε) := mul_le_mul hX hse (abs_nonneg _) hX0
            _ = X ^ (m + 1) * E0 + X * (m * ε) := by rw [pow_succ]; ring
            _ ≤ X ^ (m + 1) * E0 + m * ε := by
              have := mul_le_of_le_one_left hmε hX1
              linarith
        have herr1 : (3 * (Λm * X) + (M + 1) * X / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 ≤
            (3 * (Λ * X) + (M + 1) * X / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 := by
          have : Λm * X ≤ Λ * X := mul_le_mul_of_nonneg_right hΛm hX0
          gcongr
        have herr2 : (3 * Lm + |value t1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ≤
            (3 * polyLow X M Cl Λ + 2 * (Ch + M + 1) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
          gcongr
        have hε' : ε = (3 * (Λ * X) + (M + 1) * X / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 +
            (3 * polyLow X M Cl Λ + 2 * (Ch + M + 1) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
          rw [hε, polyEps]
        have h3 := abs_add_le (value t1.toBits + value t2.toBits -
              (value (Float.ofBits tab[o.toNat + 2 * i]!).toBits +
                value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits +
                (value m1.toBits + value m2.toBits)) +
            (value m1.toBits + value m2.toBits - vx * (value s.1.toBits + value s.2.toBits)))
          (vx * (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m))
        have h4 := abs_add_le (value t1.toBits + value t2.toBits -
              (value (Float.ofBits tab[o.toNat + 2 * i]!).toBits +
                value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits +
                (value m1.toBits + value m2.toBits)))
            (value m1.toBits + value m2.toBits - vx * (value s.1.toBits + value s.2.toBits))
        rw [← hvx] at hme
        push_cast
        linarith
      · -- the low part
        have hgrow : Lm * (1 + 1 / 2 ^ 51) + |value t1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ≤ Λm + g := by
          rw [hLm, hg, polyGrow]
          have hΛm0 : 0 ≤ Λm := le_trans (abs_nonneg _) hsl
          have hA : Λm * X ≤ Λm := mul_le_of_le_one_right hΛm0 hX1
          have hB := mul_le_mul_of_nonneg_right hA
            (by positivity : (0 : ℝ) ≤ (1 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 51))
          have hC : Λm * (1 / 2 ^ 49) ≤ Λ * (1 / 2 ^ 49) :=
            mul_le_mul_of_nonneg_right hΛm (by positivity)
          have hk2 : (M + 1) * X / 2 ^ 52 ≤ (M + 1) / 2 ^ 52 :=
            div_le_div_of_nonneg_right hMX (by norm_num)
          have hk3 := mul_le_mul_of_nonneg_right hk2 (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
          linarith
        push_cast
        linarith
  obtain ⟨h1, h2, h3, h4⟩ := key (N - 1) (by omega)
  rw [hdef, hn1eq]
  refine ⟨h1, h2, h3, h4.trans hcap⟩

/-- **`polyDDDFst`** within `el + (Lb + Cl)/2^53 + (N - 1) polyEps` of the exact Horner value, when
each coefficient that `fastSum` adds dominates the product. -/
theorem polyFst_spec (hF : FmaSpec.FmaNearest) (tab : Array UInt64) (o n : UInt64) (x l : Float)
    (hn1 : 1 ≤ n.toNat) (hon : o.toNat + 2 * n.toNat < 2 ^ 63)
    (hfh : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k]!).toBits)
    (hfl : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits)
    (X M Ch Cl Λ L el Lb : ℝ)
    (hx : Finite x.toBits) (hX : |value x.toBits| ≤ X) (hX1 : X ≤ 1)
    (hCh : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k]!).toBits| ≤ Ch)
    (hCl : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits| ≤ Cl)
    (hl : Finite l.toBits) (hlL : |value l.toBits - L| ≤ el) (hLb : |value l.toBits| ≤ Lb)
    (htop : |value l.toBits| ≤ |value (Float.ofBits tab[o.toNat + 2 * (n.toNat - 1)]!).toBits|)
    (hM : ∀ m, m + 1 ≤ n.toNat → |horner (cDD tab o) n.toNat L (value x.toBits) m| ≤ M)
    (hcap : (Lb + Cl) * (1 + 1 / 2 ^ 53) + (n.toNat - 1 : ℕ) * polyGrow M Ch Cl Λ ≤ Λ)
    (hsmall : el + (Lb + Cl) / 2 ^ 53 + (n.toNat - 1 : ℕ) * polyEps X M Ch Cl Λ + Λ ≤ 1)
    (hsize : Ch + M + 2 ≤ 2 ^ 797) (hLb1 : Lb + Cl ≤ 2 ^ 797) (hΛpos : 0 ≤ Λ)
    (hdom : ∀ k, k + 2 ≤ n.toNat → (M + 1) * X * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
      |value (Float.ofBits tab[o.toNat + 2 * k]!).toBits|) :
    Finite (polyDDDFst tab o n x l).1.toBits ∧ Finite (polyDDDFst tab o n x l).2.toBits ∧
      |value (polyDDDFst tab o n x l).1.toBits + value (polyDDDFst tab o n x l).2.toBits -
          horner (cDD tab o) n.toNat L (value x.toBits) (n.toNat - 1)| ≤
        el + (Lb + Cl) / 2 ^ 53 + (n.toNat - 1 : ℕ) * polyEps X M Ch Cl Λ ∧
      |value (polyDDDFst tab o n x l).2.toBits| ≤ Λ := by
  have hCl0 : 0 ≤ Cl := (abs_nonneg _).trans (hCl 0 (by omega))
  have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans hLb
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hX
  have hel0 : 0 ≤ el := (abs_nonneg _).trans hlL
  obtain ⟨h1, h2, h3, h4⟩ := polyFst_damped_core hF tab o n x l hn1 hon hfh hfl X M Ch Cl Λ L el
    Lb Lb hx hX hX1 hCh hCl hl hlL hLb htop hM (Or.inl le_rfl) hLb0 (by linarith) hcap hsmall hsize
    hLb1 hΛpos hdom
  refine ⟨h1, h2, h3.trans ?_, h4⟩
  have hE : 0 ≤ el + (Lb + Cl) / 2 ^ 53 := add_nonneg hel0 (div_nonneg (add_nonneg hLb0 hCl0) (by positivity))
  have := mul_le_mul_of_nonneg_right (pow_le_one₀ hX0 hX1 : X ^ (n.toNat - 1) ≤ 1) hE
  linarith

#print axioms polyFst_damped_core
#print axioms polyFst_spec

end Verified.Examples.LgammaPolyFst
