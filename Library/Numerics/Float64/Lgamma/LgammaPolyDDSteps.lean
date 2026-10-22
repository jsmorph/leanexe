import Library.Numerics.Float64.Lgamma.LgammaPolyDD

/-!
`Lgamma.polyDD` with bounds that depend on the step (`polyDD_steps`).
`LgammaPolyDD.polyDD_damped_core` bounds the high part of every state by `M + 1` and every low part
by one cap `Λ`, which suits coefficients near 1.  The kernels of `asSinpipidAccurate` have
coefficients from `2.5 · 10^-2` down to `5 · 10^-26`, and a cap above the smallest coefficients
breaks the dominance that each `fastSum` needs.  Here the caller gives the error `E m`, the cap
`Λ m` on the low part, and the bound `K m` on the high part of the state after `m` steps, and
checks the conditions of each step (`epsS`, `growS`), which come from `mulDD_spec` and
`fastSum_spec` as in `polyDD_damped_core`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPolyDDSteps
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaPoly Library.Numerics.Float64.Tgamma.TgammaPolyDDD Library.Numerics.Float64.Tgamma.TgammaMul

set_option exponentiation.threshold 4096

/-- The sum of the low parts that the `fastSum` of a step adds: the coefficient's low word and the
low part of the product. -/
noncomputable def lowS (Xh Xl K Λ Cl : ℝ) : ℝ :=
  Cl + ((K * Xl + Λ * Xh) * (1 + 1 / 2 ^ 50) + K * Xh / 2 ^ 52 + 1 / 2 ^ 1070)

/-- The bound on the high part after the `fastSum` of a step. -/
noncomputable def topS (Xh K C : ℝ) : ℝ :=
  (C + (K * Xh * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075)) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073

/-- The error added by a step. -/
noncomputable def epsS (Xh Xl K Λ C Cl : ℝ) : ℝ :=
  Λ * Xl + (4 * (K * Xl + Λ * Xh) + K * Xh / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 +
    (3 * lowS Xh Xl K Λ Cl + topS Xh K C / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53

/-- The bound on the low part after a step. -/
noncomputable def growS (Xh Xl K Λ C Cl : ℝ) : ℝ :=
  lowS Xh Xl K Λ Cl * (1 + 1 / 2 ^ 51) + topS Xh K C / 2 ^ 51 + 1 / 2 ^ 1073

set_option maxHeartbeats 1000000 in
/-- **`polyDD` with bounds per step**: within `E (N - 1)` of the exact Horner value at `xh + xl`,
with the low part at most `Λ (N - 1)`, when each step satisfies the conditions of
`mulDD_spec` and `fastSum_spec` with the state's bounds `K m`, `E m`, and `Λ m`. -/
theorem polyDD_steps (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (o n : UInt64)
    (xh xl l : Float)
    (hn1 : 1 ≤ n.toNat) (hon : o.toNat + 2 * n.toNat < 2 ^ 63)
    (hfh : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k]!).toBits)
    (hfl : ∀ k < n.toNat, Finite (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits)
    (Xh Xl L el Lb tB : ℝ) (C Cl E Λ K : ℕ → ℝ)
    (hxh : Finite xh.toBits) (hxl : Finite xl.toBits) (hXh : |value xh.toBits| ≤ Xh)
    (hXl : |value xl.toBits| ≤ Xl) (hX1 : Xh + Xl ≤ 1)
    (hC : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k]!).toBits| ≤ C k)
    (hCl : ∀ k < n.toNat, |value (Float.ofBits tab[o.toNat + 2 * k + 1]!).toBits| ≤ Cl k)
    (hsz : ∀ k < n.toNat, C k ≤ 2 ^ 797 ∧ Cl k ≤ 2 ^ 797)
    (hl : Finite l.toBits) (hlL : |value l.toBits - L| ≤ el) (hLb : |value l.toBits| ≤ Lb)
    (htop : |value l.toBits| ≤ |value (Float.ofBits tab[o.toNat + 2 * (n.toNat - 1)]!).toBits|)
    (htBh : Lb ≤ tB ∨ polyT (C (n.toNat - 1)) Lb ≤ tB) (htBs : tB ≤ 2 ^ 797)
    (hE0 : el + (tB + Cl (n.toNat - 1)) / 2 ^ 53 ≤ E 0)
    (hΛ0 : (tB + Cl (n.toNat - 1)) * (1 + 1 / 2 ^ 53) ≤ Λ 0)
    (hK : ∀ m, m + 2 ≤ n.toNat →
      |horner (cDD tab o) n.toNat L (value xh.toBits + value xl.toBits) m| + E m + Λ m ≤ K m)
    (hKsz : ∀ m, m + 2 ≤ n.toNat → K m ≤ 2 ^ 797 ∧ Λ m ≤ 2 ^ 797)
    (hdom : ∀ m, m + 2 ≤ n.toNat →
      (|horner (cDD tab o) n.toNat L (value xh.toBits + value xl.toBits) m| + E m + Λ m) *
          |value xh.toBits| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |value (Float.ofBits tab[o.toNat + 2 * (n.toNat - 2 - m)]!).toBits|)
    (hEs : ∀ m, m + 2 ≤ n.toNat → (Xh + Xl) * E m +
      epsS Xh Xl (K m) (Λ m) (C (n.toNat - 2 - m)) (Cl (n.toNat - 2 - m)) ≤ E (m + 1))
    (hΛs : ∀ m, m + 2 ≤ n.toNat →
      growS Xh Xl (K m) (Λ m) (C (n.toNat - 2 - m)) (Cl (n.toNat - 2 - m)) ≤ Λ (m + 1)) :
    Finite (Lgamma.polyDD tab o n xh xl l).1.toBits ∧ Finite (Lgamma.polyDD tab o n xh xl l).2.toBits ∧
      |value (Lgamma.polyDD tab o n xh xl l).1.toBits + value (Lgamma.polyDD tab o n xh xl l).2.toBits -
          horner (cDD tab o) n.toNat L (value xh.toBits + value xl.toBits) (n.toNat - 1)| ≤
        E (n.toNat - 1) ∧
      |value (Lgamma.polyDD tab o n xh xl l).2.toBits| ≤ Λ (n.toNat - 1) := by
  set N := n.toNat with hN
  set vx := value xh.toBits + value xl.toBits with hvx
  obtain ⟨hit1, hit2, hn1eq⟩ := idx_top o n hn1 hon
  have hXh0 : 0 ≤ Xh := (abs_nonneg _).trans hXh
  have hXl0 : 0 ≤ Xl := (abs_nonneg _).trans hXl
  have hX0 : 0 ≤ Xh + Xl := by linarith
  have hX : |vx| ≤ Xh + Xl := (abs_add_le _ _).trans (by linarith)
  have hXh1 : Xh ≤ 1 := by linarith
  have hXl1 : Xl ≤ 1 := by linarith
  have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans hLb
  -- the loop
  obtain ⟨f, hf⟩ : ∃ f : UInt64 → Float × Float → Float × Float, f = fun j s =>
      let i := n - 2 - j
      let (ch, cl) := mulDD xh xl s.1 s.2
      fastSum (entry tab (o + 2 * i)) (entry tab (o + 2 * i + 1)) ch cl := ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init : Float × Float, init =
      ((fastTwoSum (entry tab (o + 2 * (n - 1))) l).1,
        (fastTwoSum (entry tab (o + 2 * (n - 1))) l).2 + entry tab (o + 2 * (n - 1) + 1)) :=
    ⟨_, rfl⟩
  have hdef : Lgamma.polyDD tab o n xh xl l = LeanExe.loop (n - 1) init f := by
    rw [hf, hinit]
    rfl
  have key : ∀ m, m + 1 ≤ N →
      Finite (LeanExe.loop (UInt64.ofNat m) init f).1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat m) init f).2.toBits ∧
      |value (LeanExe.loop (UInt64.ofNat m) init f).1.toBits +
          value (LeanExe.loop (UInt64.ofNat m) init f).2.toBits - horner (cDD tab o) N L vx m| ≤
        E m ∧
      |value (LeanExe.loop (UInt64.ofNat m) init f).2.toBits| ≤ Λ m := by
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
      have hChi := hC (N - 1) (by omega)
      have hClo := hCl (N - 1) (by omega)
      obtain ⟨hCsz, hClsz⟩ := hsz (N - 1) (by omega)
      have hCl0 : 0 ≤ Cl (N - 1) := (abs_nonneg _).trans hClo
      obtain ⟨hsf, htf, hsum, htb4, htb5⟩ := fastTwoSum_spec _ l hhi hl htop
        (by linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 900)])
      set t := (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).2
      set lo := Float.ofBits tab[o.toNat + 2 * (N - 1) + 1]!
      have htb' : |value t.toBits| ≤ tB := by
        rcases htBh with hb | hb
        · exact htb4.trans (hLb.trans hb)
        refine le_trans ?_ hb
        have h1 := abs_add_le (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits)
          (value l.toBits)
        have h2 := mul_le_mul_of_nonneg_right
          (show |value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value l.toBits| ≤
            C (N - 1) + Lb by linarith) (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
        rw [polyT]
        have h3 : |value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits| / 2 ^ 52 ≤
            ((C (N - 1) + Lb) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 := by
          have hsb := high_bound _ _ _ hsum htb5
          exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
        linarith
      have htB0 : 0 ≤ tB := (abs_nonneg _).trans htb'
      have hw0 := fapprox_add (fapprox_self t htf) (fapprox_self lo hlo) (tB + Cl (N - 1))
        (by
          simp only [add_zero]
          exact (abs_add_le _ _).trans (by linarith))
        (by linarith [(by norm_num : (2 : ℝ) ^ 797 + 2 ^ 797 < 2 ^ 1023)])
      have hw : |value (t + lo).toBits - (value t.toBits + value lo.toBits)| ≤
          (tB + Cl (N - 1)) / 2 ^ 53 := by
        have := hw0.2
        simp only [zero_add] at this
        exact this
      refine ⟨hsf, hw0.1, ?_, ?_⟩
      · simp only [horner, cDD]
        rw [show value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits +
            value (t + lo).toBits -
            (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value lo.toBits + L) =
          (value (fastTwoSum (Float.ofBits tab[o.toNat + 2 * (N - 1)]!) l).1.toBits + value t.toBits -
            (value (Float.ofBits tab[o.toNat + 2 * (N - 1)]!).toBits + value l.toBits)) +
          (value (t + lo).toBits - (value t.toBits + value lo.toBits)) + (value l.toBits - L) by ring,
          hsum, sub_self, zero_add]
        exact (abs_add_le _ _).trans (by linarith)
      · have h1 := abs_sub_abs_le_abs_sub (value (t + lo).toBits) (value t.toBits + value lo.toBits)
        have h2 := abs_add_le (value t.toBits) (value lo.toBits)
        linarith
    | succ m ih =>
      intro hm
      obtain ⟨hs1, hs2, hse, hsl⟩ := ih (by omega)
      rw [loop_succ m (by omega) init f]
      generalize LeanExe.loop (UInt64.ofNat m) init f = s at hs1 hs2 hse hsl ⊢
      obtain ⟨hi1, hi2⟩ := idx o n m (by omega) hon
      set i := N - 2 - m with hidef
      have hstep : f (UInt64.ofNat m) s = fastSum (Float.ofBits tab[o.toNat + 2 * i]!)
          (Float.ofBits tab[o.toNat + 2 * i + 1]!) (mulDD xh xl s.1 s.2).1 (mulDD xh xl s.1 s.2).2 := by
        rw [hf, ← entry_eq _ _ _ hi1, ← entry_eq _ _ _ hi2]
      rw [hstep]
      have hhi := hfh i (by omega)
      have hlo := hfl i (by omega)
      have hCi := hC i (by omega)
      have hCli := hCl i (by omega)
      obtain ⟨hCsz, hClsz⟩ := hsz i (by omega)
      obtain ⟨hKsz', hΛsz⟩ := hKsz m (by omega)
      have hKm := hK m (by omega)
      have hΛm0 : 0 ≤ Λ m := le_trans (abs_nonneg _) hsl
      have hs1h : |value s.1.toBits| ≤ |horner (cDD tab o) N L vx m| + E m + Λ m := by
        have h1 := abs_sub_abs_le_abs_sub (value s.1.toBits)
          (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m)
        rw [show value s.1.toBits -
            (value s.1.toBits + value s.2.toBits - horner (cDD tab o) N L vx m) =
          horner (cDD tab o) N L vx m - value s.2.toBits by ring] at h1
        have h2 := abs_sub (horner (cDD tab o) N L vx m) (value s.2.toBits)
        linarith
      have hs1b : |value s.1.toBits| ≤ K m := hs1h.trans hKm
      have hK0 : 0 ≤ K m := le_trans (abs_nonneg _) hs1b
      -- the bound on the product's high part at this point, below `K m * Xh`
      set Hm := (|horner (cDD tab o) N L vx m| + E m + Λ m) * |value xh.toBits| with hHm
      have hH : |value s.1.toBits| * |value xh.toBits| ≤ Hm :=
        mul_le_mul_of_nonneg_right hs1h (abs_nonneg _)
      have hHK : Hm ≤ K m * Xh := mul_le_mul hKm hXh (abs_nonneg _) hK0
      have hP1 : |value s.1.toBits| * |value xl.toBits| ≤ K m * Xl :=
        mul_le_mul hs1b hXl (abs_nonneg _) hK0
      have hP2 : |value s.2.toBits| * |value xh.toBits| ≤ Λ m * Xh :=
        mul_le_mul hsl hXh (abs_nonneg _) hΛm0
      have hL2 : |value s.2.toBits| * |value xl.toBits| ≤ Λ m * Xl :=
        mul_le_mul hsl hXl (abs_nonneg _) hΛm0
      have hKX : K m * Xh ≤ K m := mul_le_of_le_one_right hK0 hXh1
      have hKXl : K m * Xl ≤ K m := mul_le_of_le_one_right hK0 hXl1
      have hΛX : Λ m * Xh ≤ Λ m := mul_le_of_le_one_right hΛm0 hXh1
      have hHmax : Hm ≤ 2 ^ 900 := by
        linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 900)]
      have hPmax : K m * Xl + Λ m * Xh ≤ 2 ^ 900 := by
        linarith [(by norm_num : (2 : ℝ) ^ 797 + 2 ^ 797 < 2 ^ 900)]
      obtain ⟨hm1f, hm2f, hme, hm2b, hm1b⟩ := mulDD_spec hF xh xl s.1 s.2 hxh hxl hs1 hs2 _ _ _ _
        hH hP1 hP2 hL2 hHmax hPmax
      generalize mulDD xh xl s.1 s.2 = mm at hm1f hm2f hme hm2b hm1b ⊢
      obtain ⟨m1, m2⟩ := mm
      simp only at hm1f hm2f hme hm2b hm1b ⊢
      have hLsum : |value (Float.ofBits tab[o.toNat + 2 * i + 1]!).toBits| + |value m2.toBits| ≤
          lowS Xh Xl (K m) (Λ m) (Cl i) := by
        rw [lowS]; linarith
      have hlowS : lowS Xh Xl (K m) (Λ m) (Cl i) ≤ 2 ^ 800 := by
        rw [lowS]
        have h1 : (K m * Xl + Λ m * Xh) * (1 + 1 / 2 ^ 50) ≤ (2 ^ 797 + 2 ^ 797) * (1 + 1 / 2 ^ 50) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h2 : K m * Xh / 2 ^ 52 ≤ K m * Xh := div_le_self (mul_nonneg hK0 hXh0) (by norm_num)
        linarith [(by norm_num : (2 : ℝ) ^ 797 + (2 ^ 797 + 2 ^ 797) * (1 + 1 / 2 ^ 50) + 2 ^ 797 +
          1 / 2 ^ 1070 ≤ 2 ^ 800)]
      have hm1c : |value m1.toBits| ≤ |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits| :=
        hm1b.trans (hdom m (by omega))
      have hm1K : |value m1.toBits| ≤ K m * Xh * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
        have := mul_le_mul_of_nonneg_right hHK (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
        linarith
      have hilim : |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits| < 2 ^ 898 := by
        linarith [(by norm_num : (2 : ℝ) ^ 797 < 2 ^ 898)]
      obtain ⟨htf, htlf, hte, htlb⟩ := fastSum_spec _ _ m1 m2 hhi hlo hm1f hm2f hm1c hilim
        (lowS Xh Xl (K m) (Λ m) (Cl i)) hLsum hlowS
      have ht1b : |value (fastSum (Float.ofBits tab[o.toNat + 2 * i]!)
          (Float.ofBits tab[o.toNat + 2 * i + 1]!) m1 m2).1.toBits| ≤
          |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits + value m1.toBits| * (1 + 1 / 2 ^ 51) +
            1 / 2 ^ 1073 := by
        obtain ⟨-, -, hs, -, hsl⟩ := fastTwoSum_spec _ m1 hhi hm1f hm1c
          (by linarith [(by norm_num : (2 : ℝ) ^ 898 < 2 ^ 900)])
        exact high_bound _ _ _ hs hsl
      generalize fastSum (Float.ofBits tab[o.toNat + 2 * i]!) (Float.ofBits tab[o.toNat + 2 * i + 1]!)
        m1 m2 = tt at htf htlf hte htlb ht1b ⊢
      obtain ⟨t1, t2⟩ := tt
      simp only at htf htlf hte htlb ht1b ⊢
      have ht1 : |value t1.toBits| ≤ topS Xh (K m) (C i) := by
        rw [topS]
        have h1 : |value (Float.ofBits tab[o.toNat + 2 * i]!).toBits + value m1.toBits| ≤
            C i + (K m * Xh * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075) := by
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
            (Xh + Xl) * E m := by
          rw [abs_mul]; exact mul_le_mul hX hse (abs_nonneg _) hX0
        have herr2 : (3 * lowS Xh Xl (K m) (Λ m) (Cl i) + |value t1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
            2 ^ 53 ≤ (3 * lowS Xh Xl (K m) (Λ m) (Cl i) + topS Xh (K m) (C i) / 2 ^ 52 +
              1 / 2 ^ 1074) / 2 ^ 53 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          have := div_le_div_of_nonneg_right ht1 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
          linarith
        have hEm := hEs m (by omega)
        rw [epsS] at hEm
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
        linarith
      · -- the low part
        have hΛm := hΛs m (by omega)
        rw [growS] at hΛm
        have h2 := div_le_div_of_nonneg_right ht1 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
        linarith
  obtain ⟨h1, h2, h3, h4⟩ := key (N - 1) (by omega)
  rw [hdef, hn1eq]
  exact ⟨h1, h2, h3, h4⟩

#print axioms polyDD_steps

end Library.Numerics.Float64.Lgamma.LgammaPolyDDSteps
