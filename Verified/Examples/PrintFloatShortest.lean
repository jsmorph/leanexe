import Verified.Examples.PrintFloatChoice

/-!
`PrintFloat.shortest` computes the printers' choice (`shortest_spec`): its decimal `t · 10 ^ k`
lies in the rounding interval, `k` is the top exponent `J` or `J - 1`, and the decimal is
`PrintFloatShort.Choice` at `J`, so that `PrintFloatShort.shortest_of_choice` applies.
-/

namespace Verified.Examples.PrintFloatShortest
open PrintFloat Uscale UscaleTheorem ParseFloatRound PrintFloatShort PrintFloatQuot PrintFloatSearch
  PrintFloatPick PrintFloatChoice

set_option exponentiation.threshold 4096

variable {Q E nu : ℕ} {low : Bool}

/-- The search as a word. -/
theorem search_word (hb : WordBounds Q E nu) :
    LeanExe.repeatWhile 2000 0 (fun i => i < 2000 &&
        !found (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2)
          (startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) - i)
          ((UInt64.ofNat Q &&& 1) == 0)) (fun i => i + 1) =
      UInt64.ofNat (steps Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega)) := by
  have hnu1 : 1 ≤ nu := by have := hb.hnu; omega
  apply UInt64.toNat_inj.mp
  rw [search_spec hb]
  have := top_ge (low := low) hb.hQ hb.hE hnu1
  have := jstart_le hb
  have : top Q E nu low hb.hQ hb.hE hnu1 = jstart Q E nu - steps Q E nu low hb.hQ hb.hE hnu1 := rfl
  rw [ofNat_toNat _ (by have := hb.hnu2; omega)]

/-- The word of the top exponent. -/
theorem top_word (hb : WordBounds Q E nu) :
    ((startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) -
        UInt64.ofNat (steps Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega))).toNat : ℤ) =
      2 ^ 62 + top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) := by
  have hnu1 : 1 ≤ nu := by have := hb.hnu; omega
  have hst := startExp_spec hb
  have h1 := top_ge (low := low) hb.hQ hb.hE hnu1
  have h2 := jstart_le hb
  have ht : top Q E nu low hb.hQ hb.hE hnu1 = jstart Q E nu - steps Q E nu low hb.hQ hb.hE hnu1 := rfl
  have hs : steps Q E nu low hb.hQ hb.hE hnu1 ≤ 1800 := by have := hb.hnu2; omega
  rw [toNat_sub' _ _ (by rw [ofNat_toNat _ (by omega)]; omega), ofNat_toNat _ (by omega)]
  push_cast [show steps Q E nu low hb.hQ hb.hE hnu1 ≤ (startExp (4 * UInt64.ofNat Q + 2)
    (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2)).toNat by omega]
  omega

/-- The code's decimal: positive, below `2 ^ 62`, at the top exponent or one below, in the
interval, and the printers' choice. -/
theorem shortest_spec (hb : WordBounds Q E nu) (hcan : E = 1 ∨ 16 ≤ Q) :
    0 < (shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).1.toNat ∧
      (shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).1.toNat < 2 ^ 62 ∧
      top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) - 1 ≤
        ((shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).2.toNat : ℤ) - 2 ^ 62 ∧
      ((shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).2.toNat : ℤ) - 2 ^ 62 ≤
        top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) ∧
      Inside (cl Q) (lo Q E nu low) (hi Q E nu)
        (dv (shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).1.toNat
          (((shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).2.toNat : ℤ) - 2 ^ 62)) ∧
      Choice (cl Q) (lo Q E nu low) (hi Q E nu) (vv Q E nu)
        (top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega))
        (shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).1.toNat
        (((shortest (UInt64.ofNat Q) (UInt64.ofNat E) (UInt64.ofNat nu) low).2.toNat : ℤ) - 2 ^ 62) := by
  have hnu1 : 1 ≤ nu := by have := hb.hnu; omega
  have hnu2 := hb.hnu2
  set T := top Q E nu low hb.hQ hb.hE hnu1 with hT
  have hTw := top_word (low := low) hb
  have hT1 := top_ge (low := low) hb.hQ hb.hE hnu1
  have hT2 := top_lt_start (low := low) hb.hQ hb.hE hnu1
  have hT3 := jstart_le hb
  have hTop := top_top (low := low) hb.hQ hb.hE hnu1
  have hlo := lo_pos (Q := Q) (E := E) (nu := nu) (low := low) hb.hQ
  have hratio := hi_le (Q := Q) (E := E) (nu := nu) (low := low) hb.hQ
  have hvpos : 0 ≤ vv Q E nu := le_of_lt (lt_trans hlo (lo_lt_vv hb.hQ))
  unfold shortest
  dsimp only
  rw [search_word hb]
  set Jw := startExp (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) -
    UInt64.ofNat (steps Q E nu low hb.hQ hb.hE hnu1) with hJw
  have hJn : (Jw.toNat : ℤ) - 2 ^ 62 = T := by rw [hTw]; ring
  have hJ1 : 2 ^ 62 - 2 ^ 19 ≤ Jw.toNat := by omega
  have hJ2 : Jw.toNat ≤ 2 ^ 62 + 2 ^ 19 := by omega
  -- the run at `J`
  obtain ⟨hins, hR2⟩ := range_inside (low := low) hb Jw hJ1 hJ2 (by rw [hJn]; omega)
  obtain ⟨hv1, hv2, hv3, hv4⟩ := quot_half (low := low) hb Jw hJ1 hJ2 (by rw [hJn]; omega)
  rw [hJn] at hins hv1 hv2 hv3
  generalize range (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2)
    (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) Jw
    ((UInt64.ofNat Q &&& 1) == 0) = R at hins hR2 ⊢
  generalize quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) Jw = V
    at hv1 hv2 hv3 hv4 ⊢
  have hrun : R.1.toNat < R.2.toNat := by
    obtain ⟨m, hm⟩ := ex_top (low := low) hb.hQ hb.hE hnu1
    have := (hins m).mp hm
    omega
  have hnear := nearest_spec (vv Q E nu / 10 ^ T) V.1 V.2 (by omega) hv1 hv2 hv3
  have hnear1 : (nearest V.1 V.2).toNat < 2 ^ 63 := by
    unfold nearest
    have hh : (V.1 >>> 1).toNat = V.1.toNat / 2 := by
      rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]
    split_ifs
    · rw [hh]; omega
    · rw [toNat_add' _ _ (by rw [hh]; simp; omega), hh]; simp; omega
    · rw [hh]; omega
    · rw [toNat_add' _ _ (by rw [hh]; simp; omega), hh]; simp; omega
  obtain ⟨c1, c2, c3⟩ := clamp_spec (vv Q E nu / 10 ^ T) (div_nonneg hvpos (zpow_pos (by norm_num) T).le)
    (nearest V.1 V.2) R.1 R.2 hnear hrun hnear1
  generalize clamp (nearest V.1 V.2) R.1 R.2 = M at c1 c2 c3 ⊢
  have hMin : Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv M.toNat T) := (hins M.toNat).mpr ⟨c1, c2⟩
  have hMpos : 0 < M.toNat := by
    by_contra h
    have h0 : M.toNat = 0 := by omega
    rw [h0] at hMin
    have := hMin.lo_le; unfold dv at this; simp at this; linarith
  -- `Near` at `J` for the multiplier `M`
  have hnearJ : ∀ m : ℕ, Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m T) →
      Near (dv M.toNat T) (dv m T) (vv Q E nu) M.toNat := by
    intro m hm
    have := (hins m).mp hm
    exact near_scaled T (vv Q E nu) M.toNat m (c3 m this.1 this.2)
  have hleJ : ∀ m : ℕ, Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m T) →
      |dv M.toNat T - vv Q E nu| ≤ |dv m T - vv Q E nu| := by
    intro m hm
    rcases hnearJ m hm with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  -- the result `(M, J)`
  have hcaseA : (∀ m : ℕ, m ≤ 9 → Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m (T - 1)) →
      |dv M.toNat T - vv Q E nu| < |dv m (T - 1) - vv Q E nu|) →
      (0 < (M, Jw).1.toNat ∧ (M, Jw).1.toNat < 2 ^ 62 ∧ T - 1 ≤ ((M, Jw).2.toNat : ℤ) - 2 ^ 62 ∧
        ((M, Jw).2.toNat : ℤ) - 2 ^ 62 ≤ T ∧
        Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv (M, Jw).1.toNat (((M, Jw).2.toNat : ℤ) - 2 ^ 62)) ∧
        Choice (cl Q) (lo Q E nu low) (hi Q E nu) (vv Q E nu) T (M, Jw).1.toNat
          (((M, Jw).2.toNat : ℤ) - 2 ^ 62)) := by
    intro hfar
    dsimp only
    rw [hJn]
    exact ⟨hMpos, by omega, by omega, le_rfl, hMin, Or.inl ⟨rfl, hnearJ, hfar⟩⟩
  by_cases hM10 : M < 10
  · rw [ite_eq_left hM10]
    have hM9 : M.toNat ≤ 9 := by have := UInt64.lt_iff_toNat_lt.mp hM10; simp at this; omega
    -- the run at `J - 1`
    have hJw1 : ((Jw - 1).toNat : ℤ) - 2 ^ 62 = T - 1 := by
      rw [toNat_sub' _ _ (by simp; omega)]; simp; omega
    have hK1 : 2 ^ 62 - 2 ^ 19 ≤ (Jw - 1).toNat := by omega
    have hK2 : (Jw - 1).toNat ≤ 2 ^ 62 + 2 ^ 19 := by omega
    obtain ⟨hins', hR2'⟩ := range_inside (low := low) hb (Jw - 1) hK1 hK2 (by rw [hJw1])
    obtain ⟨hw1, hw2, hw3, hw4⟩ := quot_half (low := low) hb (Jw - 1) hK1 hK2 (by rw [hJw1])
    rw [hJw1] at hins' hw1 hw2 hw3
    generalize range (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2)
      (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) (Jw - 1)
      ((UInt64.ofNat Q &&& 1) == 0) = R' at hins' hR2' ⊢
    have hmin : (min R'.2 10).toNat = min R'.2.toNat 10 := by rw [UInt64.toNat_min]; rfl
    -- the one-digit multiples at `J - 1`
    have hins1 : ∀ m : ℕ, (m ≤ 9 ∧ Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m (T - 1))) ↔
        R'.1.toNat ≤ m ∧ m < (min R'.2 10).toNat := by
      intro m
      rw [hmin, hins' m]
      omega
    by_cases hc : R'.1 < min R'.2 10
    · rw [ite_eq_left hc]
      have hrun' : R'.1.toNat < (min R'.2 10).toNat := UInt64.lt_iff_toNat_lt.mp hc
      generalize quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) (Jw - 1) = V'
        at hw1 hw2 hw3 hw4 ⊢
      have hnear' := nearest_spec (vv Q E nu / 10 ^ (T - 1)) V'.1 V'.2 (by omega) hw1 hw2 hw3
      have hnear1' : (nearest V'.1 V'.2).toNat < 2 ^ 63 := by
        unfold nearest
        have hh : (V'.1 >>> 1).toNat = V'.1.toNat / 2 := by
          rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
            Nat.shiftRight_eq_div_pow]
        split_ifs
        · rw [hh]; omega
        · rw [toNat_add' _ _ (by rw [hh]; simp; omega), hh]; simp; omega
        · rw [hh]; omega
        · rw [toNat_add' _ _ (by rw [hh]; simp; omega), hh]; simp; omega
      obtain ⟨d1, d2, d3⟩ := clamp_spec (vv Q E nu / 10 ^ (T - 1))
        (div_nonneg hvpos (zpow_pos (by norm_num) _).le) (nearest V'.1 V'.2) R'.1 (min R'.2 10)
        hnear' hrun' hnear1'
      generalize clamp (nearest V'.1 V'.2) R'.1 (min R'.2 10) = M' at d1 d2 d3 ⊢
      have hM'9 : M'.toNat ≤ 9 := by rw [hmin] at d2; omega
      have hM'in : Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv M'.toNat (T - 1)) :=
        ((hins1 M'.toNat).mpr ⟨d1, d2⟩).2
      have hM'pos : 0 < M'.toNat := by
        by_contra h
        have h0 : M'.toNat = 0 := by omega
        rw [h0] at hM'in
        have := hM'in.lo_le; unfold dv at this; simp at this; linarith
      have hy' : vv Q E nu / 10 ^ (T - 1) = 10 * (vv Q E nu / 10 ^ T) := by
        have : (10 : ℝ) ^ T = 10 * 10 ^ (T - 1) := by
          rw [← zpow_one_add₀ (show (10 : ℝ) ≠ 0 by norm_num)]; congr 1; ring
        rw [this]; field_simp
      have hdvM : dv (10 * M.toNat) (T - 1) = dv M.toNat T := by rw [dv_ten, sub_add_cancel]
      have h10M : ((10 * M.toNat : ℕ) : ℝ) = 10 * (M.toNat : ℝ) := by push_cast; ring
      have hMlt : (M'.toNat : ℝ) < 10 * M.toNat := by
        have : (M'.toNat : ℝ) ≤ 9 := by exact_mod_cast hM'9
        have : (1 : ℝ) ≤ M.toNat := by exact_mod_cast hMpos
        linarith
      have hsum : (V'.1 < M' + 10 * M) ↔ V'.1.toNat < M'.toNat + 10 * M.toNat := by
        rw [UInt64.lt_iff_toNat_lt, toNat_add' _ _ (by rw [toNat_mul' _ _ (by simp; omega)]; simp; omega),
          toNat_mul' _ _ (by simp; omega)]
        simp
      by_cases hcmp : V'.1 < M' + 10 * M
      · rw [ite_eq_left hcmp]
        have hlt := hsum.mp hcmp
        have h2y : 2 * (vv Q E nu / 10 ^ (T - 1)) < (M'.toNat : ℝ) + 10 * M.toNat := by
          have : (V'.1.toNat : ℝ) + 1 ≤ (M'.toNat : ℝ) + 10 * M.toNat := by exact_mod_cast hlt
          linarith
        have hfar : |dv M'.toNat (T - 1) - vv Q E nu| < |dv M.toNat T - vv Q E nu| := by
          rw [← hdvM, abs_dv, abs_dv, h10M]
          exact mul_lt_mul_of_pos_right (abs_lt_of_two _ _ _ hMlt h2y) (zpow_pos (by norm_num) _)
        dsimp only
        rw [hJw1]
        refine ⟨hM'pos, by omega, le_rfl, by omega, hM'in, Or.inr ⟨rfl, hM'9, ?_, ?_⟩⟩
        · intro m hm
          exact lt_of_lt_of_le hfar (hleJ m hm)
        · intro m hm9 hm
          have := (hins1 m).mp ⟨hm9, hm⟩
          exact near_scaled (T - 1) (vv Q E nu) M'.toNat m (d3 m this.1 this.2)
      · rw [ite_eq_right hcmp]
        apply hcaseA
        intro m hm9 hm
        have hge := (not_lt.mp (fun h => hcmp (hsum.mpr h)))
        have h2y : (M'.toNat : ℝ) + 10 * M.toNat ≤ 2 * (vv Q E nu / 10 ^ (T - 1)) := by
          have : ((M'.toNat + 10 * M.toNat : ℕ) : ℝ) ≤ (V'.1.toNat : ℝ) := by exact_mod_cast hge
          push_cast at this; linarith
        have hle1 : |dv M.toNat T - vv Q E nu| ≤ |dv M'.toNat (T - 1) - vv Q E nu| := by
          rw [← hdvM, abs_dv, abs_dv, h10M]
          exact mul_le_mul_of_nonneg_right (abs_le_of_two _ _ _ hMlt h2y) (zpow_pos (by norm_num) _).le
        have hle2 : |dv M'.toNat (T - 1) - vv Q E nu| ≤ |dv m (T - 1) - vv Q E nu| := by
          have := (hins1 m).mp ⟨hm9, hm⟩
          rcases near_scaled (T - 1) (vv Q E nu) M'.toNat m (d3 m this.1 this.2) with h | ⟨h, _⟩
          · exact h.le
          · exact h.le
        rcases lt_or_eq_of_le (le_trans hle1 hle2) with h | h
        · exact h
        · exact absurd h (no_tie hb hcan T M.toNat m hMpos hM9 hm9 hMin hm)
    · rw [ite_eq_right hc]
      apply hcaseA
      intro m hm9 hm
      exfalso
      have := (hins1 m).mp ⟨hm9, hm⟩
      exact hc (UInt64.lt_iff_toNat_lt.mpr (by omega))
  · rw [ite_eq_right hM10]
    apply hcaseA
    intro m hm9 hm
    exfalso
    have hM10' : 10 ≤ M.toNat := by
      have := UInt64.lt_iff_toNat_lt.not.mp hM10; simp at this; omega
    have hm0 : 0 < m := by
      by_contra h
      have h0 : m = 0 := by omega
      rw [h0] at hm
      have := hm.lo_le; unfold dv at this; simp at this; linarith
    rcases more_digits T hTop hlo hratio M.toNat hMpos hMin m (T - 1) le_rfl hm with h | ⟨h, _⟩
    · have h1 : nd m ≤ 1 := nd_le m 1 (by omega) (by omega)
      have h2 := nd_pos M.toNat (by omega)
      omega
    · have h2 : 2 ≤ nd M.toNat := nd_ge M.toNat 1 (by omega)
      omega

#print axioms shortest_spec

end Verified.Examples.PrintFloatShortest
