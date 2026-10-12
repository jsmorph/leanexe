import LeanExe.ProofKit.GammaSubnormalA
import LeanExe.ProofKit.GammaSubnormalB
import LeanExe.ProofKit.GammaSubnormalC

/-!
Every double in `(-184, -170)` is `-m/2 ^ 45` for an integer `m`, and `|Γ|` there stays `2 ^ -48`
relative away from `2 ^ -1022` (`subnormal_gap`), which keeps the choice between the subnormal and
the normal branch of `tgamma`'s reflection path correct.  On each interval `(-n - 1, -n)`, `lgamma`
is convex (`GammaConvex.convexOn_lgamma_neg`), so bounds at the two doubles next to each crossing
of the level, and at the doubles next to the poles where `|Γ|` stays below it, cover every double
of the interval.  The closest double lies at `-170.584302134743268` (`0xc06552b29a63f692`), where
`|Γ|` is `2 ^ -1022 (1 + 33.97 · 2 ^ -53)` in 80-digit arithmetic, and the Taylor model of
`pt_170_4` there has an error below `2 ^ -68` against a margin of `2 ^ -52`.
-/

namespace LeanExe.ProofKit.GammaSubnormal

open Real Set TaylorModel GammaBasic GammaModels GammaFits GammaReflect GammaConvex GammaThresholds
    GammaSubnormalBase

theorem gap_170 : ∀ m : ℕ, 5981343255101440 < m → m < 6016527627190272 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 170 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 170 hx1 hx2
  have f2 := point_below 170 _ _ _ _ _ 6014907144956298 GammaSubnormalA.pt_170_2 (by norm_num)
  have f3 := point_below 170 _ _ _ _ _ 6001901558822547 GammaSubnormalA.pt_170_3 (by norm_num)
  have f1 := point_above 170 _ _ _ _ _ 6014907144956299 GammaSubnormalA.pt_170_1 (by norm_num)
  have f4 := point_above 170 _ _ _ _ _ 6001901558822546 GammaSubnormalA.pt_170_4 (by norm_num)
  rcases le_or_gt 6014907144956299 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 170 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6001901558822546 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 170 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 170 (by norm_num) (neg_div_le (by omega : m ≤ 6014907144956298))
    (neg_div_le (by omega : 6001901558822547 ≤ m)) (by norm_num) f2 f3))

theorem gap_171 : ∀ m : ℕ, 6016527627190272 < m → m < 6051711999279104 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 171 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 171 hx1 hx2
  have f2 := point_below 171 _ _ _ _ _ 6051704583268981 GammaSubnormalA.pt_171_2 (by norm_num)
  have f3 := point_below 171 _ _ _ _ _ 6017616040599346 GammaSubnormalA.pt_171_3 (by norm_num)
  have f1 := point_above 171 _ _ _ _ _ 6051704583268982 GammaSubnormalA.pt_171_1 (by norm_num)
  have f4 := point_above 171 _ _ _ _ _ 6017616040599345 GammaSubnormalA.pt_171_4 (by norm_num)
  rcases le_or_gt 6051704583268982 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 171 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6017616040599345 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 171 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 171 (by norm_num) (neg_div_le (by omega : m ≤ 6051704583268981))
    (neg_div_le (by omega : 6017616040599346 ≤ m)) (by norm_num) f2 f3))

theorem gap_172 : ∀ m : ℕ, 6051711999279104 < m → m < 6086896371367936 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 172 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 172 hx1 hx2
  have f2 := point_below 172 _ _ _ _ _ 6086896328547070 GammaSubnormalA.pt_172_2 (by norm_num)
  have f3 := point_below 172 _ _ _ _ _ 6051719399222768 GammaSubnormalA.pt_172_3 (by norm_num)
  have f1 := point_above 172 _ _ _ _ _ 6086896328547071 GammaSubnormalA.pt_172_1 (by norm_num)
  have f4 := point_above 172 _ _ _ _ _ 6051719399222767 GammaSubnormalA.pt_172_4 (by norm_num)
  rcases le_or_gt 6086896328547071 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 172 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6051719399222767 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 172 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 172 (by norm_num) (neg_div_le (by omega : m ≤ 6086896328547070))
    (neg_div_le (by omega : 6051719399222768 ≤ m)) (by norm_num) f2 f3))

theorem gap_173 : ∀ m : ℕ, 6086896371367936 < m → m < 6122080743456768 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 173 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 173 hx1 hx2
  have f2 := point_below 173 _ _ _ _ _ 6122080743210672 GammaSubnormalB.pt_173_2 (by norm_num)
  have f3 := point_below 173 _ _ _ _ _ 6086896414188265 GammaSubnormalB.pt_173_3 (by norm_num)
  have f1 := point_above 173 _ _ _ _ _ 6122080743210673 GammaSubnormalB.pt_173_1 (by norm_num)
  have f4 := point_above 173 _ _ _ _ _ 6086896414188264 GammaSubnormalB.pt_173_4 (by norm_num)
  rcases le_or_gt 6122080743210673 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 173 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6086896414188264 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 173 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 173 (by norm_num) (neg_div_le (by omega : m ≤ 6122080743210672))
    (neg_div_le (by omega : 6086896414188265 ≤ m)) (by norm_num) f2 f3))

theorem gap_174 : ∀ m : ℕ, 6122080743456768 < m → m < 6157265115545600 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 174 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 174 hx1 hx2
  have f2 := point_below 174 _ _ _ _ _ 6157265115544193 GammaSubnormalB.pt_174_2 (by norm_num)
  have f3 := point_below 174 _ _ _ _ _ 6122080743702864 GammaSubnormalB.pt_174_3 (by norm_num)
  have f1 := point_above 174 _ _ _ _ _ 6157265115544194 GammaSubnormalB.pt_174_1 (by norm_num)
  have f4 := point_above 174 _ _ _ _ _ 6122080743702863 GammaSubnormalB.pt_174_4 (by norm_num)
  rcases le_or_gt 6157265115544194 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 174 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6122080743702863 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 174 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 174 (by norm_num) (neg_div_le (by omega : m ≤ 6157265115544193))
    (neg_div_le (by omega : 6122080743702864 ≤ m)) (by norm_num) f2 f3))

theorem gap_175 : ∀ m : ℕ, 6157265115545600 < m → m < 6192449487634432 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 175 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 175 hx1 hx2
  have f2 := point_below 175 _ _ _ _ _ 6192449487634424 GammaSubnormalB.pt_175_2 (by norm_num)
  have f3 := point_below 175 _ _ _ _ _ 6157265115547007 GammaSubnormalB.pt_175_3 (by norm_num)
  have f1 := point_above 175 _ _ _ _ _ 6192449487634425 GammaSubnormalB.pt_175_1 (by norm_num)
  have f4 := point_above 175 _ _ _ _ _ 6157265115547006 GammaSubnormalB.pt_175_4 (by norm_num)
  rcases le_or_gt 6192449487634425 m with hA | hA
  · exact Or.inr
      (gamma_above hne (left_above 175 hx1 (neg_div_le hA) (by norm_num) (by norm_num) f1 f2))
  rcases le_or_gt m 6157265115547006 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 175 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 175 (by norm_num) (neg_div_le (by omega : m ≤ 6192449487634424))
    (neg_div_le (by omega : 6157265115547007 ≤ m)) (by norm_num) f2 f3))

theorem gap_176 : ∀ m : ℕ, 6192449487634432 < m → m < 6227633859723264 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 176 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 176 hx1 hx2
  have f2 := point_below 176 _ _ _ _ _ 6227633859723263 GammaSubnormalC.pt_176_2 (by norm_num)
  have f3 := point_below 176 _ _ _ _ _ 6192449487634440 GammaSubnormalC.pt_176_3 (by norm_num)
  have f4 := point_above 176 _ _ _ _ _ 6192449487634439 GammaSubnormalC.pt_176_4 (by norm_num)
  rcases le_or_gt m 6192449487634439 with hB | hB
  · exact Or.inr
      (gamma_above hne (right_above 176 hx2 (neg_div_le hB) (by norm_num) (by norm_num) f3 f4))
  exact Or.inl
      (gamma_below hne (mid_below 176 (by norm_num) (neg_div_le (by omega : m ≤ 6227633859723263))
    (neg_div_le (by omega : 6192449487634440 ≤ m)) (by norm_num) f2 f3))

theorem gap_177 : ∀ m : ℕ, 6227633859723264 < m → m < 6262818231812096 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 177 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 177 hx1 hx2
  have f2 := point_below 177 _ _ _ _ _ 6262818231812095 GammaSubnormalC.pt_177_2 (by norm_num)
  have f3 := point_below 177 _ _ _ _ _ 6227633859723265 GammaSubnormalC.pt_177_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 177 (by norm_num) (neg_div_le (by omega : m ≤ 6262818231812095))
    (neg_div_le (by omega : 6227633859723265 ≤ m)) (by norm_num) f2 f3))

theorem gap_178 : ∀ m : ℕ, 6262818231812096 < m → m < 6298002603900928 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 178 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 178 hx1 hx2
  have f2 := point_below 178 _ _ _ _ _ 6298002603900927 GammaSubnormalC.pt_178_2 (by norm_num)
  have f3 := point_below 178 _ _ _ _ _ 6262818231812097 GammaSubnormalC.pt_178_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 178 (by norm_num) (neg_div_le (by omega : m ≤ 6298002603900927))
    (neg_div_le (by omega : 6262818231812097 ≤ m)) (by norm_num) f2 f3))

theorem gap_179 : ∀ m : ℕ, 6298002603900928 < m → m < 6333186975989760 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 179 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 179 hx1 hx2
  have f2 := point_below 179 _ _ _ _ _ 6333186975989759 GammaSubnormalC.pt_179_2 (by norm_num)
  have f3 := point_below 179 _ _ _ _ _ 6298002603900929 GammaSubnormalC.pt_179_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 179 (by norm_num) (neg_div_le (by omega : m ≤ 6333186975989759))
    (neg_div_le (by omega : 6298002603900929 ≤ m)) (by norm_num) f2 f3))

theorem gap_180 : ∀ m : ℕ, 6333186975989760 < m → m < 6368371348078592 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 180 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 180 hx1 hx2
  have f2 := point_below 180 _ _ _ _ _ 6368371348078591 GammaSubnormalC.pt_180_2 (by norm_num)
  have f3 := point_below 180 _ _ _ _ _ 6333186975989761 GammaSubnormalC.pt_180_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 180 (by norm_num) (neg_div_le (by omega : m ≤ 6368371348078591))
    (neg_div_le (by omega : 6333186975989761 ≤ m)) (by norm_num) f2 f3))

theorem gap_181 : ∀ m : ℕ, 6368371348078592 < m → m < 6403555720167424 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 181 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 181 hx1 hx2
  have f2 := point_below 181 _ _ _ _ _ 6403555720167423 GammaSubnormalC.pt_181_2 (by norm_num)
  have f3 := point_below 181 _ _ _ _ _ 6368371348078593 GammaSubnormalC.pt_181_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 181 (by norm_num) (neg_div_le (by omega : m ≤ 6403555720167423))
    (neg_div_le (by omega : 6368371348078593 ≤ m)) (by norm_num) f2 f3))

theorem gap_182 : ∀ m : ℕ, 6403555720167424 < m → m < 6438740092256256 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 182 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 182 hx1 hx2
  have f2 := point_below 182 _ _ _ _ _ 6438740092256255 GammaSubnormalC.pt_182_2 (by norm_num)
  have f3 := point_below 182 _ _ _ _ _ 6403555720167425 GammaSubnormalC.pt_182_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 182 (by norm_num) (neg_div_le (by omega : m ≤ 6438740092256255))
    (neg_div_le (by omega : 6403555720167425 ≤ m)) (by norm_num) f2 f3))

theorem gap_183 : ∀ m : ℕ, 6438740092256256 < m → m < 6473924464345088 → Gap
    (-(m : ℝ) / 35184372088832) := by
  intro m h1 h2
  obtain ⟨hx1, hx2⟩ := mem_interval 183 (m := m) (by omega) (by omega)
  have hne := gamma_ne_of_mem 183 hx1 hx2
  have f2 := point_below 183 _ _ _ _ _ 6473924464345087 GammaSubnormalC.pt_183_2 (by norm_num)
  have f3 := point_below 183 _ _ _ _ _ 6438740092256257 GammaSubnormalC.pt_183_3 (by norm_num)
  exact Or.inl
      (gamma_below hne (mid_below 183 (by norm_num) (neg_div_le (by omega : m ≤ 6473924464345087))
    (neg_div_le (by omega : 6438740092256257 ≤ m)) (by norm_num) f2 f3))

/-- `SubnormalGap`: `|Γ (-m/2 ^ 45)|` lies at most `2 ^ -1022 (1 - 2 ^ -48)` or at least
`2 ^ -1022 (1 + 2 ^ -48)` for `170 · 2 ^ 45 < m < 184 · 2 ^ 45`. -/
theorem subnormal_gap : ∀ m : ℕ, 170 * 2 ^ 45 < m → m < 184 * 2 ^ 45 →
    |Real.Gamma (-(m : ℝ) / 2 ^ 45)| ≤ 2 ^ (-1022 : ℤ) * (1 - 1 / 2 ^ 48) ∨
      2 ^ (-1022 : ℤ) * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma (-(m : ℝ) / 2 ^ 45)| := by
  intro m h1 h2
  rw [show (2 : ℝ) ^ 45 = 35184372088832 by norm_num]
  norm_num at h1 h2
  by_cases hk : m % 35184372088832 = 0
  · left
    obtain ⟨k, rfl⟩ : ∃ k, m = 35184372088832 * k :=
        ⟨m / 35184372088832, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)).symm⟩
    have e : -(((35184372088832 * k : ℕ)) : ℝ) / 35184372088832 = -(k : ℝ) := by
      push_cast
      ring
    rw [e, Real.Gamma_neg_nat_eq_zero, abs_zero]
    exact mul_nonneg (by positivity) (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n, n = m / 35184372088832 := ⟨_, rfl⟩
  have hn1 : 170 ≤ n := by omega
  have hn2 : n ≤ 183 := by omega
  interval_cases n
  · exact gap_170 m (by omega) (by omega)
  · exact gap_171 m (by omega) (by omega)
  · exact gap_172 m (by omega) (by omega)
  · exact gap_173 m (by omega) (by omega)
  · exact gap_174 m (by omega) (by omega)
  · exact gap_175 m (by omega) (by omega)
  · exact gap_176 m (by omega) (by omega)
  · exact gap_177 m (by omega) (by omega)
  · exact gap_178 m (by omega) (by omega)
  · exact gap_179 m (by omega) (by omega)
  · exact gap_180 m (by omega) (by omega)
  · exact gap_181 m (by omega) (by omega)
  · exact gap_182 m (by omega) (by omega)
  · exact gap_183 m (by omega) (by omega)

#print axioms subnormal_gap

end LeanExe.ProofKit.GammaSubnormal
