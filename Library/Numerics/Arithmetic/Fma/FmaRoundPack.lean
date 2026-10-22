import Library.Numerics.Arithmetic.Fma.FmaRound

/-!
The cases of `Fma.roundPack s w h l` for `N = h · 2 ^ 64 + l` with highest set bit `M`, and the
theorem `roundPack_spec` that collects them.  A normal result, `w + M ≥ 1378`, is rounded at bit
`M - 52` (`normal_right`), is exact for `M = 52` (`normal_exact`), and is shifted left for `M < 52`
(`normal_left`).  A subnormal result is rounded at bit `1326 - w` (`sub_right`), is a zero when that
bit lies above bit 127 (`sub_far`), is exact for `w = 1326` (`sub_exact`), and is shifted left for
`w > 1326` (`sub_left`).
-/

namespace Library.Numerics.Arithmetic.Fma.FmaRoundPack
open Verified.Examples FmaWords FmaGrid FmaRound

set_option exponentiation.threshold 4096

/-- The conclusion of every case: the packed word of a rounding of `N · 2 ^ W`. -/
def Packs (s e q : UInt64) (N M W : ℕ) : Prop :=
  ∃ E Q, assemble s e q = packWord s E Q ∧ RoundsTo (N * 2 ^ W) E Q ∧ W + M ≤ E + 1377

theorem packs_of (s e q : UInt64) (N M W E Q : ℕ) (he : e.toNat = E) (hq : q.toNat = Q)
    (hR : RoundsTo (N * 2 ^ W) E Q) (hb : W + M ≤ E + 1377) : Packs s e q N M W :=
  ⟨E, Q, assemble_round s e q _ E Q he hq hR, hR, hb⟩

theorem normal_right (s w m h l : UInt64) (N M W : ℕ) (hN : pair h l = N) (hM : m.toNat = M)
    (m1 : 2 ^ M ≤ N) (m2 : N < 2 ^ (M + 1)) (hM126 : M ≤ 126)
    (hwm : (w + m).toNat = W + M) (hA : 1378 ≤ W + M) (hB : 52 < M) :
    Packs s (w + m - 1377) (sig h l false (m - 52)) N M W := by
  have he : (w + m - 1377).toNat = W + M - 1377 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 1377).mpr (by rw [hwm]; exact le_trans (by decide) hA)),
      hwm]
    rfl
  have hr : (m - 52).toNat = M - 52 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 52).mpr (by rw [hM]; exact hB.le)), hM]
    rfl
  have hsmall : N / 2 ^ (M - 52) < 2 ^ 63 := by
    have := div_small N M (M - 52) m2 (by omega)
    rw [show M + 1 - (M - 52) = 53 by omega] at this
    exact lt_trans this (by norm_num)
  obtain ⟨hu, hd⟩ := sig_round h l (m - 52) (by rw [hr]; omega) (by rw [hr]; omega)
    (by rw [hr, hN]; exact hsmall)
  rw [hr, hN] at hu hd
  obtain ⟨r1, r2, r3⟩ := round_right N (M - 52) _ (by omega) hu hd
  obtain ⟨bhi, blo⟩ := binade_normal N M W m1 m2 hA
  exact packs_of s _ _ N M W (W + M - 1377) _ he rfl
    (roundsTo_of N W _ _ (M - 52) (by omega) (by omega) bhi (Or.inr blo) r1 r2 r3) (by omega)

theorem normal_exact (s w m h l : UInt64) (N M W : ℕ) (hN : pair h l = N) (hM : m.toNat = M)
    (m1 : 2 ^ M ≤ N) (m2 : N < 2 ^ (M + 1))
    (hwm : (w + m).toNat = W + M) (hA : 1378 ≤ W + M) (hB : M = 52) :
    Packs s (w + m - 1377) (sig h l false (m - 52)) N M W := by
  have he : (w + m - 1377).toNat = W + M - 1377 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 1377).mpr (by rw [hwm]; exact le_trans (by decide) hA)),
      hwm]
    rfl
  have hr0 : m - 52 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 52).mpr (by rw [hM, hB]; rfl)), hM, hB]
    rfl
  rw [hr0]
  have hN53 : N < 2 ^ 63 := by
    rw [hB] at m2; exact lt_trans m2 (by norm_num)
  have hq := sig_exact h l (by rw [hN]; exact hN53)
  rw [hN] at hq
  obtain ⟨bhi, blo⟩ := binade_normal N M W m1 m2 hA
  refine packs_of s _ _ N M W (W + M - 1377) N he hq ?_ (by omega)
  apply roundsTo_exact _ _ _ (by omega) _ bhi (Or.inr blo)
  unfold spacing
  rw [show W + M - 1377 + 1325 = W by omega]

theorem normal_left (s w m h l : UInt64) (N M W : ℕ) (hN : pair h l = N) (hM : m.toNat = M)
    (m1 : 2 ^ M ≤ N) (m2 : N < 2 ^ (M + 1))
    (hwm : (w + m).toNat = W + M) (hA : 1378 ≤ W + M) (hB : M < 52) :
    Packs s (w + m - 1377) (sig h l true (52 - m)) N M W := by
  have he : (w + m - 1377).toNat = W + M - 1377 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 1377).mpr (by rw [hwm]; exact le_trans (by decide) hA)),
      hwm]
    rfl
  have hr : (52 - m).toNat = 52 - M := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ m).mpr (by rw [hM]; exact hB.le)), hM]
    rfl
  have hfit : N * 2 ^ (52 - M) < 2 ^ 53 := by
    calc N * 2 ^ (52 - M) < 2 ^ (M + 1) * 2 ^ (52 - M) :=
          Nat.mul_lt_mul_of_pos_right m2 (by positivity)
      _ = 2 ^ 53 := by rw [← pow_add, show M + 1 + (52 - M) = 53 by omega]
  have hq := sig_left h l (52 - m) (by rw [hr]; omega)
    (by rw [hr, hN]; exact lt_trans hfit (by norm_num))
  rw [hr, hN] at hq
  obtain ⟨bhi, blo⟩ := binade_normal N M W m1 m2 hA
  refine packs_of s _ _ N M W (W + M - 1377) _ he hq ?_ (by omega)
  apply roundsTo_exact _ _ _ (by omega) _ bhi (Or.inr blo)
  unfold spacing
  rw [mul_assoc, ← pow_add, show 52 - M + (W + M - 1377 + 1325) = W by omega]

theorem sub_far (s w h l : UInt64) (N M W : ℕ) (hN : pair h l = N)
    (hW : w.toNat = W) (m2 : N < 2 ^ (M + 1)) (hN127 : N < 2 ^ 127) (hA : W + M < 1378)
    (hB : W ≤ 1326) (hfar : 128 ≤ 1326 - W) :
    Packs s 1 (sig h l false (1326 - w)) N M W := by
  have hr : (1326 - w).toNat = 1326 - W := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ w).mpr (by rw [hW]; exact hB)), hW]
    rfl
  rw [sig_far h l _ (by rw [hr]; exact hfar)]
  have bhi := binade_sub N M W m2 hA
  refine packs_of s _ _ N M W 1 0 rfl rfl ?_ (by omega)
  apply roundsTo_of N W 1 0 (1326 - W) le_rfl (by omega) bhi (Or.inl rfl) _ _ (by simp)
  · have h1 : 2 ^ 128 ≤ 2 ^ (1326 - W) := Nat.pow_le_pow_right (by norm_num) hfar
    have h2 : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  · simp

theorem sub_exact (s w h l : UInt64) (N M W : ℕ) (hN : pair h l = N)
    (hW : w.toNat = W) (m2 : N < 2 ^ (M + 1)) (hA : W + M < 1378) (hB : W = 1326) :
    Packs s 1 (sig h l false (1326 - w)) N M W := by
  have hr0 : 1326 - w = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ w).mpr (by rw [hW, hB]; rfl)), hW, hB]
    rfl
  rw [hr0]
  have hN63 : N < 2 ^ 63 := by
    have : 2 ^ (M + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq := sig_exact h l (by rw [hN]; exact hN63)
  rw [hN] at hq
  have bhi := binade_sub N M W m2 hA
  refine packs_of s _ _ N M W 1 N rfl hq ?_ (by omega)
  apply roundsTo_exact _ _ _ le_rfl _ bhi (Or.inl rfl)
  unfold spacing
  rw [hB]

theorem sub_right (s w h l : UInt64) (N M W : ℕ) (hN : pair h l = N)
    (hW : w.toNat = W) (m2 : N < 2 ^ (M + 1)) (hA : W + M < 1378) (hB : W < 1326)
    (hnear : 1326 - W < 128) :
    Packs s 1 (sig h l false (1326 - w)) N M W := by
  have hr : (1326 - w).toNat = 1326 - W := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ w).mpr (by rw [hW]; exact hB.le)), hW]
    rfl
  have hsmall : N / 2 ^ (1326 - W) < 2 ^ 63 := by
    by_cases hr' : 1326 - W ≤ M + 1
    · have h1 := div_small N M (1326 - W) m2 hr'
      have h2 : 2 ^ (M + 1 - (1326 - W)) ≤ 2 ^ 63 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact lt_of_lt_of_le h1 h2
    · have h1 : 2 ^ (M + 1) ≤ 2 ^ (1326 - W) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le m2 h1)]
      positivity
  obtain ⟨hu, hd⟩ := sig_round h l (1326 - w) (by rw [hr]; omega) (by rw [hr]; exact hnear)
    (by rw [hr, hN]; exact hsmall)
  rw [hr, hN] at hu hd
  obtain ⟨r1, r2, r3⟩ := round_right N (1326 - W) _ (by omega) hu hd
  have bhi := binade_sub N M W m2 hA
  exact packs_of s _ _ N M W 1 _ rfl rfl
    (roundsTo_of N W 1 _ (1326 - W) le_rfl (by omega) bhi (Or.inl rfl) r1 r2 r3) (by omega)

theorem sub_left (s w h l : UInt64) (N M W : ℕ) (hN : pair h l = N)
    (hW : w.toNat = W) (m2 : N < 2 ^ (M + 1)) (hA : W + M < 1378) (hB : 1326 < W) :
    Packs s 1 (sig h l true (w - 1326)) N M W := by
  have hr : (w - 1326).toNat = W - 1326 := by
    rw [UInt64.toNat_sub_of_le _ _ ((lit_le _ 1326).mpr (by rw [hW]; exact hB.le)), hW]
    rfl
  have hfit : N * 2 ^ (W - 1326) < 2 ^ 64 := by
    calc N * 2 ^ (W - 1326) < 2 ^ (M + 1) * 2 ^ (W - 1326) :=
          Nat.mul_lt_mul_of_pos_right m2 (by positivity)
      _ = 2 ^ (M + 1 + (W - 1326)) := (pow_add 2 (M + 1) (W - 1326)).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := sig_left h l (w - 1326) (by rw [hr]; omega) (by rw [hr, hN]; exact hfit)
  rw [hr, hN] at hq
  have bhi := binade_sub N M W m2 hA
  refine packs_of s _ _ N M W 1 _ rfl hq ?_ (by omega)
  apply roundsTo_exact _ _ _ le_rfl _ bhi (Or.inl rfl)
  unfold spacing
  rw [mul_assoc, ← pow_add, show W - 1326 + (1 + 1325) = W by omega]

/-- `Fma.roundPack` rounds `N · 2 ^ (w - 2400)` as `RoundsTo` describes. -/
theorem roundPack_spec (s w h l : UInt64) (hN0 : pair h l ≠ 0) (hN127 : pair h l < 2 ^ 127)
    (hw : w.toNat < 2 ^ 32) :
    ∃ E Q, Fma.roundPack s w h l = packWord s E Q ∧ RoundsTo (pair h l * 2 ^ w.toNat) E Q ∧
      w.toNat + (Fma.msb128 h l).toNat ≤ E + 1377 := by
  obtain ⟨m128, m1, m2⟩ := msb128_spec h l hN0
  rw [roundPack_eq]
  generalize Fma.msb128 h l = m at m128 m1 m2 ⊢
  generalize hN : pair h l = N at hN0 hN127 m1 m2 ⊢
  generalize hM : m.toNat = M at m128 m1 m2 ⊢
  generalize hW : w.toNat = W at hw ⊢
  have hM126 : M ≤ 126 := by
    by_contra hc
    have : 2 ^ 127 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hwm : (w + m).toNat = W + M := by
    rw [UInt64.toNat_add, hW, hM]
    exact Nat.mod_eq_of_lt (by
      have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
      have : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
      omega)
  suffices hP : Packs s (plan w m).2.2 (sig h l (plan w m).1 (plan w m).2.1) N M W from hP
  by_cases hA : 1378 ≤ W + M
  · have hc1 : w + m ≥ 1378 := (lit_le _ 1378).mpr (by rw [hwm]; exact hA)
    by_cases hB : 52 ≤ M
    · have hc2 : m ≥ 52 := (lit_le m 52).mpr (by rw [hM]; exact hB)
      have hp : plan w m = (false, m - 52, w + m - 1377) := by
        unfold plan; rw [ite_eq_left hc1, ite_eq_left hc2]
      rw [hp]
      rcases lt_or_eq_of_le hB with hB' | hB'
      · exact normal_right s w m h l N M W hN hM m1 m2 hM126 hwm hA hB'
      · exact normal_exact s w m h l N M W hN hM m1 m2 hwm hA hB'.symm
    · have hc2 : ¬ (m ≥ 52) := fun h' => hB (by have := (lit_le m 52).mp h'; rw [hM] at this; exact this)
      have hp : plan w m = (true, 52 - m, w + m - 1377) := by
        unfold plan; rw [ite_eq_left hc1, ite_eq_right hc2]
      rw [hp]
      exact normal_left s w m h l N M W hN hM m1 m2 hwm hA (by omega)
  · have hc1 : ¬ (w + m ≥ 1378) := fun h' => hA (by
      have := (lit_le _ 1378).mp h'; rw [hwm] at this; exact this)
    by_cases hB : W ≤ 1326
    · have hc2 : w ≤ 1326 := (lit_le 1326 w).mpr (by rw [hW]; exact hB)
      have hp : plan w m = (false, 1326 - w, 1) := by
        unfold plan; rw [ite_eq_right hc1, ite_eq_left hc2]
      rw [hp]
      by_cases hfar : 128 ≤ 1326 - W
      · exact sub_far s w h l N M W hN hW m2 hN127 (by omega) hB hfar
      · rcases lt_or_eq_of_le hB with hB' | hB'
        · exact sub_right s w h l N M W hN hW m2 (by omega) hB' (by omega)
        · exact sub_exact s w h l N M W hN hW m2 (by omega) hB'
    · have hc2 : ¬ (w ≤ 1326) := fun h' => hB (by
        have := (lit_le 1326 w).mp h'; rw [hW] at this; exact this)
      have hp : plan w m = (true, w - 1326, 1) := by
        unfold plan; rw [ite_eq_right hc1, ite_eq_right hc2]
      rw [hp]
      exact sub_left s w h l N M W hN hW m2 (by omega) (by omega)

#print axioms normal_right
#print axioms sub_right
#print axioms roundPack_spec

end Library.Numerics.Arithmetic.Fma.FmaRoundPack
