module

public import Library.Numerics.Bignum.Third.DivFix

@[expose] public section

/-!
Algorithm 1.8, RecursiveDivRem, in place: `rdiv_spec` states that `rdiv` divides the `n + m`
limbs at `ap` by the normalized `n` limbs at `bp`, for `m ≤ n`, with the quotient in `m` limbs at
`qp` and a top word, the remainder over the dividend's segment, and the `6 m + 9` words of scratch
from `sp`, by strong induction on `m`.

The proof follows Brent and Zimmermann's proof of Theorem 1.4.  With `k = ⌊m/2⌋`, `h = m - k`,
`B = B0 + β^k B1`, and `A = Alow + β^k Amid + β^(2k) A2`, the first call gives `A2 = Q1 B1 + R1`,
the first correction gives `X' = Amid + β^k R1 - Q1 B0 + j1 B` in `[0, B)` and the quotient
`Q1 - j1`, the second call gives `X' = Q0 B1 + R0`, and the second correction gives
`X2' = Alow + β^k R0 - Q0 B0 + j0 B` in `[0, B)` and `Q0 - j0`, so that
`A = ((Q1 - j1) β^k + (Q0 - j0)) B + X2'`.  The products are below `2 β^m` and `2 β^(2k)`, since a
quotient by a normalized divisor of `n'` limbs of a dividend of `n' + m'` limbs is below `2 β^m'`.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- A segment of value 0 holds zeros. -/
theorem segVal_eq_zero {W : Array UInt64} {p k : ℕ} (h : segVal W p k = 0) :
    ∀ i, i < k → W[p + i]! = 0 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    rw [segVal_succ] at h
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · exact ih (by omega) i hik
    · have hi' : i = k := by omega
      subst hi'
      have h1 : W[p + i]!.toNat * base ^ i = 0 := by omega
      have h2 : W[p + i]!.toNat = 0 := by
        rcases Nat.mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h (Nat.pos_iff_ne_zero.mp (pow_pos base_pos _))
      exact UInt64.toNat_inj.mp (by rw [h2]; rfl)

/-- The quotient by a normalized divisor of `n` limbs of a dividend below `β^(n + m)` is below
`2 β^m`. -/
theorem quot_lt_two {A B n m : ℕ} (hA : A < base ^ (n + m)) (hB : base ^ n ≤ 2 * B) :
    A / B < 2 * base ^ m := by
  have hBpos : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h] at hB; have := pow_pos base_pos n; omega
    · exact h
  rw [Nat.div_lt_iff_lt_mul hBpos]
  calc A < base ^ (n + m) := hA
    _ = base ^ m * base ^ n := by rw [pow_add]; ring
    _ ≤ base ^ m * (2 * B) := Nat.mul_le_mul_left _ hB
    _ = 2 * base ^ m * B := by ring

/-- A weaker frame: more scratch. -/
theorem DivPost.mono {W : Array UInt64} {ap bp qp sp n m S S' : ℕ} {r : UInt64 × Array UInt64}
    (h : DivPost W ap bp qp sp n m S r) (hS : S ≤ S') : DivPost W ap bp qp sp n m S' r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, fun p hp1 hp2 hp3 => h2 p hp1 hp2 (by omega), h3, h4, h5, h6, h7⟩

set_option maxHeartbeats 8000000 in
/-- Algorithm 1.8 divides the `n + m` limbs at `ap` by the normalized `n ≥ 2` limbs at `bp`, for
`m ≤ n`, the quotient below the divisor, the divisor below the dividend, and the dividend below
`6 m + 9` words of scratch. -/
theorem rdiv_spec (t T : UInt64) : ∀ (m : ℕ) (W : Array UInt64) (ap bp qp sp n mm : UInt64),
    mm.toNat = m → W.size < 2 ^ 62 → 2 ≤ n.toNat → m ≤ n.toNat →
    qp.toNat + m ≤ bp.toNat → bp.toNat + n.toNat ≤ ap.toNat →
    ap.toNat + n.toNat + m ≤ sp.toNat → sp.toNat + 6 * m + 9 ≤ W.size →
    SegDigits W ap.toNat (n.toNat + m) → SegDigits W bp.toNat n.toNat →
    base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat →
    DivPost W ap.toNat bp.toNat qp.toNat sp.toNat n.toNat m (6 * m + 9)
      (rdiv t T W ap bp qp sp n mm) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W ap bp qp sp n mm hm hW hn hmn hqb hba has hsz hda hdb hv1
  rw [rdiv]
  by_cases hc : mm < T ∨ mm < 3
  · rw [dif_pos hc]
    have := baseDiv_spec W ap bp qp n mm hW hn (by omega) hba (by omega) (by rw [hm]; exact hda)
      hdb hv1 sp.toNat
    rw [hm] at this
    exact this.mono (by omega)
  rw [dif_neg hc]
  have hm3 : 3 ≤ m := by
    simp only [not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat] at hc; omega
  -- the halves
  obtain ⟨N, hN⟩ : ∃ N, n.toNat = N := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = m / 2 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = m - K := ⟨_, rfl⟩
  rw [hN] at hn hmn hba has hda hdb hv1 ⊢
  have hK1 : 1 ≤ K := by omega
  have hKH : K ≤ H := by omega
  have hHm : H < m := by omega
  have hKm : K < m := by omega
  have hmK : m = K + H := by omega
  have hk : (mm / 2).toNat = K := by rw [UInt64.toNat_div, hm, hK]; rfl
  have hh : (mm - mm / 2).toNat = H := by rw [toNat_sub_le' (by rw [hk]; omega), hk, hm, hH]
  have hnk : (n - mm / 2).toNat = N - K := by rw [toNat_sub_le' (by rw [hk]; omega), hk, hN]
  have hap2 : (ap + 2 * (mm / 2)).toNat = ap.toNat + 2 * K := by
    have : (2 * (mm / 2)).toNat = 2 * K := by
      rw [toNat_mul_lt' (by rw [hk]; simp; omega), hk]; simp
    rw [toNat_add_lt (by rw [this]; omega), this]
  have hapk : (ap + mm / 2).toNat = ap.toNat + K := by rw [toNat_add_lt (by rw [hk]; omega), hk]
  have hbpk : (bp + mm / 2).toNat = bp.toNat + K := by rw [toNat_add_lt (by rw [hk]; omega), hk]
  have hqpk : (qp + mm / 2).toNat = qp.toNat + K := by rw [toNat_add_lt (by rw [hk]; omega), hk]
  -- the values
  have hb0 := base_pos
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  generalize hA : segVal W ap.toNat (N + m) = A
  generalize hB : segVal W bp.toNat N = B at hBge hBpos
  have hBsplit : B = segVal W bp.toNat K + base ^ K * segVal W (bp.toNat + K) (N - K) := by
    rw [← hB, show N = K + (N - K) by omega, segVal_add]; simp
  have hdb1 : SegDigits W (bp.toNat + K) (N - K) := fun i hi => by
    rw [Nat.add_assoc]; exact hdb (K + i) (by omega)
  have hv11 : base ≤ 2 * W[bp.toNat + K + (N - K) - 1]!.toNat := by
    rw [show bp.toNat + K + (N - K) - 1 = bp.toNat + N - 1 by omega]; exact hv1
  have hda2 : SegDigits W (ap.toNat + 2 * K) (N - K + H) := fun i hi => by
    rw [Nat.add_assoc]; exact hda (2 * K + i) (by omega)
  -- the first call
  have r1 := ih H hHm W (ap + 2 * (mm / 2)) (bp + mm / 2) (qp + mm / 2) sp (n - mm / 2)
    (mm - mm / 2) hh hW (by rw [hnk]; omega) (by rw [hnk]; omega) (by rw [hqpk, hbpk]; omega)
    (by rw [hbpk, hnk, hap2]; omega) (by rw [hap2, hnk]; omega) (by omega)
    (by rw [hap2, hnk]; exact hda2) (by rw [hbpk, hnk]; exact hdb1)
    (by rw [hbpk, hnk]; exact hv11)
  rw [hap2, hbpk, hqpk, hnk] at r1
  dsimp only
  generalize hR1 : rdiv t T W (ap + 2 * (mm / 2)) (bp + mm / 2) (qp + mm / 2) sp (n - mm / 2)
    (mm - mm / 2) = R1 at r1 ⊢
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := r1
  generalize hA2 : segVal W (ap.toNat + 2 * K) (N - K + H) = A2 at p6 p7
  generalize hB1 : segVal W (bp.toNat + K) (N - K) = B1 at p6 p7 hBsplit
  generalize hB0 : segVal W bp.toNat K = B0 at hBsplit
  have hB1ge : base ^ (N - K) ≤ 2 * B1 := by
    rw [← hB1]; exact (normalized_ge (by omega) hdb1 hv11).1
  have hB1pos : 0 < B1 := by have := pow_pos base_pos (N - K); omega
  have hB0lt : B0 < base ^ K := by rw [← hB0]; exact segVal_lt (hdb.mono (by omega))
  have hB1lt : B1 < base ^ (N - K) := by rw [← hB1]; exact segVal_lt hdb1
  have hA2lt : A2 < base ^ (N - K + H) := by rw [← hA2]; exact segVal_lt hda2
  have hQ1lt : A2 / B1 < 2 * base ^ H := quot_lt_two hA2lt hB1ge
  have hR1lt : A2 % B1 < B1 := Nat.mod_lt _ hB1pos
  -- the words of `W` that the first call keeps
  have hk1 : ∀ p, p < ap.toNat + 2 * K → bp.toNat ≤ p → R1.2[p]! = W[p]! := fun p h1 h2 =>
    p2 p (by omega) (by omega) (by omega)
  -- the region of the first correction: `Amid + β^k R1`
  have hR1z : segVal R1.2 (ap.toNat + 2 * K + (N - K)) H = 0 :=
    segVal_high_zero p3 (by rw [p6]; exact lt_of_lt_of_le hR1lt (le_of_lt hB1lt))
  have hR1v : segVal R1.2 (ap.toNat + 2 * K) (N - K) = A2 % B1 := by
    rw [← p6, segVal_add R1.2 (ap.toNat + 2 * K) (N - K) H, hR1z, Nat.mul_zero, Nat.add_zero]
  have hR1top : R1.2[ap.toNat + 2 * K + (N - K)]! = 0 := by
    have := segVal_eq_zero hR1z 0 (by omega); simpa using this
  have hX1 : segVal R1.2 (ap.toNat + K) (N + 1) =
      segVal W (ap.toNat + K) K + base ^ K * (A2 % B1) := by
    rw [show N + 1 = K + (N - K + 1) by omega, segVal_add,
      segVal_congr (W := R1.2) (W' := W) (p := ap.toNat + K) (p' := ap.toNat + K)
        fun i hi => hk1 _ (by omega) (by omega),
      show ap.toNat + K + K = ap.toNat + 2 * K by omega, segVal_succ, hR1v, hR1top]
    simp
  -- the first correction
  have hAL1 : 2 * H + 1 = (K + H - 1) / H * H + H + 1 := by
    rw [Nat.div_eq_of_lt_le (by omega : 1 * H ≤ K + H - 1) (by omega : K + H - 1 < (1 + 1) * H)]
    ring
  have hRb : ∀ i, i < N → R1.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
    hk1 _ (by omega) (by omega)
  have hBR : segVal R1.2 bp.toNat N = B := by rw [← hB]; exact segVal_congr hRb
  have hB0R : segVal R1.2 bp.toNat K = B0 := by
    rw [← hB0]; exact segVal_congr fun i hi => hRb i (by omega)
  have hdr1 : SegDigits R1.2 (ap.toNat + K) (N + 1) := fun i hi => by
    by_cases hiK : i < K
    · rw [hk1 _ (by omega) (by omega)]; rw [Nat.add_assoc]; exact hda (K + i) (by omega)
    · have := p3 (i - K) (by omega)
      rwa [show ap.toNat + 2 * K + (i - K) = ap.toNat + K + i by omega] at this
  have hQ1B0 : (A2 / B1) * B0 < 2 * base ^ m := by
    rcases Nat.eq_zero_or_pos B0 with h0 | h0
    · rw [h0, Nat.mul_zero]; exact Nat.mul_pos (by norm_num) (pow_pos base_pos _)
    · calc (A2 / B1) * B0 < 2 * base ^ H * B0 := Nat.mul_lt_mul_of_pos_right hQ1lt h0
        _ ≤ 2 * base ^ H * base ^ K := Nat.mul_le_mul_left _ (le_of_lt hB0lt)
        _ = 2 * base ^ m := by rw [hmK, pow_add]; ring
  have hpowm : 2 * base ^ m ≤ base ^ (N + 1) := by
    calc 2 * base ^ m ≤ base * base ^ N := Nat.mul_le_mul (by rw [base_eq]; norm_num)
          (Nat.pow_le_pow_right base_pos hmn)
      _ = base ^ (N + 1) := by ring
  have hBN : base ^ m ≤ 2 * B := le_trans (Nat.pow_le_pow_right base_pos hmn) hBge
  obtain ⟨q1, q2, q3, q4, q5, j1, hj1, q6, q7, q8⟩ := halfStep_spec t R1.2 (ap + mm / 2) bp n
    (mm / 2) (qp + mm / 2) (mm - mm / 2) R1.1 sp N K H (2 * H + 1) hN hk hh hAL1
    (by omega) hK1 (by omega) (by omega) p5 (by rw [hqpk]; omega) (by rw [hapk]; omega)
    (by rw [hapk]; omega) (by omega) (by rw [hapk]; exact hdr1) (hdb.congr hRb)
    (by rw [hqpk]; exact p4) (by rw [hBR]; exact hBpos)
    (by rw [hqpk, p7, hB0R]; omega)
    (by
      rw [hqpk, p7, hB0R, hBR, hapk]
      have : (0 : ℤ) ≤ segVal R1.2 (ap.toNat + K) (N + 1) := by positivity
      have h1 : ((A2 / B1 * B0 : ℕ) : ℤ) < 2 * base ^ m := by exact_mod_cast hQ1B0
      have h2 : (2 * base ^ m : ℤ) ≤ 4 * B := by exact_mod_cast (by omega : 2 * base ^ m ≤ 4 * B)
      linarith)
  rw [hapk, hX1, hBR, hqpk, p7, hB0R] at q6
  rw [hapk] at q2 q3
  rw [hqpk, p7] at q7
  rw [hapk, hBR] at q8
  rw [hqpk] at q2 q4
  generalize hR2 : halfStep t R1.2 (ap + mm / 2) bp n (mm / 2) (qp + mm / 2) (mm - mm / 2) R1.1 sp
    = R2 at q1 q2 q3 q4 q5 q6 q7 q8 ⊢
  generalize hX' : segVal R2.2 (ap.toNat + K) (N + 1) = X' at q6 q8
  have hX'lt : X' < B := by
    rcases q8 with h0 | h
    · subst h0
      have : (X' : ℤ) ≤ segVal W (ap.toNat + K) K + base ^ K * (A2 % B1) := by
        have h0 : (0 : ℤ) ≤ ((A2 / B1 * B0 : ℕ) : ℤ) := Nat.cast_nonneg _
        rw [q6]; push_cast at h0 ⊢; linarith
      have hmid : segVal W (ap.toNat + K) K < base ^ K := segVal_lt fun i hi => by
        rw [Nat.add_assoc]; exact hda (K + i) (by omega)
      have h3 : segVal W (ap.toNat + K) K + base ^ K * (A2 % B1) < B := by
        calc segVal W (ap.toNat + K) K + base ^ K * (A2 % B1)
            < base ^ K + base ^ K * (A2 % B1) := by omega
          _ = base ^ K * (A2 % B1 + 1) := by ring
          _ ≤ base ^ K * B1 := Nat.mul_le_mul_left _ hR1lt
          _ ≤ B := by rw [hBsplit]; omega
      have : (X' : ℤ) < B := by push_cast at this ⊢; omega
      exact_mod_cast this
    · exact h
  -- the second call, on the `n` limbs at `ap + k`
  have hX'n : segVal R2.2 (ap.toNat + K) N = X' := by
    have hz : segVal R2.2 (ap.toNat + K + N) 1 = 0 :=
      segVal_high_zero q3 (by rw [hX']; exact lt_of_lt_of_le hX'lt (le_of_lt (by
        rw [← hB]; exact segVal_lt hdb)))
    rw [← hX', segVal_add R2.2 (ap.toNat + K) N 1, hz, Nat.mul_zero, Nat.add_zero]
  have hk2 : ∀ p, ¬ (ap.toNat + K ≤ p ∧ p < ap.toNat + K + N + 1) →
      ¬ (qp.toNat + K ≤ p ∧ p < qp.toNat + K + H) → ¬ (sp.toNat ≤ p ∧ p < sp.toNat + 6 * m + 9) →
      R2.2[p]! = R1.2[p]! := fun p h1 h2 h3 => q2 p h1 h2 (by omega)
  have hRb2 : ∀ i, i < N → R2.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi => by
    rw [hk2 _ (by omega) (by omega) (by omega), hRb i hi]
  have hdb12 : SegDigits R2.2 (bp.toNat + K) (N - K) := hdb1.congr fun i hi => by
    rw [Nat.add_assoc]; exact hRb2 (K + i) (by omega)
  have hB1R2 : segVal R2.2 (bp.toNat + K) (N - K) = B1 := by
    rw [← hB1]; exact segVal_congr fun i hi => by
      rw [Nat.add_assoc]; exact hRb2 (K + i) (by omega)
  have r3 := ih K hKm R2.2 (ap + mm / 2) (bp + mm / 2) qp sp (n - mm / 2) (mm / 2) hk
    (by omega) (by rw [hnk]; omega) (by rw [hnk]; omega) (by rw [hbpk]; omega)
    (by rw [hbpk, hnk, hapk]; omega) (by rw [hapk, hnk]; omega) (by omega)
    (by rw [hapk, hnk, show N - K + K = N by omega]; exact q3.mono (by omega))
    (by rw [hbpk, hnk]; exact hdb12)
    (by rw [hbpk, hnk, show bp.toNat + K + (N - K) - 1 = bp.toNat + (N - 1) by omega,
          hRb2 _ (by omega), show bp.toNat + (N - 1) = bp.toNat + N - 1 by omega]; exact hv1)
  rw [hapk, hbpk, hnk] at r3
  generalize hR3 : rdiv t T R2.2 (ap + mm / 2) (bp + mm / 2) qp sp (n - mm / 2) (mm / 2) = R3
    at r3 ⊢
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := r3
  rw [show N - K + K = N by omega, hX'n, hB1R2] at s6 s7
  rw [show N - K + K = N by omega] at s3
  have hX'lt' : X' < base ^ (N - K + K) := by
    rw [show N - K + K = N by omega]; exact lt_of_lt_of_le hX'lt (le_of_lt (by
      rw [← hB]; exact segVal_lt hdb))
  have hB1ge' : base ^ (N - K) ≤ 2 * B1 := hB1ge
  have hQ0lt : X' / B1 < 2 * base ^ K := quot_lt_two hX'lt' hB1ge
  have hR0lt : X' % B1 < B1 := Nat.mod_lt _ hB1pos
  -- the region of the second correction: `Alow + β^k R0`
  have hk3 : ∀ p, ¬ (ap.toNat + K ≤ p ∧ p < ap.toNat + K + (N - K) + K) →
      ¬ (qp.toNat ≤ p ∧ p < qp.toNat + K) → ¬ (sp.toNat ≤ p ∧ p < sp.toNat + 6 * m + 9) →
      R3.2[p]! = R2.2[p]! := fun p h1 h2 h3 => s2 p h1 h2 (by omega)
  have hlow : ∀ i, i < K → R3.2[ap.toNat + i]! = W[ap.toNat + i]! := fun i hi => by
    rw [hk3 _ (by omega) (by omega) (by omega), hk2 _ (by omega) (by omega) (by omega),
      hk1 _ (by omega) (by omega)]
  have hR0z : segVal R3.2 (ap.toNat + K + (N - K)) K = 0 :=
    segVal_high_zero (by rw [show N - K + K = N by omega]; exact s3)
      (by rw [show N - K + K = N by omega, s6]; exact lt_of_lt_of_le hR0lt (le_of_lt hB1lt))
  have hR0v : segVal R3.2 (ap.toNat + K) (N - K) = X' % B1 := by
    rw [← s6, show N = N - K + K by omega, segVal_add R3.2 (ap.toNat + K) (N - K) K, hR0z,
      Nat.mul_zero, Nat.add_zero]
    congr 1; omega
  have hR0top : R3.2[ap.toNat + K + (N - K)]! = 0 := by
    have := segVal_eq_zero hR0z 0 (by omega); simpa using this
  have hX2 : segVal R3.2 ap.toNat (N + 1) = segVal W ap.toNat K + base ^ K * (X' % B1) := by
    rw [show N + 1 = K + (N - K + 1) by omega, segVal_add,
      segVal_congr (W := R3.2) (W' := W) (p := ap.toNat) (p' := ap.toNat) hlow, segVal_succ,
      hR0v, hR0top]
    simp
  have hRb3 : ∀ i, i < N → R3.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi => by
    rw [hk3 _ (by omega) (by omega) (by omega), hRb2 i hi]
  have hBR3 : segVal R3.2 bp.toNat N = B := by rw [← hB]; exact segVal_congr hRb3
  have hB0R3 : segVal R3.2 bp.toNat K = B0 := by
    rw [← hB0]; exact segVal_congr fun i hi => hRb3 i (by omega)
  have hdr3 : SegDigits R3.2 ap.toNat (N + 1) := fun i hi => by
    by_cases hiK : i < K
    · rw [hlow i hiK]; exact hda i (by omega)
    · have := s3 (i - K) (by omega)
      rwa [show ap.toNat + K + (i - K) = ap.toNat + i by omega] at this
  -- the second correction
  have hAL2 : 2 * K + 1 = (K + K - 1) / K * K + K + 1 := by
    rw [Nat.div_eq_of_lt_le (by omega : 1 * K ≤ K + K - 1) (by omega : K + K - 1 < (1 + 1) * K)]
    ring
  have hQ0B0 : (X' / B1) * B0 < 2 * base ^ m := by
    rcases Nat.eq_zero_or_pos B0 with h0 | h0
    · rw [h0, Nat.mul_zero]; exact Nat.mul_pos (by norm_num) (pow_pos base_pos _)
    · calc (X' / B1) * B0 < 2 * base ^ K * B0 := Nat.mul_lt_mul_of_pos_right hQ0lt h0
        _ ≤ 2 * base ^ K * base ^ K := Nat.mul_le_mul_left _ (le_of_lt hB0lt)
        _ = 2 * base ^ (K + K) := by rw [pow_add]; ring
        _ ≤ 2 * base ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right base_pos (by omega))
  unfold lowHalf
  dsimp only
  obtain ⟨t1, t2, t3, t4, t5, j0, hj0, t6, t7, t8⟩ := halfStep_spec t R3.2 ap bp n (mm / 2) qp
    (mm / 2) R3.1 sp N K K (2 * K + 1) hN hk hk hAL2 (by omega) hK1 (by omega) hK1 s5
    (by omega) hba (by omega) (by omega) hdr3 (hdb.congr hRb3) s4 (by rw [hBR3]; exact hBpos)
    (by rw [s7, hB0R3]; omega)
    (by
      rw [s7, hB0R3, hBR3]
      have : (0 : ℤ) ≤ segVal R3.2 ap.toNat (N + 1) := by positivity
      have h1 : ((X' / B1 * B0 : ℕ) : ℤ) < 2 * base ^ m := by exact_mod_cast hQ0B0
      have h2 : (2 * base ^ m : ℤ) ≤ 4 * B := by exact_mod_cast (by omega : 2 * base ^ m ≤ 4 * B)
      linarith)
  rw [hX2, hBR3, s7, hB0R3] at t6
  rw [s7] at t7
  rw [hBR3] at t8
  generalize hR4 : halfStep t R3.2 ap bp n (mm / 2) qp (mm / 2) R3.1 sp = R4
    at t1 t2 t3 t4 t5 t6 t7 t8 ⊢
  generalize hX2' : segVal R4.2 ap.toNat (N + 1) = X2' at t6 t8
  have hX2'lt : X2' < B := by
    rcases t8 with h0 | h
    · subst h0
      have : (X2' : ℤ) ≤ segVal W ap.toNat K + base ^ K * (X' % B1) := by
        have h0 : (0 : ℤ) ≤ ((X' / B1 * B0 : ℕ) : ℤ) := Nat.cast_nonneg _
        rw [t6]; push_cast at h0 ⊢; linarith
      have hlo : segVal W ap.toNat K < base ^ K := segVal_lt (hda.mono (by omega))
      have h3 : segVal W ap.toNat K + base ^ K * (X' % B1) < B := by
        calc segVal W ap.toNat K + base ^ K * (X' % B1)
            < base ^ K + base ^ K * (X' % B1) := by omega
          _ = base ^ K * (X' % B1 + 1) := by ring
          _ ≤ base ^ K * B1 := Nat.mul_le_mul_left _ hR0lt
          _ ≤ B := by rw [hBsplit]; omega
      have : (X2' : ℤ) < B := by push_cast at this ⊢; omega
      exact_mod_cast this
    · exact h
  -- the quotient: `Q0` gets the top word of `Q0`'s correction added at limb `k`
  have hsp4 : sp.toNat < R4.2.size := by omega
  have get4 := fun p => get_set R4.2 sp.toNat R4.1 p hsp4
  have hW4q : ∀ i, i < H → (R4.2.set! sp.toNat R4.1)[qp.toNat + K + i]! =
      R2.2[qp.toNat + K + i]! := fun i hi => by
    rw [get4, if_neg (by omega), t2 _ (by omega) (by omega) (by omega),
      hk3 _ (by omega) (by omega) (by omega)]
  have hd4 : SegDigits (R4.2.set! sp.toNat R4.1) (qp.toNat + K) H := q4.congr hW4q
  have hsp1 : SegDigits (R4.2.set! sp.toNat R4.1) sp.toNat (min (1 : UInt64).toNat H) := by
    rw [show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left (by omega)]
    intro i hi
    rw [show i = 0 by omega, Nat.add_zero, get4, if_pos rfl]
    exact lt_of_le_of_lt t5 one_lt_base
  obtain ⟨u1, u2, u3, u4, u5⟩ := addGen_inplace (R4.2.set! sp.toNat R4.1) (qp + mm / 2) sp 1
    (mm - mm / 2) (by simp; omega) (by rw [hqpk, hh]; simp; omega)
    (by rw [hh]; simp; omega) (by rw [hqpk, hh]; exact hd4) (by rw [hh]; exact hsp1)
    (by rw [hqpk, hh, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left (by omega)]; omega)
  rw [hqpk, hh, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left (by omega : 1 ≤ H)] at u5
  rw [hqpk, hh] at u2 u3
  have hsp1v : segVal (R4.2.set! sp.toNat R4.1) sp.toNat 1 = R4.1.toNat := by
    simp only [segVal, Nat.add_zero, pow_zero, Nat.mul_one, Nat.zero_add]; rw [get4, if_pos rfl]
  rw [hsp1v, segVal_congr hW4q] at u5
  generalize hR5 : addGen (R4.2.set! sp.toNat R4.1) (qp + mm / 2) sp 1 (qp + mm / 2)
    (mm - mm / 2) = R5 at u1 u2 u3 u4 u5 ⊢
  -- the words of the result
  have h54 : ∀ p, (p < qp.toNat + K ∨ qp.toNat + K + H ≤ p) → p ≠ sp.toNat →
      R5.2[p]! = R4.2[p]! := fun p h1 h2 => by rw [u2 p h1, get4, if_neg h2]
  have hframe : ∀ p, ¬ (ap.toNat ≤ p ∧ p < ap.toNat + N + m) →
      ¬ (qp.toNat ≤ p ∧ p < qp.toNat + m) → ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (6 * m + 9)) →
      R5.2[p]! = W[p]! := fun p h1 h2 h3 => by
    rw [h54 p (by omega) (by omega), t2 p (by omega) (by omega) (by omega),
      hk3 p (by omega) (by omega) (by omega), hk2 p (by omega) (by omega) (by omega),
      p2 p (by omega) (by omega) (by omega)]
  -- the zeros above the remainder
  have hBlt : B < base ^ N := by rw [← hB]; exact segVal_lt hdb
  have hZ4 : R4.2[ap.toNat + N]! = 0 := by
    have hz := segVal_high_zero (W := R4.2) (p := ap.toNat) (a := N) (k := 1) t3
      (by rw [hX2']; exact lt_of_lt_of_le hX2'lt (le_of_lt hBlt))
    have := segVal_eq_zero hz 0 (by omega); simpa using this
  have hZ2 : R2.2[ap.toNat + K + N]! = 0 := by
    have hz := segVal_high_zero (W := R2.2) (p := ap.toNat + K) (a := N) (k := 1) q3
      (by rw [hX']; exact lt_of_lt_of_le hX'lt (le_of_lt hBlt))
    have := segVal_eq_zero hz 0 (by omega); simpa using this
  have hzero : ∀ i, i < m → R5.2[ap.toNat + N + i]! = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [Nat.add_zero, h54 _ (by omega) (by omega)]; exact hZ4
    rw [h54 _ (by omega) (by omega), t2 _ (by omega) (by omega) (by omega)]
    by_cases hiK : i < K
    · have := segVal_eq_zero hR0z i hiK
      rwa [show ap.toNat + K + (N - K) + i = ap.toNat + N + i by omega] at this
    rw [hk3 _ (by omega) (by omega) (by omega)]
    by_cases hiK' : i = K
    · subst hiK'; rw [show ap.toNat + N + i = ap.toNat + i + N by omega]; exact hZ2
    rw [hk2 _ (by omega) (by omega) (by omega)]
    have := segVal_eq_zero hR1z (i - K) (by omega)
    rwa [show ap.toNat + 2 * K + (N - K) + (i - K) = ap.toNat + N + i by omega] at this
  have hrem : segVal R5.2 ap.toNat (N + m) = X2' := by
    rw [segVal_add, segVal_zeros hzero, Nat.mul_zero, Nat.add_zero, ← hX2', segVal_succ, hZ4]
    simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    exact segVal_congr fun i hi => h54 _ (by omega) (by omega)
  -- the identity `A = Q B + R`
  have hAsplit : A = segVal W ap.toNat K + base ^ K * segVal W (ap.toNat + K) K +
      base ^ (2 * K) * A2 := by
    rw [← hA, ← hA2, show N + m = K + K + (N - K + H) by omega, segVal_window,
      show K + K = 2 * K by omega, show ap.toNat + K + K = ap.toNat + 2 * K by omega]
  have hQlo : segVal R5.2 qp.toNat m = segVal R4.2 qp.toNat K +
      base ^ K * segVal R5.2 (qp.toNat + K) H := by
    rw [hmK, segVal_add]
    congr 1
    exact segVal_congr fun i hi => h54 _ (by omega) (by omega)
  have hA2d := Nat.div_add_mod A2 B1
  have hXd := Nat.div_add_mod X' B1
  generalize hS : segVal R5.2 qp.toNat m = S at hQlo ⊢
  generalize hU : segVal R5.2 (qp.toNat + K) H = U at hQlo u5
  generalize hQ1l : segVal R2.2 (qp.toNat + K) H = Q1l at q7 u5
  generalize hQ0l : segVal R4.2 qp.toNat K = Q0l at t7 hQlo
  generalize hAlow : segVal W ap.toNat K = Alow at hAsplit t6
  generalize hAmid : segVal W (ap.toNat + K) K = Amid at hAsplit q6
  generalize hQ1v : A2 / B1 = Q1 at q6 q7 hA2d
  generalize hR1v : A2 % B1 = R1v at q6 hA2d
  generalize hQ0v : X' / B1 = Q0 at t6 t7 hXd
  generalize hR0v' : X' % B1 = R0 at t6 hXd
  have hpm : base ^ m = base ^ K * base ^ H := by rw [hmK, pow_add]
  have E1 : (A : ℤ) = Alow + base ^ K * Amid + base ^ (2 * K) * A2 := by exact_mod_cast hAsplit
  have E2 : (B1 : ℤ) * Q1 + R1v = A2 := by exact_mod_cast hA2d
  have E3 : (X2' : ℤ) = Alow + base ^ K * R0 - Q0 * B0 + j0 * B := by push_cast at t6; exact t6
  have E4 : (B1 : ℤ) * Q0 + R0 = X' := by exact_mod_cast hXd
  have E5 : (X' : ℤ) = Amid + base ^ K * R1v - Q1 * B0 + j1 * B := by push_cast at q6; exact q6
  have E6 : (B : ℤ) = B0 + base ^ K * B1 := by exact_mod_cast hBsplit
  have E7 : (S : ℤ) = Q0l + base ^ K * U := by exact_mod_cast hQlo
  have E8 : (Q0l : ℤ) + R4.1.toNat * base ^ K + j0 = Q0 := by exact_mod_cast t7
  have E9 : (Q1l : ℤ) + R2.1.toNat * base ^ H + j1 = Q1 := by exact_mod_cast q7
  have E10 : (U : ℤ) + R5.1.toNat * base ^ H = Q1l + R4.1.toNat := by exact_mod_cast u5
  have Eb : ((base : ℤ) ^ m) = (base : ℤ) ^ K * (base : ℤ) ^ H := by exact_mod_cast hpm
  have E2K : ((base : ℤ) ^ (2 * K)) = (base : ℤ) ^ K * (base : ℤ) ^ K := by
    rw [two_mul, pow_add]
  have hQtot : (S : ℤ) + (R2.1.toNat + R5.1.toNat) * base ^ m =
      (Q0 - j0) + base ^ K * (Q1 - j1) := by
    linear_combination E7 + E8 + (base : ℤ) ^ K * E9 + (base : ℤ) ^ K * E10 +
      ((R2.1.toNat : ℤ) + R5.1.toNat) * Eb
  have hfinal : (A : ℤ) = ((Q0 - j0) + base ^ K * (Q1 - j1)) * B + X2' := by
    linear_combination E1 - (base : ℤ) ^ (2 * K) * E2 - E3 - (base : ℤ) ^ K * E4 -
      (base : ℤ) ^ K * E5 - ((Q0 : ℤ) + (base : ℤ) ^ K * Q1) * E6 + (Q1 * B1 : ℤ) * E2K
  have hAeq : A = (S + (R2.1.toNat + R5.1.toNat) * base ^ m) * B + X2' := by
    have : (A : ℤ) = ((S : ℤ) + (R2.1.toNat + R5.1.toNat) * base ^ m) * B + X2' := by
      rw [hQtot]; exact hfinal
    exact_mod_cast this
  have hdiv : A / B = S + (R2.1.toNat + R5.1.toNat) * base ^ m := by
    rw [hAeq, Nat.mul_comm, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hX2'lt, Nat.add_zero]
  have hmod : A % B = X2' := by
    rw [hAeq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hX2'lt]
  have hAlt : A < base ^ (N + m) := by rw [← hA]; exact segVal_lt hda
  have hQlt := quot_lt_two hAlt hBge
  have hc1e : R2.1.toNat + R5.1.toNat ≤ 1 := by
    rw [hdiv] at hQlt
    by_contra hc
    have : 2 * base ^ m ≤ (R2.1.toNat + R5.1.toNat) * base ^ m :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hadd : (R2.1 + R5.1).toNat = R2.1.toNat + R5.1.toNat := by
    rw [toNat_add_lt (by omega)]
  refine ⟨by simp [u1, t1, s1, q1, p1], hframe, fun i hi => ?_, fun i hi => ?_, by
    rw [hadd]; exact hc1e, by rw [hrem, hA, hB, hmod], by
      show segVal R5.2 qp.toNat m + (R2.1 + R5.1).toNat * base ^ m = _
      rw [hadd, hS, hA, hB, hdiv]⟩
  · rcases Nat.lt_or_ge i N with hiN | hiN
    · rw [h54 _ (by omega) (by omega)]; exact t3 i (by omega)
    · have := hzero (i - N) (by omega)
      rw [show ap.toNat + N + (i - N) = ap.toNat + i by omega] at this
      rw [this]; exact base_pos
  · rcases Nat.lt_or_ge i K with hiK | hiK
    · rw [h54 _ (by omega) (by omega)]; exact t4 i hiK
    · have := u3 (i - K) (by omega)
      rwa [show qp.toNat + K + (i - K) = qp.toNat + i by omega] at this

end Library.Numerics.Bignum
