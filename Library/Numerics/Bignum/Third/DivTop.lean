module

public import Library.Numerics.Bignum.Third.DivRec

@[expose] public section

/-!
The last part of a division with fewer quotient limbs than divisor limbs (`tdiv_spec`) and
Algorithm 1.9, UnbalancedDivision (`udiv_spec`).

`tdiv` divides the top `2 m` limbs of a dividend of `n + m` limbs by the top `m` limbs of the
divisor with `rdiv`, and subtracts the product of that quotient by the low `n - m` limbs with the
corrections of `subFix`, as the steps 3 to 5 of Algorithm 1.8 do.  `udiv` divides a dividend of
`n + M` limbs below `β^M B` by `n` quotient limbs at a time from the top, each a division of `2 n`
by `n` limbs, and the rest by `rdiv` or `tdiv`; `block_step` is the arithmetic of one block.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- One block of a division by `B β^p`: the remainder by `B β^(p + w)` is the low part `L` and the
window `D` of `w` limbs from `p`, and dividing the window by `B` gives the remainder and the next
`w` limbs of the quotient. -/
theorem block_step {A B L D p w : ℕ} (hB : 0 < B) (hV : A % (B * base ^ (p + w)) = L + base ^ p * D)
    (hL : L < base ^ p) :
    A % (B * base ^ p) = L + base ^ p * (D % B) ∧
      A / (B * base ^ p) = A / (B * base ^ (p + w)) * base ^ w + D / B := by
  have hbp : 0 < base ^ p := pow_pos base_pos p
  have hU := Nat.div_add_mod A (B * base ^ (p + w))
  rw [hV] at hU
  have hDB := Nat.div_add_mod D B
  have hDm := Nat.mod_lt D hB
  have hlt : L + base ^ p * (D % B) < B * base ^ p := by
    calc L + base ^ p * (D % B) < base ^ p + base ^ p * (D % B) := by omega
      _ = base ^ p * (D % B + 1) := by ring
      _ ≤ base ^ p * B := Nat.mul_le_mul_left _ hDm
      _ = B * base ^ p := by ring
  have hA : A = (L + base ^ p * (D % B)) +
      (A / (B * base ^ (p + w)) * base ^ w + D / B) * (B * base ^ p) := by
    rw [pow_add] at hU ⊢
    zify at hU hDB ⊢
    linear_combination -hU - ((base : ℤ) ^ p) * hDB
  generalize hq : A / (B * base ^ (p + w)) = q at hA ⊢
  constructor
  · rw [hA, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  · rw [hA, Nat.add_mul_div_right _ _ (Nat.mul_pos hB hbp), Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- A division whose dividend is below `β^m B` has the top word 0. -/
theorem DivPost.top_zero {W : Array UInt64} {ap bp qp sp n m S : ℕ} {r : UInt64 × Array UInt64}
    (h : DivPost W ap bp qp sp n m S r)
    (hlt : segVal W ap (n + m) < base ^ m * segVal W bp n) : r.1.toNat = 0 := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := h
  have hBpos : 0 < segVal W bp n := by
    rcases Nat.eq_zero_or_pos (segVal W bp n) with h0 | h0
    · rw [h0, Nat.mul_zero] at hlt; omega
    · exact h0
  have hq : segVal W ap (n + m) / segVal W bp n < base ^ m :=
    (Nat.div_lt_iff_lt_mul hBpos).mpr hlt
  by_contra hne
  have : base ^ m ≤ r.1.toNat * base ^ m := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
  omega

set_option maxHeartbeats 4000000 in
/-- The last part of Algorithm 1.9 for `2 ≤ m < n` quotient limbs: the top `2 m` limbs divided by
the top `m` limbs of the divisor, and the correction by the product with the low `n - m` limbs. -/
theorem tdiv_spec (t T : UInt64) (W : Array UInt64) (ap bp qp sp n mm : UInt64) (N m : ℕ)
    (hN : n.toNat = N) (hm : mm.toNat = m) (hW : W.size < 2 ^ 62) (hm2 : 2 ≤ m) (hmN : m < N)
    (hqb : qp.toNat + m ≤ bp.toNat) (hba : bp.toNat + N ≤ ap.toNat)
    (has : ap.toNat + N + m ≤ sp.toNat) (hsz : sp.toNat + 12 * N + 9 ≤ W.size)
    (hda : SegDigits W ap.toNat (N + m)) (hdb : SegDigits W bp.toNat N)
    (hv1 : base ≤ 2 * W[bp.toNat + N - 1]!.toNat) :
    DivPost W ap.toNat bp.toNat qp.toNat sp.toNat N m (12 * N + 9)
      (tdiv t T W ap bp qp sp n mm) := by
  obtain ⟨S, hS⟩ : ∃ S, S = N - m := ⟨_, rfl⟩
  have hb0 := base_pos
  have hs : (n - mm).toNat = S := by rw [toNat_sub_le' (by omega), hN, hm, hS]
  have has' : (ap + (n - mm)).toNat = ap.toNat + S := by rw [toNat_add_lt (by omega), hs]
  have hbs' : (bp + (n - mm)).toNat = bp.toNat + S := by rw [toNat_add_lt (by omega), hs]
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  generalize hA : segVal W ap.toNat (N + m) = A
  generalize hB : segVal W bp.toNat N = B at hBge hBpos
  have hdb1 : SegDigits W (bp.toNat + S) m := fun i hi => by
    rw [Nat.add_assoc]; exact hdb (S + i) (by omega)
  have hv11 : base ≤ 2 * W[bp.toNat + S + m - 1]!.toNat := by
    rw [show bp.toNat + S + m - 1 = bp.toNat + N - 1 by omega]; exact hv1
  have hdat : SegDigits W (ap.toNat + S) (m + m) := fun i hi => by
    rw [Nat.add_assoc]; exact hda (S + i) (by omega)
  -- the top part
  have r1 := rdiv_spec t T m W (ap + (n - mm)) (bp + (n - mm)) qp sp mm mm hm hW (by omega)
    (by omega) (by rw [hbs']; omega) (by rw [hbs', has']; omega) (by rw [has']; omega)
    (by omega) (by rw [has', hm]; exact hdat) (by rw [hbs', hm]; exact hdb1)
    (by rw [hbs', hm]; exact hv11)
  rw [has', hbs', hm] at r1
  unfold tdiv
  dsimp only
  generalize hR1 : rdiv t T W (ap + (n - mm)) (bp + (n - mm)) qp sp mm mm = R1 at r1 ⊢
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := r1
  generalize hAt : segVal W (ap.toNat + S) (m + m) = At at p6 p7
  generalize hB1 : segVal W (bp.toNat + S) m = B1 at p6 p7
  have hB1ge : base ^ m ≤ 2 * B1 := by rw [← hB1]; exact (normalized_ge (by omega) hdb1 hv11).1
  have hB1pos : 0 < B1 := by have := pow_pos base_pos m; omega
  have hB1lt : B1 < base ^ m := by rw [← hB1]; exact segVal_lt hdb1
  have hAtlt : At < base ^ (m + m) := by rw [← hAt]; exact segVal_lt hdat
  have hQlt : At / B1 < 2 * base ^ m := quot_lt_two hAtlt hB1ge
  have hRlt : At % B1 < B1 := Nat.mod_lt _ hB1pos
  have hk1 : ∀ p, p < ap.toNat + S → bp.toNat ≤ p → R1.2[p]! = W[p]! := fun p h1 h2 =>
    p2 p (by omega) (by omega) (by omega)
  have hRz : segVal R1.2 (ap.toNat + S + m) m = 0 :=
    segVal_high_zero p3 (by rw [p6]; exact lt_of_lt_of_le hRlt (le_of_lt hB1lt))
  have hRv : segVal R1.2 (ap.toNat + S) m = At % B1 := by
    rw [← p6, segVal_add R1.2 (ap.toNat + S) m m, hRz, Nat.mul_zero, Nat.add_zero]
  have hRtop : R1.2[ap.toNat + S + m]! = 0 := by
    have := segVal_eq_zero hRz 0 (by omega); simpa using this
  have hX : segVal R1.2 ap.toNat (N + 1) = segVal W ap.toNat S + base ^ S * (At % B1) := by
    rw [show N + 1 = S + (m + 1) by omega, segVal_add,
      segVal_congr (W := R1.2) (W' := W) (p := ap.toNat) (p' := ap.toNat)
        fun i hi => hk1 _ (by omega) (by omega), segVal_succ, hRv, hRtop]
    simp
  have hRb : ∀ i, i < N → R1.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
    hk1 _ (by omega) (by omega)
  have hBR : segVal R1.2 bp.toNat N = B := by rw [← hB]; exact segVal_congr hRb
  generalize hB0 : segVal W bp.toNat S = B0
  have hB0R : segVal R1.2 bp.toNat S = B0 := by
    rw [← hB0]; exact segVal_congr fun i hi => hRb i (by omega)
  have hB0lt : B0 < base ^ S := by rw [← hB0]; exact segVal_lt (hdb.mono (by omega))
  have hBsplit : B = B0 + base ^ S * B1 := by
    rw [← hB, ← hB0, ← hB1, show N = S + m by omega, segVal_add]
  have hdr : SegDigits R1.2 ap.toNat (N + 1) := fun i hi => by
    by_cases hiS : i < S
    · rw [hk1 _ (by omega) (by omega)]; exact hda i (by omega)
    · have := p3 (i - S) (by omega)
      rwa [show ap.toNat + S + (i - S) = ap.toNat + i by omega] at this
  -- the correction
  obtain ⟨NC, hNC⟩ : ∃ NC, NC = (S + m - 1) / m := ⟨_, rfl⟩
  have hNCm : NC * m ≤ S + m - 1 := by rw [hNC]; exact Nat.div_mul_le_self _ _
  have hQB0 : (At / B1) * B0 < 2 * base ^ N := by
    rcases Nat.eq_zero_or_pos B0 with h0 | h0
    · rw [h0, Nat.mul_zero]; exact Nat.mul_pos (by norm_num) (pow_pos base_pos _)
    · calc (At / B1) * B0 < 2 * base ^ m * B0 := Nat.mul_lt_mul_of_pos_right hQlt h0
        _ ≤ 2 * base ^ m * base ^ S := Nat.mul_le_mul_left _ (le_of_lt hB0lt)
        _ = 2 * base ^ N := by rw [show N = m + S by omega, pow_add]; ring
  have hpowN : 2 * base ^ N ≤ base ^ (N + 1) := by
    calc 2 * base ^ N ≤ base * base ^ N := Nat.mul_le_mul_right _ (by rw [base_eq]; norm_num)
      _ = base ^ (N + 1) := by ring
  obtain ⟨q1, q2, q3, q4, q5, j, hj, q6, q7, q8⟩ := halfStep_spec t R1.2 ap bp n (n - mm) qp mm R1.1
    sp N S m (NC * m + m + 1) hN hs hm (by rw [hNC]) (by omega) (by omega) (by omega) (by omega)
    p5 hqb hba (by omega) (by omega) hdr (hdb.congr hRb) p4 (by rw [hBR]; exact hBpos)
    (by rw [p7, hB0R]; omega)
    (by
      rw [p7, hB0R, hBR]
      have : (0 : ℤ) ≤ segVal R1.2 ap.toNat (N + 1) := by positivity
      have h1 : ((At / B1 * B0 : ℕ) : ℤ) < 2 * base ^ N := by exact_mod_cast hQB0
      have h2 : (2 * base ^ N : ℤ) ≤ 4 * B := by exact_mod_cast (by omega : 2 * base ^ N ≤ 4 * B)
      linarith)
  rw [hX, hBR, p7, hB0R] at q6
  rw [p7] at q7
  rw [hBR] at q8
  generalize hR2 : halfStep t R1.2 ap bp n (n - mm) qp mm R1.1 sp = R2 at q1 q2 q3 q4 q5 q6 q7 q8 ⊢
  generalize hX' : segVal R2.2 ap.toNat (N + 1) = X' at q6 q8
  have hBlt : B < base ^ N := by rw [← hB]; exact segVal_lt hdb
  have hX'lt : X' < B := by
    rcases q8 with h0 | h
    · subst h0
      have : (X' : ℤ) ≤ segVal W ap.toNat S + base ^ S * (At % B1) := by
        have h0 : (0 : ℤ) ≤ ((At / B1 * B0 : ℕ) : ℤ) := Nat.cast_nonneg _
        rw [q6]; push_cast at h0 ⊢; linarith
      have hlo : segVal W ap.toNat S < base ^ S := segVal_lt (hda.mono (by omega))
      have h3 : segVal W ap.toNat S + base ^ S * (At % B1) < B := by
        calc segVal W ap.toNat S + base ^ S * (At % B1)
            < base ^ S + base ^ S * (At % B1) := by omega
          _ = base ^ S * (At % B1 + 1) := by ring
          _ ≤ base ^ S * B1 := Nat.mul_le_mul_left _ hRlt
          _ ≤ B := by rw [hBsplit]; omega
      have : (X' : ℤ) < B := by push_cast at this ⊢; omega
      exact_mod_cast this
    · exact h
  -- the zeros above the remainder
  have hZ : R2.2[ap.toNat + N]! = 0 := by
    have hz := segVal_high_zero (W := R2.2) (p := ap.toNat) (a := N) (k := 1) q3
      (by rw [hX']; exact lt_of_lt_of_le hX'lt (le_of_lt hBlt))
    have := segVal_eq_zero hz 0 (by omega); simpa using this
  have hzero : ∀ i, i < m → R2.2[ap.toNat + N + i]! = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [Nat.add_zero]; exact hZ
    · rw [q2 _ (by omega) (by omega) (by omega)]
      have := segVal_eq_zero hRz i hi
      rwa [show ap.toNat + S + m + i = ap.toNat + N + i by omega] at this
  have hrem : segVal R2.2 ap.toNat (N + m) = X' := by
    rw [segVal_add, segVal_zeros hzero, Nat.mul_zero, Nat.add_zero, ← hX', segVal_succ, hZ]
    simp
  -- the identity
  have hAsplit : A = segVal W ap.toNat S + base ^ S * At := by
    rw [← hA, ← hAt, show N + m = S + (m + m) by omega, segVal_add]
  have hdm := Nat.div_add_mod At B1
  generalize At / B1 = Qh at hdm q6 q7
  generalize At % B1 = Rh at hdm q6
  have E1 : (A : ℤ) = segVal W ap.toNat S + base ^ S * At := by exact_mod_cast hAsplit
  have E2 : (B1 : ℤ) * Qh + Rh = At := by exact_mod_cast hdm
  have E3 : (B : ℤ) = B0 + base ^ S * B1 := by exact_mod_cast hBsplit
  have E4 : (segVal R2.2 qp.toNat m : ℤ) + R2.1.toNat * base ^ m + j = Qh := by
    exact_mod_cast q7
  have E5 : (X' : ℤ) = segVal W ap.toNat S + base ^ S * Rh - Qh * B0 + j * B := by
    push_cast at q6; exact q6
  have hfinal : (A : ℤ) = (segVal R2.2 qp.toNat m + R2.1.toNat * base ^ m : ℕ) * B + X' := by
    push_cast
    linear_combination E1 - (base : ℤ) ^ S * E2 - E5 - (B : ℤ) * E4 - (Qh : ℤ) * E3
  have hAeq : A = X' + (segVal R2.2 qp.toNat m + R2.1.toNat * base ^ m) * B := by
    have : (A : ℤ) = X' + (segVal R2.2 qp.toNat m + R2.1.toNat * base ^ m : ℕ) * B := by
      rw [hfinal]; ring
    exact_mod_cast this
  refine ⟨by rw [q1, p1], fun p h1 h2 h3 => by
      rw [q2 p (by omega) (by omega) (by omega), p2 p (by omega) (by omega) (by omega)],
    fun i hi => ?_, q4, q5, by rw [hrem, hA, hB, hAeq, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hX'lt], by
      rw [hA, hB, hAeq, Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt hX'lt, Nat.zero_add]⟩
  rcases Nat.lt_or_ge i N with hiN | hiN
  · exact q3 i (by omega)
  · have := hzero (i - N) (by omega)
    rw [show ap.toNat + N + (i - N) = ap.toNat + i by omega] at this
    rw [this]; exact base_pos

/-- The invariant of the loop of `udiv` once the quotient limbs from `MJ` on are written. -/
def UInv (W0 : Array UInt64) (ap qp sp N M A B MJ : ℕ) (V : Array UInt64) : Prop :=
  V.size = W0.size ∧
  (∀ p, ¬ (ap ≤ p ∧ p < ap + N + M) → ¬ (qp + MJ ≤ p ∧ p < qp + M) →
    ¬ (sp ≤ p ∧ p < sp + (12 * N + 9)) → V[p]! = W0[p]!) ∧
  SegDigits V ap (N + M) ∧ SegDigits V (qp + MJ) (M - MJ) ∧
  segVal V (qp + MJ) (M - MJ) = A / (B * base ^ MJ) ∧ segVal V ap (N + M) = A % (B * base ^ MJ)

set_option maxHeartbeats 4000000 in
/-- One block of Algorithm 1.9: the `2 n` limbs from `p = MJ - n` divided by `B`. -/
theorem udiv_block (t T : UInt64) (W0 V : Array UInt64) (ap bp qp sp n pp : UInt64)
    (N M A P : ℕ) (hN : n.toNat = N) (hP : pp.toNat = P) (hW : W0.size < 2 ^ 62) (hn : 2 ≤ N)
    (hPM : P + N ≤ M) (hP1 : 1 ≤ P)
    (hqb : qp.toNat + M ≤ bp.toNat) (hba : bp.toNat + N ≤ ap.toNat)
    (has : ap.toNat + N + M ≤ sp.toNat) (hsz : sp.toNat + 12 * N + 9 ≤ W0.size)
    (hdb : SegDigits W0 bp.toNat N) (hv1 : base ≤ 2 * W0[bp.toNat + N - 1]!.toNat)
    (hinv : UInv W0 ap.toNat qp.toNat sp.toNat N M A (segVal W0 bp.toNat N) (P + N) V) :
    UInv W0 ap.toNat qp.toNat sp.toNat N M A (segVal W0 bp.toNat N) P
      (rdiv t T V (ap + pp) bp (qp + pp) sp n n).2 := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hinv
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  generalize hB : segVal W0 bp.toNat N = B at hBge hBpos v5 v6 ⊢
  have hBlt : B < base ^ N := by rw [← hB]; exact segVal_lt hdb
  have hap : (ap + pp).toNat = ap.toNat + P := by rw [toNat_add_lt (by omega), hP]
  have hqp : (qp + pp).toNat = qp.toNat + P := by rw [toNat_add_lt (by omega), hP]
  have hVb : ∀ i, i < N → V[bp.toNat + i]! = W0[bp.toNat + i]! := fun i hi =>
    v2 _ (by omega) (by omega) (by omega)
  have hBV : segVal V bp.toNat N = B := by rw [← hB]; exact segVal_congr hVb
  -- the window of the block
  have hsplit := segVal_window V ap.toNat P (2 * N) (M - N - P)
  rw [show P + 2 * N + (M - N - P) = N + M by omega, v6] at hsplit
  have hlt : A % (B * base ^ (P + N)) < B * base ^ (P + N) :=
    Nat.mod_lt _ (Nat.mul_pos hBpos (pow_pos base_pos _))
  have hlt2 : A % (B * base ^ (P + N)) < base ^ (P + 2 * N) :=
    lt_of_lt_of_le hlt (by
      calc B * base ^ (P + N) ≤ base ^ N * base ^ (P + N) := Nat.mul_le_mul_right _ (le_of_lt hBlt)
        _ = base ^ (P + 2 * N) := by rw [← pow_add]; congr 1; omega)
  have hrest : segVal V (ap.toNat + P + 2 * N) (M - N - P) = 0 := by
    have := segVal_high_zero (W := V) (p := ap.toNat) (a := P + 2 * N) (k := M - N - P)
      (by rw [show P + 2 * N + (M - N - P) = N + M by omega]; exact v3)
      (by rw [show P + 2 * N + (M - N - P) = N + M by omega, v6]; exact hlt2)
    rwa [← Nat.add_assoc] at this
  rw [hrest, Nat.mul_zero, Nat.add_zero] at hsplit
  generalize hL : segVal V ap.toNat P = L at hsplit
  generalize hD : segVal V (ap.toNat + P) (2 * N) = D at hsplit
  have hLlt : L < base ^ P := by rw [← hL]; exact segVal_lt (v3.mono (by omega))
  have hDlt : D < base ^ N * B := by
    have h1 : base ^ P * D < base ^ P * (base ^ N * B) := by
      calc base ^ P * D ≤ A % (B * base ^ (P + N)) := by rw [hsplit]; omega
        _ < B * base ^ (P + N) := hlt
        _ = base ^ P * (base ^ N * B) := by rw [pow_add]; ring
    exact Nat.lt_of_mul_lt_mul_left h1
  -- the division of the block
  have hdD : SegDigits V (ap.toNat + P) (N + N) := fun i hi => by
    rw [Nat.add_assoc]; exact v3 (P + i) (by omega)
  have hv1V : base ≤ 2 * V[bp.toNat + N - 1]!.toNat := by
    rw [show bp.toNat + N - 1 = bp.toNat + (N - 1) by omega, hVb _ (by omega),
      show bp.toNat + (N - 1) = bp.toNat + N - 1 by omega]; exact hv1
  have r := rdiv_spec t T N V (ap + pp) bp (qp + pp) sp n n hN (by omega) (by omega) (by omega)
    (by rw [hqp]; omega) (by rw [hap, hN]; omega) (by rw [hap, hN]; omega) (by omega)
    (by rw [hap, hN]; exact hdD) (by rw [hN]; exact hdb.congr hVb) (by rw [hN]; exact hv1V)
  rw [hap, hqp, hN] at r
  have hc0 := r.top_zero (by rw [show N + N = 2 * N by omega, hD, hBV]; exact hDlt)
  generalize hR : rdiv t T V (ap + pp) bp (qp + pp) sp n n = R at r hc0 ⊢
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := r
  rw [show N + N = 2 * N by omega, hD, hBV] at r6 r7
  rw [hc0, Nat.zero_mul, Nat.add_zero] at r7
  rw [show N + N = 2 * N by omega] at r3
  obtain ⟨b1, b2⟩ := block_step (A := A) (B := B) (L := L) (D := D) (p := P) (w := N) hBpos
    hsplit hLlt
  have hRV : ∀ q, (q < ap.toNat + P ∨ ap.toNat + P + 2 * N ≤ q) → q < qp.toNat + P ∨
      qp.toNat + P + N ≤ q → ¬ (sp.toNat ≤ q ∧ q < sp.toNat + (6 * N + 9)) → R.2[q]! = V[q]! :=
    fun q h1 h2 h3 => r2 q (by omega) (by omega) h3
  refine ⟨by rw [r1, v1], fun q h1 h2 h3 => by
      rw [hRV q (by omega) (by omega) (by omega)]; exact v2 q h1 (by omega) h3,
    fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · by_cases hw : P ≤ i ∧ i < P + 2 * N
    · have := r3 (i - P) (by omega)
      rwa [show ap.toNat + P + (i - P) = ap.toNat + i by omega] at this
    · rw [hRV _ (by omega) (by omega) (by omega)]; exact v3 i hi
  · by_cases hw : i < N
    · exact r4 i hw
    · rw [hRV _ (by omega) (by omega) (by omega)]
      have := v4 (i - N) (by omega)
      rwa [show qp.toNat + (P + N) + (i - N) = qp.toNat + P + i by omega] at this
  · rw [show M - P = N + (M - (P + N)) by omega, segVal_add, r7,
      show qp.toNat + P + N = qp.toNat + (P + N) by omega,
      segVal_congr (W := R.2) (W' := V) (p := qp.toNat + (P + N)) (p' := qp.toNat + (P + N))
        fun i hi => hRV _ (by omega) (by omega) (by omega), v5, b2]
    ring
  · have hsplit' := segVal_window R.2 ap.toNat P (2 * N) (M - N - P)
    rw [show P + 2 * N + (M - N - P) = N + M by omega] at hsplit'
    rw [hsplit', r6, b1,
      segVal_congr (W := R.2) (W' := V) (p := ap.toNat) (p' := ap.toNat)
        fun i hi => hRV _ (by omega) (by omega) (by omega),
      segVal_congr (W := R.2) (W' := V) (p := ap.toNat + P + 2 * N) (p' := ap.toNat + P + 2 * N)
        fun i hi => hRV _ (by omega) (by omega) (by omega), hrest, hL]
    ring

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

set_option maxHeartbeats 4000000 in
/-- Algorithm 1.9: `udiv` divides the `n + M` limbs at `ap`, below `β^M B`, by the normalized
`n ≥ 2` limbs `B` at `bp`, with the quotient in the `M` limbs at `qp` and the remainder over the
dividend's segment. -/
theorem udiv_spec (t T : UInt64) (W : Array UInt64) (ap bp qp sp n MM : UInt64) (N M : ℕ)
    (hN : n.toNat = N) (hM : MM.toNat = M) (hW : W.size < 2 ^ 62) (hn : 2 ≤ N) (hM1 : 1 ≤ M)
    (hqb : qp.toNat + M ≤ bp.toNat) (hba : bp.toNat + N ≤ ap.toNat)
    (has : ap.toNat + N + M ≤ sp.toNat) (hsz : sp.toNat + 12 * N + 9 ≤ W.size)
    (hda : SegDigits W ap.toNat (N + M)) (hdb : SegDigits W bp.toNat N)
    (hv1 : base ≤ 2 * W[bp.toNat + N - 1]!.toNat)
    (hlt : segVal W ap.toNat (N + M) < base ^ M * segVal W bp.toNat N) :
    (udiv t T W ap bp qp sp n MM).size = W.size ∧
    (∀ p, ¬ (ap.toNat ≤ p ∧ p < ap.toNat + N + M) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + M) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (12 * N + 9)) → (udiv t T W ap bp qp sp n MM)[p]! = W[p]!) ∧
    SegDigits (udiv t T W ap bp qp sp n MM) ap.toNat (N + M) ∧
    SegDigits (udiv t T W ap bp qp sp n MM) qp.toNat M ∧
    segVal (udiv t T W ap bp qp sp n MM) ap.toNat (N + M) =
      segVal W ap.toNat (N + M) % segVal W bp.toNat N ∧
    segVal (udiv t T W ap bp qp sp n MM) qp.toNat M =
      segVal W ap.toNat (N + M) / segVal W bp.toNat N := by
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  generalize hA : segVal W ap.toNat (N + M) = A at hlt ⊢
  generalize hB : segVal W bp.toNat N = B at hBge hBpos hlt ⊢
  -- the blocks
  obtain ⟨C, hC⟩ : ∃ C, C = (M - 1) / N := ⟨_, rfl⟩
  have hCN : C * N ≤ M - 1 := by rw [hC]; exact Nat.div_mul_le_self _ _
  have hCN2 : M - 1 < (C + 1) * N := by
    rw [hC]; have := Nat.lt_mul_div_succ (M - 1) (show 0 < N by omega); linarith [this]
  have hc : ((MM - 1) / n).toNat = C := by
    rw [UInt64.toNat_div, toNat_sub_le' (by simp; omega), hM, hN, hC]; rfl
  have hcn : ((MM - 1) / n * n).toNat = C * N := by rw [toNat_mul_lt' (by rw [hc, hN]; omega), hc, hN]
  have hM' : (MM - (MM - 1) / n * n).toNat = M - C * N := by
    rw [toNat_sub_le' (by rw [hcn]; omega), hcn, hM]
  unfold udiv
  dsimp only
  have key := loop_induction (n := (MM - 1) / n) (init := W)
    (f := fun j W => (rdiv t T W (ap + (MM - n - j * n)) bp (qp + (MM - n - j * n)) sp n n).2)
    (fun j V => UInv W ap.toNat qp.toNat sp.toNat N M A B (M - j * N) V)
    ⟨rfl, fun _ _ _ _ => rfl, hda, fun i hi => by simp at hi, by
      simp only [Nat.zero_mul, Nat.sub_zero, Nat.sub_self, segVal_zero]
      rw [Nat.div_eq_of_lt (by rw [Nat.mul_comm]; exact hlt)], by
      simp only [Nat.zero_mul, Nat.sub_zero]
      rw [hA, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact hlt)]⟩ (by
      intro j V hj hinv
      rw [hc] at hj
      have hjN : j * N + N ≤ C * N := by
        have := Nat.mul_le_mul_right N (show j + 1 ≤ C by omega); rw [Nat.add_mul] at this; omega
      have hCle : C ≤ C * N := Nat.le_mul_of_pos_right _ (by omega)
      have hjj : (UInt64.ofNat j).toNat = j := toNat_ofNat_lt (by omega)
      have hpp : (MM - n - UInt64.ofNat j * n).toNat = M - N - j * N := by
        have : (UInt64.ofNat j * n).toNat = j * N := by
          rw [toNat_mul_lt' (by rw [hjj, hN]; omega), hjj, hN]
        rw [toNat_sub_le' (by rw [this, toNat_sub_le' (by omega), hM, hN]; omega), this,
          toNat_sub_le' (by omega), hM, hN]
      have hb := udiv_block t T W V ap bp qp sp n (MM - n - UInt64.ofNat j * n) N M A
        (M - N - j * N) hN hpp hW hn (by omega) (by omega) hqb hba has hsz hdb hv1 (by
          rw [hB, show M - N - j * N + N = M - j * N by omega]; exact hinv)
      rw [hB, show M - N - j * N = M - (j + 1) * N by rw [Nat.add_mul, Nat.one_mul]; omega] at hb
      exact hb)
  rw [hc] at key
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key
  generalize hV : LeanExe.loop ((MM - 1) / n) W (fun j W =>
    (rdiv t T W (ap + (MM - n - j * n)) bp (qp + (MM - n - j * n)) sp n n).2) = V at k1 k2 k3 k4 k5 k6 ⊢
  -- the last part
  obtain ⟨M', hM'd⟩ : ∃ M', M' = M - C * N := ⟨_, rfl⟩
  rw [← hM'd] at k2 k4 k5 k6
  have hM'1 : 1 ≤ M' := by omega
  have hM'N : M' ≤ N := by
    have : M - 1 < C * N + N := by rw [Nat.add_mul, Nat.one_mul] at hCN2; exact hCN2
    omega
  have hVc : A % (B * base ^ M') < B * base ^ M' := Nat.mod_lt _ (Nat.mul_pos hBpos (pow_pos base_pos _))
  have hVc2 : A % (B * base ^ M') < base ^ (N + M') := lt_of_lt_of_le hVc (by
    calc B * base ^ M' ≤ base ^ N * base ^ M' := Nat.mul_le_mul_right _ (le_of_lt (by
          rw [← hB]; exact segVal_lt hdb))
      _ = base ^ (N + M') := by rw [pow_add])
  have hupper : segVal V (ap.toNat + (N + M')) (M - M') = 0 :=
    segVal_high_zero (by rw [show N + M' + (M - M') = N + M by omega]; exact k3)
      (by rw [show N + M' + (M - M') = N + M by omega, k6]; exact hVc2)
  have hVlow : segVal V ap.toNat (N + M') = A % (B * base ^ M') := by
    rw [← k6, show N + M = N + M' + (M - M') by omega, segVal_add V ap.toNat (N + M'), hupper,
      Nat.mul_zero, Nat.add_zero]
  have hVb : ∀ i, i < N → V[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
    k2 _ (by omega) (by omega) (by omega)
  have hBV : segVal V bp.toNat N = B := by rw [← hB]; exact segVal_congr hVb
  have hv1V : base ≤ 2 * V[bp.toNat + N - 1]!.toNat := by
    rw [show bp.toNat + N - 1 = bp.toNat + (N - 1) by omega, hVb _ (by omega),
      show bp.toNat + (N - 1) = bp.toNat + N - 1 by omega]; exact hv1
  have hVlt : segVal V ap.toNat (N + M') < base ^ M' * segVal V bp.toNat N := by
    rw [hVlow, hBV, Nat.mul_comm (base ^ M') B]; exact hVc
  -- the post of the last division, whichever branch
  obtain ⟨R, hR, hpost⟩ : ∃ R : UInt64 × Array UInt64,
      (if n ≤ MM - (MM - 1) / n * n ∨ MM - (MM - 1) / n * n < T ∨ MM - (MM - 1) / n * n < 3 then
        (rdiv t T V ap bp qp sp n (MM - (MM - 1) / n * n)).2
      else (tdiv t T V ap bp qp sp n (MM - (MM - 1) / n * n)).2) = R.2 ∧
      DivPost V ap.toNat bp.toNat qp.toNat sp.toNat N M' (12 * N + 9) R := by
    by_cases hbr : n ≤ MM - (MM - 1) / n * n ∨ MM - (MM - 1) / n * n < T ∨
        MM - (MM - 1) / n * n < 3
    · refine ⟨_, by rw [if_pos hbr], ?_⟩
      have := rdiv_spec t T M' V ap bp qp sp n (MM - (MM - 1) / n * n) (by rw [hM', hM'd])
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [hN]; exact k3.mono (by omega)) (by rw [hN]; exact hdb.congr hVb) (by rw [hN]; exact hv1V)
      rw [hN] at this
      exact this.mono (by omega)
    · refine ⟨_, by rw [if_neg hbr], ?_⟩
      have hlt' : M' < N := by
        simp only [not_or, UInt64.not_le, UInt64.lt_iff_toNat_lt, hN, hM'] at hbr; omega
      have h3 : 3 ≤ M' := by
        simp only [not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, hM', UInt64.reduceToNat] at hbr
        omega
      exact tdiv_spec t T V ap bp qp sp n (MM - (MM - 1) / n * n) N M' hN (by rw [hM', hM'd])
        (by omega) (by omega) hlt' (by omega) hba (by omega) (by omega) (k3.mono (by omega))
        (hdb.congr hVb) hv1V
  rw [hR]
  have hc0 := hpost.top_zero hVlt
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := hpost
  rw [hVlow, hBV] at u6 u7
  rw [hc0, Nat.zero_mul, Nat.add_zero] at u7
  obtain ⟨b1, b2⟩ := block_step (A := A) (B := B) (L := 0) (D := A % (B * base ^ M')) (p := 0)
    (w := M') hBpos (by simp) (by simp)
  simp only [Nat.zero_add, pow_zero, Nat.mul_one, one_mul] at b1 b2
  have hRV : ∀ q, (q < ap.toNat ∨ ap.toNat + N + M' ≤ q) → (q < qp.toNat ∨ qp.toNat + M' ≤ q) →
      ¬ (sp.toNat ≤ q ∧ q < sp.toNat + (12 * N + 9)) → R.2[q]! = V[q]! :=
    fun q h1 h2 h3 => u2 q (by omega) (by omega) h3
  refine ⟨by rw [u1, k1], fun q h1 h2 h3 => by
      rw [hRV q (by omega) (by omega) h3]; exact k2 q h1 (by omega) h3,
    fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · rcases Nat.lt_or_ge i (N + M') with h | h
    · exact u3 i h
    · rw [hRV _ (by omega) (by omega) (by omega)]; exact k3 i hi
  · rcases Nat.lt_or_ge i M' with h | h
    · exact u4 i h
    · rw [hRV _ (by omega) (by omega) (by omega)]
      have := k4 (i - M') (by omega)
      rwa [show qp.toNat + M' + (i - M') = qp.toNat + i by omega] at this
  · rw [show N + M = N + M' + (M - M') by omega, segVal_add R.2 ap.toNat (N + M'), u6,
      segVal_congr (W := R.2) (W' := V) (p := ap.toNat + (N + M')) (p' := ap.toNat + (N + M'))
        fun i hi => hRV _ (by omega) (by omega) (by omega), hupper, Nat.mul_zero, Nat.add_zero, b1]
  · rw [show M = M' + (M - M') by omega, segVal_add R.2 qp.toNat M', u7,
      segVal_congr (W := R.2) (W' := V) (p := qp.toNat + M') (p' := qp.toNat + M')
        fun i hi => hRV _ (by omega) (by omega) (by omega), k5, b2]
    ring

end Library.Numerics.Bignum
