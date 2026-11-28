module

public import Library.Numerics.Bignum.Third.DivBase

@[expose] public section

/-!
The product of a quotient by the low part of the divisor, in place: `mulChunk_spec` adds the
product of the quotient `Q = Qlo + c β^ql` by one chunk of `ql` limbs to a window of the
accumulator, through Karatsuba's product of `ql` limbs and one addition of the chunk for the top
word `c`, and `mulAcc_spec` sums the chunks into the accumulator, which then holds `Q · B0`.  The
positions and lengths enter the statements as natural numbers equal to the words' values, as in
`kara_spec`, so that `omega` reads them as variables.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

theorem toNat_mul_lt' {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem toNat_sub_le' {a b : UInt64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

/-- The value of a segment with zeros above a prefix. -/
theorem segVal_pad {W : Array UInt64} {p a k : ℕ} (hz : ∀ i, i < k → W[p + a + i]! = 0) :
    segVal W p (a + k) = segVal W p a := by
  rw [segVal_add, segVal_zeros hz, Nat.mul_zero, Nat.add_zero]

set_option maxHeartbeats 1600000 in
/-- One chunk: the product of the quotient by the chunk is added to the accumulator's window. -/
theorem mulChunk_spec (t : UInt64) (W : Array UInt64) (bp k ql c ac qc j : UInt64)
    (Q J L : ℕ) (hQ : ql.toNat = Q) (hJ : j.toNat * Q = J) (hL : L = min Q (k.toNat - J))
    (hW : W.size < 2 ^ 62) (hQ1 : 1 ≤ Q) (hc : c.toNat ≤ 1)
    (hjk : J < k.toNat) (hbk : bp.toNat + k.toNat ≤ ac.toNat)
    (hac : ac.toNat + J + 2 * Q + 1 ≤ qc.toNat) (hqc : qc.toNat + 10 * Q + 1 ≤ W.size)
    (hdb : SegDigits W bp.toNat k.toNat) (hdq : SegDigits W qc.toNat Q)
    (hdw : SegDigits W (ac.toNat + J) (2 * Q + 1))
    (hlt : segVal W (ac.toNat + J) (2 * Q + 1) +
        (segVal W qc.toNat Q + c.toNat * base ^ Q) * segVal W (bp.toNat + J) L <
        base ^ (2 * Q + 1)) :
    (mulChunk t W bp k ql c ac qc j).size = W.size ∧
    (∀ q, ¬ (ac.toNat + J ≤ q ∧ q < ac.toNat + J + 2 * Q + 1) →
      ¬ (qc.toNat + Q ≤ q ∧ q < qc.toNat + 10 * Q + 1) →
      (mulChunk t W bp k ql c ac qc j)[q]! = W[q]!) ∧
    SegDigits (mulChunk t W bp k ql c ac qc j) (ac.toNat + J) (2 * Q + 1) ∧
    segVal (mulChunk t W bp k ql c ac qc j) (ac.toNat + J) (2 * Q + 1) =
      segVal W (ac.toNat + J) (2 * Q + 1) +
        (segVal W qc.toNat Q + c.toNat * base ^ Q) * segVal W (bp.toNat + J) L := by
  have hb := base_eq
  have hjq : (j * ql).toNat = J := by rw [toNat_mul_lt' (by rw [hQ]; omega), hQ, hJ]
  have hkj : (k - j * ql).toNat = k.toNat - J := by rw [toNat_sub_le' (by omega), hjq]
  have hlen : (if k - j * ql < ql then k - j * ql else ql).toNat = L := by
    split
    · rename_i h; rw [UInt64.lt_iff_toNat_lt, hkj, hQ] at h; rw [hkj]; omega
    · rename_i h; rw [UInt64.lt_iff_toNat_lt, hkj, hQ] at h; omega
  have hL1 : 1 ≤ L := by omega
  have hLQ : L ≤ Q := by omega
  have hbj : (bp + j * ql).toNat = bp.toNat + J := by rw [toNat_add_lt] <;> omega
  have hq1 : (qc + ql).toNat = qc.toNat + Q := by rw [toNat_add_lt] <;> omega
  have hm2 : (2 * ql).toNat = 2 * Q := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have hm3 : (3 * ql).toNat = 3 * Q := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have hm4 : (4 * ql).toNat = 4 * Q := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have hq2 : (qc + 2 * ql).toNat = qc.toNat + 2 * Q := by rw [toNat_add_lt] <;> omega
  have hq3 : (qc + 3 * ql).toNat = qc.toNat + 3 * Q := by rw [toNat_add_lt] <;> omega
  have hq4 : (qc + 4 * ql).toNat = qc.toNat + 4 * Q := by rw [toNat_add_lt] <;> omega
  have hq41 : (qc + 4 * ql + 1).toNat = qc.toNat + 4 * Q + 1 := by
    rw [toNat_add_lt, hq4] <;> simp <;> omega
  have hacj : (ac + j * ql).toNat = ac.toNat + J := by rw [toNat_add_lt] <;> omega
  have h2q1 : (2 * ql + 1).toNat = 2 * Q + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  have hql1 : (ql + 1).toNat = Q + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  unfold mulChunk
  dsimp only
  generalize hlenw : (if k - j * ql < ql then k - j * ql else ql) = len at hlen
  -- the copy of the chunk
  obtain ⟨c1, c2, c3, c4⟩ := addGen_copy W (bp + j * ql) (bp + j * ql) (qc + ql) len (by omega)
    (by rw [hbj, hlen]; omega) (by rw [hbj]; omega) (by rw [hq1, hlen]; omega)
    (by rw [hbj, hlen]; exact fun i hi => by rw [Nat.add_assoc]; exact hdb (J + i) (by omega))
    (by rw [hq1, hbj, hlen]; omega)
  rw [hq1, hlen] at c2 c3 c4
  rw [hbj] at c4
  generalize hW1 : (addGen W (bp + j * ql) (bp + j * ql) 0 (qc + ql) len).2 = W1 at c1 c2 c3 c4
  -- the padding
  have hlq : (ql - len).toNat = Q - L := by rw [toNat_sub_le' (by omega), hlen, hQ]
  have hpz : (qc + ql + len).toNat = qc.toNat + Q + L := by
    rw [toNat_add_lt, hq1, hlen] <;> omega
  obtain ⟨z1, z2, z3⟩ := clear_spec W1 (qc + ql + len) (ql - len) (by omega)
    (by rw [hpz, hlq]; omega)
  rw [hpz, hlq] at z2 z3
  generalize hW2 : (LeanExe.loop (ql - len) W1 fun i W => W.set! (qc + ql + len + i).toNat 0) =
    W2 at z1 z2 z3
  have h2W : ∀ q, (q < qc.toNat + Q ∨ qc.toNat + 2 * Q ≤ q) → W2[q]! = W[q]! := fun q hq => by
    rw [z2 q (by omega), c2 q (by omega)]
  have hB2 : segVal W2 (qc.toNat + Q) Q = segVal W (bp.toNat + J) L := by
    rw [show Q = L + (Q - L) by omega, segVal_pad (fun i hi => by
      have := z3 i hi; rwa [show qc.toNat + Q + L + i = qc.toNat + (L + (Q - L)) + L + i by omega]
        at this), ← c4]
    exact segVal_congr fun i hi => by rw [show L + (Q - L) = Q by omega]; exact z2 _ (by omega)
  have hdB2 : SegDigits W2 (qc.toNat + Q) Q := fun i hi => by
    by_cases hiL : i < L
    · rw [z2 _ (by omega)]; exact c3 i hiL
    · have := z3 (i - L) (by omega)
      rw [show qc.toNat + Q + L + (i - L) = qc.toNat + Q + i by omega] at this
      rw [this]; exact base_pos
  have hdQ2 : SegDigits W2 qc.toNat Q := fun i hi => by rw [h2W _ (by omega)]; exact hdq i hi
  have hQ2 : segVal W2 qc.toNat Q = segVal W qc.toNat Q :=
    segVal_congr fun i hi => h2W _ (by omega)
  -- Karatsuba's product of the copy of `Q` and the chunk
  obtain ⟨k1, k2, k3, k4⟩ := kara_spec t Q W2 qc (qc + ql) (qc + 2 * ql) (qc + 4 * ql + 1) ql hQ
    (by omega) (by rw [hq2]; omega) (by rw [hq1, hq2]; omega) (by rw [hq2, hq41]; omega)
    (by rw [hq41]; omega) hdQ2 (by rw [hq1]; exact hdB2)
  simp only [hq1, hq2, hq41] at k2 k3 k4
  rw [hQ2, hB2] at k4
  generalize hW3 : kara t W2 qc (qc + ql) (qc + 2 * ql) (qc + 4 * ql + 1) ql = W3 at k1 k2 k3 k4
  have h3W : ∀ q, ¬ (qc.toNat + 2 * Q ≤ q ∧ q < qc.toNat + 2 * Q + 2 * Q) →
      ¬ (qc.toNat + 4 * Q + 1 ≤ q ∧ q < qc.toNat + 4 * Q + 1 + 6 * Q) → W3[q]! = W2[q]! := k2
  -- the top word of the product
  rw [hq4]
  generalize hW4 : W3.set! (qc.toNat + 4 * Q) 0 = W4
  have hin4 : qc.toNat + 4 * Q < W3.size := by omega
  have hget4 := fun q => get_set W3 (qc.toNat + 4 * Q) 0 q hin4
  rw [hW4] at hget4
  have h4s : W4.size = W.size := by rw [← hW4]; simp [k1, z1, c1]
  have hP4 : segVal W4 (qc.toNat + 2 * Q) (2 * Q + 1) =
      segVal W qc.toNat Q * segVal W (bp.toNat + J) L := by
    rw [segVal_succ, hget4, if_pos (by omega), ← k4]
    simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    exact segVal_congr fun i hi => by rw [hget4, if_neg (by omega)]
  have hdP4 : SegDigits W4 (qc.toNat + 2 * Q) (2 * Q + 1) := fun i hi => by
    rw [hget4]; split
    · exact base_pos
    · exact k3 i (by omega)
  have h4W : ∀ q, q ≠ qc.toNat + 4 * Q → W4[q]! = W3[q]! := fun q hq => by
    rw [hget4, if_neg hq]
  have hC4 : ∀ i, i < L → W4[qc.toNat + Q + i]! = W2[qc.toNat + Q + i]! := fun i hi => by
    rw [h4W _ (by omega), h3W _ (by omega) (by omega)]
  -- the top word `c` of the quotient
  have hQl := segVal_lt hdq
  have hCl : segVal W (bp.toNat + J) L < base ^ Q := by
    rw [← c4]
    exact lt_of_lt_of_le (segVal_lt c3) (Nat.pow_le_pow_right base_pos hLQ)
  obtain ⟨W5, hW5, h5s, h5W, hdP5, hP5⟩ : ∃ W5 : Array UInt64,
      (if c == 1 then (addGen W4 (qc + 3 * ql) (qc + ql) len (qc + 3 * ql) (ql + 1)).2 else W4)
        = W5 ∧ W5.size = W.size ∧
      (∀ q, (q < qc.toNat + 2 * Q ∨ qc.toNat + 4 * Q + 1 ≤ q) → W5[q]! = W4[q]!) ∧
      SegDigits W5 (qc.toNat + 2 * Q) (2 * Q + 1) ∧
      segVal W5 (qc.toNat + 2 * Q) (2 * Q + 1) =
        (segVal W qc.toNat Q + c.toNat * base ^ Q) * segVal W (bp.toNat + J) L := by
    by_cases hc1 : c = 1
    · have hc1' : c.toNat = 1 := by rw [hc1]; rfl
      have hd3 : SegDigits W4 (qc.toNat + 3 * Q) (Q + 1) := fun i hi => by
        have := hdP4 (Q + i) (by omega)
        rwa [show qc.toNat + 2 * Q + (Q + i) = qc.toNat + 3 * Q + i by omega] at this
      have hdC : SegDigits W4 (qc.toNat + Q) L := fun i hi => by
        rw [hC4 i hi, z2 _ (by omega)]; exact c3 i hi
      obtain ⟨a1, a2, a3, a4, a5⟩ := addGen_inplace W4 (qc + 3 * ql) (qc + ql) len (ql + 1)
        (by omega) (by rw [hq3, hql1]; omega) (by rw [hq1, hlen, hql1]; omega)
        (by rw [hq3, hql1]; exact hd3)
        (by rw [hq1, hlen, hql1, show min L (Q + 1) = L by omega]; exact hdC)
        (by rw [hq1, hq3, hlen, hql1]; omega)
      rw [hq3, hql1, hq1, hlen, show min L (Q + 1) = L by omega] at a5
      rw [hq3, hql1] at a2 a3
      have hCv : segVal W4 (qc.toNat + Q) L = segVal W (bp.toNat + J) L := by
        rw [← c4]; exact segVal_congr fun i hi => by rw [hC4 i hi, z2 _ (by omega)]
      rw [hCv] at a5
      generalize hA : addGen W4 (qc + 3 * ql) (qc + ql) len (qc + 3 * ql) (ql + 1) = A at a1 a2 a3 a4 a5
      refine ⟨_, by rw [if_pos (by rw [hc1]; rfl)], by rw [a1, h4s],
        fun q hq => a2 q (by omega), ?_, ?_⟩
      · intro i hi
        by_cases hi' : i < Q
        · rw [a2 _ (by omega)]; exact hdP4 i hi
        · have := a3 (i - Q) (by omega)
          rwa [show qc.toNat + 3 * Q + (i - Q) = qc.toNat + 2 * Q + i by omega] at this
      · -- the value, with no carry out
        have hsplit : ∀ V : Array UInt64, segVal V (qc.toNat + 2 * Q) (2 * Q + 1) =
            segVal V (qc.toNat + 2 * Q) Q + base ^ Q * segVal V (qc.toNat + 3 * Q) (Q + 1) :=
          fun V => by
            rw [show 2 * Q + 1 = Q + (Q + 1) by omega, segVal_add,
              show qc.toNat + 2 * Q + Q = qc.toNat + 3 * Q by omega]
        have hlo : segVal A.2 (qc.toNat + 2 * Q) Q = segVal W4 (qc.toNat + 2 * Q) Q :=
          segVal_congr fun i hi => a2 _ (by omega)
        have ha3 := segVal_lt a3
        have hP4s := hsplit W4
        rw [hP4] at hP4s
        rw [hc1', Nat.one_mul]
        generalize hQv : segVal W qc.toNat Q = Qv at hP4s hQl ⊢
        generalize hCv' : segVal W (bp.toNat + J) L = Cv at hP4s hCl a5 ⊢
        generalize hT : segVal W4 (qc.toNat + 3 * Q) (Q + 1) = Tv at hP4s a5
        generalize hT' : segVal A.2 (qc.toNat + 3 * Q) (Q + 1) = Tv' at ha3 a5 ⊢
        generalize hLo : segVal W4 (qc.toNat + 2 * Q) Q = Lo at hP4s hlo
        have hprod : (Qv + base ^ Q) * Cv < base ^ (2 * Q + 1) := by
          calc (Qv + base ^ Q) * Cv ≤ (2 * base ^ Q) * Cv := Nat.mul_le_mul_right _ (by omega)
            _ < (2 * base ^ Q) * base ^ Q :=
                Nat.mul_lt_mul_of_pos_left hCl (Nat.mul_pos (by norm_num) (pow_pos base_pos _))
            _ ≤ base * base ^ Q * base ^ Q := by
                apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; rw [hb]; norm_num
            _ = base ^ (2 * Q + 1) := by ring
        have h2 : base ^ Q * base ^ (Q + 1) = base ^ (2 * Q + 1) := by
          rw [← pow_add, show Q + (Q + 1) = 2 * Q + 1 by omega]
        have h5 : base ^ Q * (Tv + Cv) = base ^ Q * Tv + base ^ Q * Cv := Nat.mul_add _ _ _
        have h6 : (Qv + base ^ Q) * Cv = Qv * Cv + base ^ Q * Cv := Nat.add_mul _ _ _
        have hcar : A.1.toNat = 0 := by
          by_contra hne
          have h1 : base ^ (Q + 1) ≤ A.1.toNat * base ^ (Q + 1) :=
            Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
          have h3 : base ^ Q * base ^ (Q + 1) ≤ base ^ Q * (Tv + Cv) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        rw [hcar, Nat.zero_mul, Nat.add_zero] at a5
        rw [hsplit, hlo, hT', a5, h5, h6, hP4s]
        ring
    · have hc0 : c.toNat = 0 := by
        have : c.toNat ≠ 1 := fun h => hc1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
        omega
      refine ⟨W4, by rw [if_neg (by intro h; exact hc1 (by simpa using h))], h4s,
        fun _ _ => rfl, hdP4, ?_⟩
      rw [hP4, hc0]; ring
  -- the addition to the accumulator's window
  have hw5 : ∀ i, i < 2 * Q + 1 → W5[ac.toNat + J + i]! = W[ac.toNat + J + i]! := fun i hi => by
    have q1 : ac.toNat + J + i < qc.toNat + 2 * Q := by omega
    rw [h5W (ac.toNat + J + i) (Or.inl q1), h4W (ac.toNat + J + i) (by omega),
      h3W (ac.toNat + J + i) (by omega) (by omega), h2W (ac.toNat + J + i) (by omega)]
  obtain ⟨e1, e2, e3, e4, e5⟩ := addGen_inplace W5 (ac + j * ql) (qc + 2 * ql) (2 * ql + 1)
    (2 * ql + 1) (by omega) (by rw [hacj, h2q1]; omega) (by rw [hq2, h2q1]; omega)
    (by rw [hacj, h2q1]; exact hdw.congr hw5) (by rw [hq2, h2q1, min_self]; exact hdP5)
    (by rw [hacj, hq2, h2q1, min_self]; omega)
  rw [hacj, hq2, h2q1, min_self, hP5, segVal_congr hw5] at e5
  rw [hacj, h2q1] at e2 e3
  have hcar : (addGen W5 (ac + j * ql) (qc + 2 * ql) (2 * ql + 1) (ac + j * ql)
      (2 * ql + 1)).1.toNat = 0 := by
    by_contra hne
    have : base ^ (2 * Q + 1) ≤ (addGen W5 (ac + j * ql) (qc + 2 * ql) (2 * ql + 1)
        (ac + j * ql) (2 * ql + 1)).1.toNat * base ^ (2 * Q + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  rw [hcar, Nat.zero_mul, Nat.add_zero] at e5
  rw [hW5]
  refine ⟨by rw [e1, h5s], fun q hq1 hq2 => ?_, e3, e5⟩
  rw [e2 q (by omega), h5W q (by omega), h4W q (by omega), h3W q (by omega) (by omega),
    h2W q (by omega)]

/-- A segment's value split at `a`: the window of `w` limbs from `a` and the rest above it. -/
theorem segVal_window (W : Array UInt64) (p a w r : ℕ) :
    segVal W p (a + w + r) =
      segVal W p a + base ^ a * segVal W (p + a) w + base ^ (a + w) * segVal W (p + a + w) r := by
  rw [segVal_add W p (a + w) r, segVal_add W p a w, Nat.add_assoc p a w]

/-- The count of chunks `⌈K / Q⌉`. -/
theorem ceil_div_facts {K Q : ℕ} (hQ : 1 ≤ Q) (hK : 1 ≤ K) :
    ((K + Q - 1) / Q - 1) * Q < K ∧ K ≤ (K + Q - 1) / Q * Q ∧ 1 ≤ (K + Q - 1) / Q := by
  have h1 := Nat.div_add_mod (K + Q - 1) Q
  have h2 := Nat.mod_lt (K + Q - 1) (show 0 < Q by omega)
  generalize (K + Q - 1) / Q = NC at h1 ⊢
  generalize (K + Q - 1) % Q = r at h1 h2
  rw [Nat.mul_comm] at h1
  rcases Nat.eq_zero_or_pos NC with h0 | hpos
  · subst h0; simp at h1; omega
  · have hm : (NC - 1) * Q + Q = NC * Q := by
      rw [Nat.sub_mul, Nat.one_mul]; have : Q ≤ NC * Q := Nat.le_mul_of_pos_left _ hpos; omega
    omega

/-- `mulAcc` writes `Q · B0` to the accumulator of `nc·ql + ql + 1` limbs at `sp + 1`, for the
quotient `Q`, the `ql ≥ 1` limbs at `qp` plus `c β^ql`, and the `k ≥ 1` limbs `B0` at `bp`, both
below `sp`, and it changes no word outside the `nc·ql + 11 ql + 2` words from `sp + 1`. -/
theorem mulAcc_spec (t : UInt64) (W : Array UInt64) (bp k qp ql c sp : UInt64)
    (Q K NC AL : ℕ) (hQ : ql.toNat = Q) (hK : k.toNat = K) (hNC : NC = (K + Q - 1) / Q)
    (hAL : AL = NC * Q + Q + 1)
    (hW : W.size < 2 ^ 62) (hQ1 : 1 ≤ Q) (hK1 : 1 ≤ K) (hc : c.toNat ≤ 1)
    (hbs : bp.toNat + K ≤ sp.toNat) (hqs : qp.toNat + Q ≤ sp.toNat)
    (hsz : sp.toNat + 1 + AL + 10 * Q + 1 ≤ W.size)
    (hdb : SegDigits W bp.toNat K) (hdq : SegDigits W qp.toNat Q) :
    (mulAcc t W bp k qp ql c sp).size = W.size ∧
    (∀ q, ¬ (sp.toNat + 1 ≤ q ∧ q < sp.toNat + 1 + AL + 10 * Q + 1) →
      (mulAcc t W bp k qp ql c sp)[q]! = W[q]!) ∧
    SegDigits (mulAcc t W bp k qp ql c sp) (sp.toNat + 1) AL ∧
    segVal (mulAcc t W bp k qp ql c sp) (sp.toNat + 1) AL =
      (segVal W qp.toNat Q + c.toNat * base ^ Q) * segVal W bp.toNat K := by
  have hb := base_eq
  have hNCQ := ceil_div_facts hQ1 hK1
  rw [← hNC] at hNCQ
  obtain ⟨hNC1, hNC2, hNC3⟩ := hNCQ
  have hnc : ((k + ql - 1) / ql).toNat = NC := by
    rw [UInt64.toNat_div, toNat_sub_le' (by rw [toNat_add_lt] <;> simp <;> omega),
      toNat_add_lt (by omega), hQ, hK, hNC]; rfl
  have hm : ((k + ql - 1) / ql * ql).toNat = NC * Q := by
    rw [toNat_mul_lt' (by rw [hnc, hQ]; omega), hnc, hQ]
  have hm1 : ((k + ql - 1) / ql * ql + ql).toNat = NC * Q + Q := by
    rw [toNat_add_lt (by rw [hm, hQ]; omega), hm, hQ]
  have hncq : ((k + ql - 1) / ql * ql + ql + 1).toNat = AL := by
    rw [toNat_add_lt (by rw [hm1]; simp; omega), hm1]; simp; omega
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  have hqc : (sp + 1 + (k + ql - 1) / ql * ql + ql + 1).toNat = sp.toNat + 1 + AL := by
    have : (sp + 1 + (k + ql - 1) / ql * ql + ql + 1) = (sp + 1) +
        ((k + ql - 1) / ql * ql + ql + 1) := by ac_rfl
    rw [this, toNat_add_lt (by rw [hs1, hncq]; omega), hs1, hncq]
  unfold mulAcc
  dsimp only
  generalize hQCw : sp + 1 + (k + ql - 1) / ql * ql + ql + 1 = qc at hqc
  -- the cleared accumulator
  have hclr : (sp + 1 + 0) = sp + 1 := by simp
  obtain ⟨z1, z2, z3⟩ := clear_spec W (sp + 1) ((k + ql - 1) / ql * ql + ql + 1) (by omega)
    (by rw [hs1, hncq]; omega)
  rw [hs1, hncq] at z2 z3
  generalize hW1 : (LeanExe.loop ((k + ql - 1) / ql * ql + ql + 1) W fun i W =>
    W.set! (sp + 1 + i).toNat 0) = W1 at z1 z2 z3
  -- the copy of the quotient
  have hdq1 : SegDigits W1 qp.toNat Q := hdq.congr fun i hi => z2 _ (by omega)
  obtain ⟨c1, c2, c3, c4⟩ := addGen_copy W1 qp qp qc ql (by omega) (by rw [hQ]; omega)
    (by omega) (by rw [hqc, hQ]; omega) (by rw [hQ]; exact hdq1) (by rw [hqc, hQ]; omega)
  rw [hqc, hQ] at c2 c3 c4
  rw [segVal_congr (W := W1) (W' := W) (p := qp.toNat) (p' := qp.toNat) fun i hi =>
    z2 _ (by omega)] at c4
  generalize hW2 : (addGen W1 qp qp 0 qc ql).2 = W2 at c1 c2 c3 c4
  -- the loop of chunks
  generalize hQv : segVal W qp.toNat Q + c.toNat * base ^ Q = Qf
  have hQl := segVal_lt hdq
  have hQf : Qf < 2 * base ^ Q := by
    rw [← hQv]; have : c.toNat * base ^ Q ≤ 1 * base ^ Q := Nat.mul_le_mul_right _ hc; omega
  have hNCle : NC ≤ NC * Q := Nat.le_mul_of_pos_right _ (by omega)
  have key := loop_induction (n := (k + ql - 1) / ql) (init := W2)
    (f := fun j W => mulChunk t W bp k ql c (sp + 1) qc j)
    (fun j V => V.size = W.size ∧
      (∀ q, ¬ (sp.toNat + 1 ≤ q ∧ q < sp.toNat + 1 + AL + 10 * Q + 1) → V[q]! = W[q]!) ∧
      (∀ i, i < Q → V[sp.toNat + 1 + AL + i]! = W2[sp.toNat + 1 + AL + i]!) ∧
      SegDigits V (sp.toNat + 1) AL ∧
      segVal V (sp.toNat + 1) AL = Qf * segVal W bp.toNat (min (j * Q) K))
    ⟨by rw [c1, z1], fun q hq => by rw [c2 q (by omega), z2 q (by omega)], fun _ _ => rfl,
      fun i hi => by rw [c2 _ (by omega), z3 i hi]; exact base_pos, by
        rw [Nat.zero_mul, Nat.zero_min, segVal_zero, Nat.mul_zero]
        exact (segVal_congr fun i hi => by rw [c2 _ (by omega)]).trans
          (segVal_zeros fun i hi => z3 i hi)⟩ (by
      intro j V hj ⟨v1, v2, v3, v4, v5⟩
      rw [hnc] at hj
      have hj1 : (j + 1) * Q ≤ NC * Q := Nat.mul_le_mul_right _ (by omega)
      have hjQ' : j * Q + Q = (j + 1) * Q := by ring
      have hjQ : j * Q < K := by
        have : j * Q ≤ (NC - 1) * Q := Nat.mul_le_mul_right _ (by omega)
        omega
      have hjj : (UInt64.ofNat j).toNat * Q = j * Q := by rw [toNat_ofNat_lt (by omega)]
      have hVb : ∀ i, i < K → V[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi => v2 _ (by omega)
      have hVq : ∀ i, i < Q → V[sp.toNat + 1 + AL + i]! = W2[sp.toNat + 1 + AL + i]! := v3
      have hQfV : segVal V (sp.toNat + 1 + AL) Q + c.toNat * base ^ Q = Qf := by
        rw [segVal_congr hVq, c4, hQv]
      obtain ⟨L, hL⟩ : ∃ L, L = min Q (k.toNat - j * Q) := ⟨_, rfl⟩
      have hLK : j * Q + L = min ((j + 1) * Q) K := by rw [hL, hK]; omega
      -- the window of the accumulator before this chunk
      have hsplitV := segVal_window V (sp.toNat + 1) (j * Q) (2 * Q + 1) (AL - (j * Q) - (2 * Q + 1))
      rw [show j * Q + (2 * Q + 1) + (AL - j * Q - (2 * Q + 1)) = AL by omega, v5,
        show min (j * Q) K = j * Q by omega] at hsplitV
      have hB0 := segVal_lt (hdb.mono (k' := j * Q) (by omega))
      have hwin : segVal V (sp.toNat + 1 + j * Q) (2 * Q + 1) < 2 * base ^ Q := by
        have h1 : base ^ (j * Q) * segVal V (sp.toNat + 1 + j * Q) (2 * Q + 1) <
            base ^ (j * Q) * (2 * base ^ Q) := by
          calc base ^ (j * Q) * segVal V (sp.toNat + 1 + j * Q) (2 * Q + 1)
              ≤ Qf * segVal W bp.toNat (j * Q) := by rw [hsplitV]; omega
            _ < 2 * base ^ Q * base ^ (j * Q) := by
                rcases Nat.eq_zero_or_pos Qf with h0 | hpos
                · rw [h0, Nat.zero_mul]; exact Nat.mul_pos (Nat.mul_pos (by norm_num)
                    (pow_pos base_pos _)) (pow_pos base_pos _)
                · calc Qf * segVal W bp.toNat (j * Q) < Qf * base ^ (j * Q) :=
                        Nat.mul_lt_mul_of_pos_left hB0 hpos
                    _ ≤ 2 * base ^ Q * base ^ (j * Q) := Nat.mul_le_mul_right _ (by omega)
            _ = base ^ (j * Q) * (2 * base ^ Q) := by ring
        exact Nat.lt_of_mul_lt_mul_left h1
      have hC : segVal V (bp.toNat + j * Q) L = segVal W (bp.toNat + j * Q) L :=
        segVal_congr fun i hi => by
          rw [show bp.toNat + j * Q + i = bp.toNat + (j * Q + i) by omega, hVb _ (by omega)]
      have hCl : segVal W (bp.toNat + j * Q) L < base ^ Q :=
        lt_of_lt_of_le (segVal_lt fun i hi => by
          rw [show bp.toNat + j * Q + i = bp.toNat + (j * Q + i) by omega]
          exact hdb _ (by omega)) (Nat.pow_le_pow_right base_pos (by omega))
      have hprod : Qf * segVal W (bp.toNat + j * Q) L < 2 * (base ^ Q * base ^ Q) := by
        rcases Nat.eq_zero_or_pos Qf with h0 | hpos
        · rw [h0, Nat.zero_mul]; exact Nat.mul_pos (by norm_num)
            (Nat.mul_pos (pow_pos base_pos _) (pow_pos base_pos _))
        · calc Qf * segVal W (bp.toNat + j * Q) L < Qf * base ^ Q :=
                Nat.mul_lt_mul_of_pos_left hCl hpos
            _ ≤ 2 * base ^ Q * base ^ Q := Nat.mul_le_mul_right _ (by omega)
            _ = 2 * (base ^ Q * base ^ Q) := by ring
      have hpow : 4 * (base ^ Q * base ^ Q) ≤ base ^ (2 * Q + 1) := by
        rw [show 2 * Q + 1 = Q + Q + 1 by omega, pow_succ, pow_add]
        calc 4 * (base ^ Q * base ^ Q) ≤ base * (base ^ Q * base ^ Q) :=
              Nat.mul_le_mul_right _ (by rw [hb]; norm_num)
          _ = base ^ Q * base ^ Q * base := by ring
      have hQQ : base ^ Q ≤ base ^ Q * base ^ Q := Nat.le_mul_of_pos_right _ (pow_pos base_pos _)
      have hdwV : SegDigits V (sp.toNat + 1 + j * Q) (2 * Q + 1) := fun i hi => by
        rw [Nat.add_assoc]; exact v4 _ (by omega)
      have hdqV : SegDigits V (sp.toNat + 1 + AL) Q := fun i hi => by
        rw [hVq i hi]; exact c3 i hi
      obtain ⟨m1, m2, m3, m4⟩ := mulChunk_spec t V bp k ql c (sp + 1) qc (UInt64.ofNat j)
        Q (j * Q) L hQ hjj hL (by omega) hQ1 hc (by omega) (by rw [hs1]; omega)
        (by rw [hs1, hqc]; omega) (by rw [hqc]; omega)
        (by rw [hK]; exact hdb.congr hVb) (by rw [hqc]; exact hdqV) (by rw [hs1]; exact hdwV)
        (by rw [hs1, hqc, hQfV, hC]; omega)
      rw [hs1, hqc, hQfV, hC] at m4
      simp only [hs1, hqc] at m2 m3
      refine ⟨by rw [m1, v1], fun q hq => by rw [m2 q (by omega) (by omega), v2 q hq],
        fun i hi => by rw [m2 _ (by omega) (by omega), v3 i hi], ?_, ?_⟩
      · intro i hi
        by_cases hw : j * Q ≤ i ∧ i < j * Q + (2 * Q + 1)
        · have := m3 (i - j * Q) (by omega)
          rwa [show sp.toNat + 1 + j * Q + (i - j * Q) = sp.toNat + 1 + i by omega] at this
        · rw [m2 _ (by omega) (by omega)]; exact v4 i hi
      · have hsplitV' := segVal_window (mulChunk t V bp k ql c (sp + 1) qc (UInt64.ofNat j))
          (sp.toNat + 1) (j * Q) (2 * Q + 1) (AL - (j * Q) - (2 * Q + 1))
        rw [show j * Q + (2 * Q + 1) + (AL - j * Q - (2 * Q + 1)) = AL by omega] at hsplitV'
        rw [hsplitV', m4, ← hLK, segVal_add W bp.toNat (j * Q) L]
        have e1 : segVal (mulChunk t V bp k ql c (sp + 1) qc (UInt64.ofNat j)) (sp.toNat + 1) (j * Q)
            = segVal V (sp.toNat + 1) (j * Q) :=
          segVal_congr fun i hi => m2 _ (by omega) (by omega)
        have e2 : segVal (mulChunk t V bp k ql c (sp + 1) qc (UInt64.ofNat j))
            (sp.toNat + 1 + j * Q + (2 * Q + 1)) (AL - j * Q - (2 * Q + 1)) =
            segVal V (sp.toNat + 1 + j * Q + (2 * Q + 1)) (AL - j * Q - (2 * Q + 1)) :=
          segVal_congr fun i hi => m2 _ (by omega) (by omega)
        rw [e1, e2]
        have hsv := segVal_window V (sp.toNat + 1) (j * Q) (2 * Q + 1) (AL - (j * Q) - (2 * Q + 1))
        rw [show j * Q + (2 * Q + 1) + (AL - j * Q - (2 * Q + 1)) = AL by omega, v5,
          show min (j * Q) K = j * Q by omega] at hsv
        generalize segVal V (sp.toNat + 1 + j * Q + (2 * Q + 1)) (AL - j * Q - (2 * Q + 1)) = R
          at hsv ⊢
        generalize segVal V (sp.toNat + 1 + j * Q) (2 * Q + 1) = Wv at hsv ⊢
        generalize segVal V (sp.toNat + 1) (j * Q) = Lv at hsv ⊢
        zify at hsv ⊢
        linear_combination -hsv)
  rw [hnc] at key
  obtain ⟨r1, r2, r3, r4, r5⟩ := key
  rw [show min (NC * Q) K = K by omega] at r5
  exact ⟨r1, r2, r4, r5⟩

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- An invariant of `LeanExe.repeatWhile` indexed by the number of steps taken: when every step
from a state that meets the condition keeps it, and the condition fails at the fuel, the loop
ends at a state of the invariant whose condition fails. -/
theorem repeatWhile_count {α : Type} (fuel : UInt64) (init : α) (cond : α → Bool)
    (step : α → α) (I : ℕ → α → Prop) (h0 : I 0 init)
    (hstep : ∀ j s, j < fuel.toNat → I j s → cond s = true → I (j + 1) (step s))
    (hstop : ∀ s, I fuel.toNat s → cond s = false) :
    ∃ j, j ≤ fuel.toNat ∧ I j (LeanExe.repeatWhile fuel init cond step) ∧
      cond (LeanExe.repeatWhile fuel init cond step) = false := by
  unfold LeanExe.repeatWhile
  suffices h : ∀ f j s, j + f = fuel.toNat → I j s →
      ∃ j', j' ≤ fuel.toNat ∧ I j' (LeanExe.repeatWhile.go cond step f s) ∧
        cond (LeanExe.repeatWhile.go cond step f s) = false from h _ 0 init (by omega) h0
  intro f
  induction f with
  | zero =>
    intro j s hj hI
    exact ⟨j, by omega, hI, hstop s (by rw [← hj]; simpa using hI)⟩
  | succ f ih =>
    intro j s hj hI
    simp only [LeanExe.repeatWhile.go]
    by_cases hc : cond s = true
    · rw [if_pos hc]
      exact ih (j + 1) (step s) (by omega) (hstep j s (by omega) hI hc)
    · rw [if_neg hc]
      exact ⟨j, by omega, hI, by simpa using hc⟩

end Library.Numerics.Bignum
