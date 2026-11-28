module

public import Library.Numerics.Bignum.Third.DivTop
public import Library.Numerics.Bignum.Second.Loops
public import Library.Numerics.Bignum.Second.Read
public import Library.Numerics.Bignum.IntProof

@[expose] public section

/-!
The division of naturals and integers of the third iteration.  `divSmallSeg_spec` is the short
division of a segment by a word in place, `divSeg_spec` the division of segments with the
normalization by `2^s`, and `natDivModBZWith_eq` the equation of the natural division with the
first iteration's specification, at every threshold.  The integer divisions equal the first
iteration's, so the first iteration's theorems give their specifications.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The state of `divSmallSeg` after the top `e` limbs: those limbs hold the quotient of the
number they held by `d`, the remainder is in the state, and the limbs below are unchanged. -/
def SmallInv (W : Array UInt64) (p len d e : ℕ) (s : UInt64 × Array UInt64) : Prop :=
  s.2.size = W.size ∧ (∀ q, (q < p + len - e ∨ p + len ≤ q) → s.2[q]! = W[q]!) ∧
  SegDigits s.2 (p + len - e) e ∧
  segVal s.2 (p + len - e) e = segVal W (p + len - e) e / d ∧
  s.1.toNat = segVal W (p + len - e) e % d

/-- Short division in place: `divSmallSeg` divides the `len` limbs at `p` by `0 < d ≤ 2^32`. -/
theorem divSmallSeg_spec (W : Array UInt64) (p len d : UInt64) (hW : W.size < 2 ^ 62)
    (hd0 : 0 < d.toNat) (hd : d.toNat ≤ base) (hp : p.toNat + len.toNat ≤ W.size)
    (hdig : SegDigits W p.toNat len.toNat) :
    (divSmallSeg W p len d).2.size = W.size ∧
    (∀ q, (q < p.toNat ∨ p.toNat + len.toNat ≤ q) → (divSmallSeg W p len d).2[q]! = W[q]!) ∧
    SegDigits (divSmallSeg W p len d).2 p.toNat len.toNat ∧
    segVal (divSmallSeg W p len d).2 p.toNat len.toNat = segVal W p.toNat len.toNat / d.toNat ∧
    (divSmallSeg W p len d).1.toNat = segVal W p.toNat len.toNat % d.toNat := by
  have hb := base_eq
  have key := loop_induction (n := len) (init := ((0 : UInt64), W))
    (f := fun e s => ((s.1 * 4294967296 + s.2[(p + len - 1 - e).toNat]!) % d,
      s.2.set! (p + len - 1 - e).toNat ((s.1 * 4294967296 + s.2[(p + len - 1 - e).toNat]!) / d)))
    (SmallInv W p.toNat len.toNat d.toNat)
    ⟨rfl, fun _ _ => rfl, fun i hi => by omega, by simp [segVal], by simp [segVal]⟩ (by
      intro e s he ⟨s1, s2, s3, s4, s5⟩
      have hee : (UInt64.ofNat e).toNat = e := toNat_ofNat_lt (by omega)
      have hq : (p + len - 1 - UInt64.ofNat e).toNat = p.toNat + len.toNat - 1 - e := by
        rw [toNat_sub_le' (by rw [hee, toNat_sub_le' (by rw [toNat_add_lt (by omega)]; simp; omega),
          toNat_add_lt (by omega)]; simp; omega), hee, toNat_sub_le' (by
            rw [toNat_add_lt (by omega)]; simp; omega), toNat_add_lt (by omega)]
        simp
      rw [hq]
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = p.toNat + len.toNat - 1 - e := ⟨_, rfl⟩
      rw [← hQ]
      have hQe : Q + 1 = p.toNat + len.toNat - e := by omega
      have hsQ : s.2[Q]! = W[Q]! := s2 Q (by omega)
      have hwQ : W[Q]!.toNat < base := by
        have := hdig (Q - p.toNat) (by omega); rwa [show p.toNat + (Q - p.toNat) = Q by omega] at this
      have hrem : s.1.toNat < d.toNat := by rw [s5]; exact Nat.mod_lt _ hd0
      have hx : (s.1 * 4294967296 + s.2[Q]!).toNat = s.1.toNat * base + W[Q]!.toNat := by
        have h0 : s.1.toNat ≤ 4294967295 := by rw [hb] at hd; omega
        have h1 : (s.1 * 4294967296).toNat = s.1.toNat * 4294967296 :=
          toNat_mul_lt' (by simp only [UInt64.reduceToNat]; omega)
        have h2 : W[Q]!.toNat < 4294967296 := by rw [hb] at hwQ; exact hwQ
        rw [toNat_add_lt (by rw [h1, hsQ]; omega), h1, hsQ, hb]
      generalize hX : s.1 * 4294967296 + s.2[Q]! = X at hx
      have hT := segVal_lt s3
      generalize hTv : segVal W (p.toNat + len.toNat - e) e = Tv at s4 s5
      -- the step of the short division
      obtain ⟨d1, d2⟩ := div_step (H := Tv) (b := base) (x := W[Q]!.toNat) hd0
      have hXd : X.toNat / d.toNat < base := by
        rw [hx, Nat.div_lt_iff_lt_mul hd0]
        calc s.1.toNat * base + W[Q]!.toNat < s.1.toNat * base + base := by omega
          _ = (s.1.toNat + 1) * base := by ring
          _ ≤ d.toNat * base := Nat.mul_le_mul_right _ hrem
          _ = base * d.toNat := by ring
      have hin : Q < s.2.size := by omega
      have hget := fun q => get_set s.2 Q (X / d) q hin
      have hW1 : segVal W Q (e + 1) = W[Q]!.toNat + base * Tv := by
        rw [show e + 1 = 1 + e by omega, segVal_add, ← hTv, hQe]
        simp [segVal]
      refine ⟨by simp [s1], fun q hq => ?_, fun i hi => ?_, ?_, ?_⟩
      · rw [hget, if_neg (by omega)]; exact s2 q (by omega)
      · rw [show p.toNat + len.toNat - (e + 1) = Q by omega, hget]
        split
        · rw [UInt64.toNat_div]; exact hXd
        · have := s3 (i - 1) (by omega)
          rwa [show p.toNat + len.toNat - e + (i - 1) = Q + i by omega] at this
      · rw [show p.toNat + len.toNat - (e + 1) = Q by omega, hW1, show e + 1 = 1 + e by omega,
          segVal_add]
        have h1 : segVal (s.2.set! Q (X / d)) Q 1 = (X / d).toNat := by
          simp only [segVal, Nat.add_zero, pow_zero, Nat.mul_one, Nat.zero_add]
          rw [hget, if_pos rfl]
        have h2 : segVal (s.2.set! Q (X / d)) (Q + 1) e = Tv / d.toNat := by
          rw [← s4, hQe]; exact segVal_congr fun i hi => by rw [hget, if_neg (by omega)]
        rw [h1, h2, UInt64.toNat_div, hx, pow_one,
          show W[Q]!.toNat + base * Tv = Tv * base + W[Q]!.toNat by ring, d1, ← s5]
        ring
      · rw [show p.toNat + len.toNat - (e + 1) = Q by omega, hW1, UInt64.toNat_mod, hx,
          show W[Q]!.toNat + base * Tv = Tv * base + W[Q]!.toNat by ring, d2, ← s5])
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  rw [show p.toNat + len.toNat - len.toNat = p.toNat by omega] at k2 k3 k4 k5
  exact ⟨k1, fun q hq => k2 q (by omega), k3, k4, k5⟩

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

set_option maxHeartbeats 4000000 in
/-- `divSeg` divides the `lx` limbs `X` at `xp` by the `n ≥ 2` limbs `D` at `dp`, whose top limb
is not 0, for `n ≤ lx`: the `lx + 1 - n` limbs at `qp` receive `X / D`, the segment at `xp` holds
`X % D`, and every word outside those, and outside the `13 n + lx + 10` words of scratch at `sp`,
keeps its value. -/
theorem divSeg_spec (t T : UInt64) (W : Array UInt64) (xp lx dp n qp sp : UInt64) (N LX : ℕ)
    (hN : n.toNat = N) (hLX : lx.toNat = LX) (hW : W.size < 2 ^ 62) (hn : 2 ≤ N) (hNL : N ≤ LX)
    (hxq : xp.toNat + LX ≤ qp.toNat) (hdq : dp.toNat + N ≤ qp.toNat)
    (hqs : qp.toNat + (LX + 1 - N) ≤ sp.toNat) (hsz : sp.toNat + 13 * N + LX + 10 ≤ W.size)
    (hdx : SegDigits W xp.toNat LX) (hdd : SegDigits W dp.toNat N)
    (htop : W[dp.toNat + N - 1]! ≠ 0) :
    (divSeg t T W xp lx dp n qp sp).size = W.size ∧
    (∀ p, ¬ (xp.toNat ≤ p ∧ p < xp.toNat + LX) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + (LX + 1 - N)) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (13 * N + LX + 10)) → (divSeg t T W xp lx dp n qp sp)[p]! = W[p]!) ∧
    SegDigits (divSeg t T W xp lx dp n qp sp) xp.toNat LX ∧
    SegDigits (divSeg t T W xp lx dp n qp sp) qp.toNat (LX + 1 - N) ∧
    segVal (divSeg t T W xp lx dp n qp sp) xp.toNat LX = segVal W xp.toNat LX % segVal W dp.toNat N ∧
    segVal (divSeg t T W xp lx dp n qp sp) qp.toNat (LX + 1 - N) =
      segVal W xp.toNat LX / segVal W dp.toNat N := by
  have hb := base_eq
  have hb0 := base_pos
  generalize hX : segVal W xp.toNat LX = X
  generalize hD : segVal W dp.toNat N = D
  have hXlt : X < base ^ LX := by rw [← hX]; exact segVal_lt hdx
  -- the shift
  have hdn1 : (dp + n - 1).toNat = dp.toNat + N - 1 := by
    rw [toNat_sub_le' (by rw [toNat_add_lt (by omega)]; simp; omega), toNat_add_lt (by omega), hN]
    simp
  have htop0 : 0 < W[dp.toNat + N - 1]!.toNat := by
    rcases Nat.eq_zero_or_pos W[dp.toNat + N - 1]!.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) htop
    · exact h
  have htopb : W[dp.toNat + N - 1]!.toNat < base := by
    have := hdd (N - 1) (by omega); rwa [show dp.toNat + (N - 1) = dp.toNat + N - 1 by omega] at this
  obtain ⟨hd0, hdb, hdn, hdu⟩ := normalize W[dp.toNat + N - 1]! htop0 htopb
  unfold divSeg
  rw [hdn1]
  generalize hdw : (1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits
    W[dp.toNat + N - 1]!) = d at hd0 hdb hdn hdu
  dsimp only
  -- `D` and its normalized form `D · d`
  have hDsplit : D = segVal W dp.toNat (N - 1) + base ^ (N - 1) * W[dp.toNat + N - 1]!.toNat := by
    have := segVal_succ W dp.toNat (N - 1)
    rw [show N - 1 + 1 = N by omega, show dp.toNat + (N - 1) = dp.toNat + N - 1 by omega] at this
    rw [← hD, this]; ring
  have hDl := segVal_lt (hdd.mono (k' := N - 1) (by omega))
  have hDd : D * d.toNat < base ^ N := by
    rw [hDsplit]
    calc (segVal W dp.toNat (N - 1) + base ^ (N - 1) * W[dp.toNat + N - 1]!.toNat) * d.toNat
        < (base ^ (N - 1) + base ^ (N - 1) * W[dp.toNat + N - 1]!.toNat) * d.toNat :=
          Nat.mul_lt_mul_of_pos_right (by omega) hd0
      _ = base ^ (N - 1) * ((W[dp.toNat + N - 1]!.toNat + 1) * d.toNat) := by ring
      _ ≤ base ^ (N - 1) * base := Nat.mul_le_mul_left _ hdu
      _ = base ^ N := by rw [← pow_succ]; congr 1; omega
  have hDge : base ^ (N - 1) ≤ D := by
    rw [hDsplit]
    calc base ^ (N - 1) = base ^ (N - 1) * 1 := by ring
      _ ≤ base ^ (N - 1) * W[dp.toNat + N - 1]!.toNat := Nat.mul_le_mul_left _ htop0
      _ ≤ _ := Nat.le_add_left _ _
  have hsn : (sp + n).toNat = sp.toNat + N := by rw [toNat_add_lt (by omega), hN]
  have hsnl : (sp + n + lx).toNat = sp.toNat + N + LX := by rw [toNat_add_lt (by omega), hsn, hLX]
  have hl1 : (lx + 1).toNat = LX + 1 := by rw [toNat_add_lt (by simp; omega), hLX]; simp
  -- the copy and normalization of the divisor
  obtain ⟨a1, a2, a3, a4⟩ := addGen_copy W dp dp sp n (by omega) (by rw [hN]; omega) (by omega)
    (by rw [hN]; omega) (by rw [hN]; exact hdd) (by rw [hN]; omega)
  rw [hN, hD] at a4
  rw [hN] at a2 a3
  generalize hW1 : (addGen W dp dp 0 sp n).2 = W1 at a1 a2 a3 a4
  obtain ⟨m1, m2, m3, m4⟩ := mulAddSeg_spec W1 sp n d 0 (by omega) (by rw [hN, a1]; omega)
    (by rw [hN]; exact a3) hdb (by simp; exact hb0) (by rw [hN, a4]; simpa using hDd)
  rw [hN, a4] at m4
  rw [hN] at m2 m3
  simp only [UInt64.toNat_zero, Nat.add_zero] at m4
  generalize hW2 : mulAddSeg W1 sp n d 0 = W2 at m1 m2 m3 m4
  -- the copy of the dividend with one more limb, and its normalization
  have hdx2 : SegDigits W2 xp.toNat LX := hdx.congr fun i hi => by
    rw [m2 _ (by omega), a2 _ (by omega)]
  obtain ⟨c1, c2, c3, c4⟩ := addGen_copy W2 xp xp (sp + n) lx (by omega) (by rw [hLX]; omega)
    (by rw [m1, a1]; omega) (by rw [hsn, hLX, m1, a1]; omega) (by rw [hLX]; exact hdx2)
    (by rw [hsn, hLX]; omega)
  rw [hsn, hLX] at c2 c3 c4
  rw [segVal_congr (W := W2) (W' := W) (p := xp.toNat) (p' := xp.toNat) fun i hi => by
    rw [m2 _ (by omega), a2 _ (by omega)], hX] at c4
  generalize hW3 : (addGen W2 xp xp 0 (sp + n) lx).2 = W3 at c1 c2 c3 c4
  have hin3 : sp.toNat + N + LX < W3.size := by rw [c1, m1, a1]; omega
  have get3 := fun q => get_set W3 (sp.toNat + N + LX) 0 q hin3
  rw [hsnl]
  generalize hW4 : W3.set! (sp.toNat + N + LX) 0 = W4 at get3
  have h4s : W4.size = W.size := by rw [← hW4]; simp [c1, m1, a1]
  have hX4 : segVal W4 (sp.toNat + N) (LX + 1) = X := by
    rw [segVal_succ, get3, if_pos rfl, ← c4]
    simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
    exact segVal_congr fun i hi => by rw [get3, if_neg (by omega)]
  have hd4 : SegDigits W4 (sp.toNat + N) (LX + 1) := fun i hi => by
    rw [get3]; split
    · exact hb0
    · exact c3 i (by omega)
  have hXd : X * d.toNat < base ^ (LX + 1) := by
    rw [pow_succ]; exact Nat.mul_lt_mul_of_lt_of_le hXlt (le_of_lt hdb) hb0
  obtain ⟨n1, n2, n3, n4⟩ := mulAddSeg_spec W4 (sp + n) (lx + 1) d 0 (by omega)
    (by rw [hsn, hl1]; omega) (by rw [hsn, hl1]; exact hd4) hdb (by simp; exact hb0)
    (by rw [hsn, hl1, hX4]; simpa using hXd)
  rw [hsn, hl1, hX4] at n4
  rw [hsn, hl1] at n2 n3
  simp only [UInt64.toNat_zero, Nat.add_zero] at n4
  generalize hW5 : mulAddSeg W4 (sp + n) (lx + 1) d 0 = W5 at n1 n2 n3 n4
  -- the normalized divisor in `W5`
  have h5b : ∀ i, i < N → W5[sp.toNat + i]! = W2[sp.toNat + i]! := fun i hi => by
    rw [n2 _ (by omega), get3, if_neg (by omega), c2 _ (by omega)]
  have hBd : segVal W5 sp.toNat N = D * d.toNat := by rw [segVal_congr h5b, m4]
  have hdb5 : SegDigits W5 sp.toNat N := m3.congr h5b
  have hv15 : base ≤ 2 * W5[sp.toNat + N - 1]!.toNat := by
    have hdig := segVal_digit m3 (show N - 1 < N by omega)
    rw [m4, Nat.mod_eq_of_lt (by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hb0 _), ← pow_succ', show N - 1 + 1 = N by omega]
      exact hDd)] at hdig
    rw [show sp.toNat + N - 1 = sp.toNat + (N - 1) by omega, h5b _ (by omega), ← hdig]
    have : W[dp.toNat + N - 1]!.toNat * d.toNat ≤ D * d.toNat / base ^ (N - 1) := by
      rw [Nat.le_div_iff_mul_le (pow_pos hb0 _)]
      calc W[dp.toNat + N - 1]!.toNat * d.toNat * base ^ (N - 1)
          = base ^ (N - 1) * W[dp.toNat + N - 1]!.toNat * d.toNat := by ring
        _ ≤ D * d.toNat := Nat.mul_le_mul_right _ (by rw [hDsplit]; exact Nat.le_add_left _ _)
    omega
  -- the division
  obtain ⟨M, hM⟩ : ∃ M, M = LX + 1 - N := ⟨_, rfl⟩
  have hMw : (lx + 1 - n).toNat = M := by rw [toNat_sub_le' (by rw [hl1, hN]; omega), hl1, hN, hM]
  have hsnl1 : (sp + n + lx + 1).toNat = sp.toNat + N + LX + 1 := by
    rw [toNat_add_lt (by rw [hsnl]; simp; omega), hsnl]; simp
  have hlt : segVal W5 (sp.toNat + N) (N + M) < base ^ M * segVal W5 sp.toNat N := by
    rw [show N + M = LX + 1 by omega, n4, hBd]
    have : X < base ^ M * D := lt_of_lt_of_le hXlt (by
      calc base ^ LX = base ^ M * base ^ (N - 1) := by rw [← pow_add]; congr 1; omega
        _ ≤ base ^ M * D := Nat.mul_le_mul_left _ hDge)
    calc X * d.toNat < base ^ M * D * d.toNat := Nat.mul_lt_mul_of_pos_right this hd0
      _ = base ^ M * (D * d.toNat) := by ring
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := udiv_spec t T W5 (sp + n) sp qp (sp + n + lx + 1) n
    (lx + 1 - n) N M hN hMw (by omega) hn (by omega) (by omega) (by rw [hsn]) (by rw [hsn, hsnl1]; omega)
    (by rw [hsnl1, n1, h4s]; omega) (by rw [hsn, show N + M = LX + 1 by omega]; exact n3) hdb5 hv15
    (by rw [hsn]; exact hlt)
  rw [hsn, show N + M = LX + 1 by omega, n4, hBd, Nat.mul_mod_mul_right] at u5
  rw [hsn, show N + M = LX + 1 by omega, n4, hBd, Nat.mul_div_mul_right _ _ hd0] at u6
  rw [hsn, hsnl1] at u2
  rw [hsn, show N + M = LX + 1 by omega] at u3
  generalize hW6 : udiv t T W5 (sp + n) sp qp (sp + n + lx + 1) n (lx + 1 - n) = W6
    at u1 u2 u3 u4 u5 u6
  -- the remainder divided back by `d`
  have hDpos : 0 < D := lt_of_lt_of_le (pow_pos hb0 _) hDge
  have hR6 : segVal W6 (sp.toNat + N) N = X % D * d.toNat := by
    have hsm := Nat.mod_lt X hDpos
    have hz := segVal_high_zero (W := W6) (p := sp.toNat + N) (a := N) (k := LX + 1 - N)
      (by rw [show N + (LX + 1 - N) = LX + 1 by omega]; exact u3)
      (by rw [show N + (LX + 1 - N) = LX + 1 by omega, u5]
          exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hsm hd0) (le_of_lt hDd))
    rw [← u5, show LX + 1 = N + (LX + 1 - N) by omega, segVal_add W6 (sp.toNat + N) N, hz,
      Nat.mul_zero, Nat.add_zero]
  obtain ⟨v1, v2, v3, v4, v5⟩ := divSmallSeg_spec W6 (sp + n) n d (by omega) hd0 (le_of_lt hdb)
    (by rw [hsn, hN, u1, n1, h4s]; omega) (by rw [hsn, hN]; exact u3.mono (by omega))
  rw [hsn, hN, hR6, Nat.mul_div_cancel _ hd0] at v4
  rw [hsn, hN] at v2 v3
  generalize hW7 : (divSmallSeg W6 (sp + n) n d).2 = W7 at v1 v2 v3 v4
  -- the copy of the remainder and the zeros above it
  obtain ⟨w1, w2, w3, w4⟩ := addGen_copy W7 (sp + n) (sp + n) xp n (by omega)
    (by rw [hsn, hN, v1, u1, n1, h4s]; omega) (by rw [hsn, v1, u1, n1, h4s]; omega)
    (by rw [hN, v1, u1, n1, h4s]; omega) (by rw [hsn, hN]; exact v3) (by rw [hsn, hN]; omega)
  rw [hsn, hN, v4] at w4
  rw [hN] at w2 w3
  generalize hW8 : (addGen W7 (sp + n) (sp + n) 0 xp n).2 = W8 at w1 w2 w3 w4
  have hxn : (xp + n).toNat = xp.toNat + N := by rw [toNat_add_lt (by omega), hN]
  have hln : (lx - n).toNat = LX - N := by rw [toNat_sub_le' (by rw [hN, hLX]; omega), hN, hLX]
  obtain ⟨z1, z2, z3⟩ := clear_spec W8 (xp + n) (lx - n) (by omega)
    (by rw [hxn, hln, w1, v1, u1, n1, h4s]; omega)
  rw [hxn, hln] at z2 z3
  -- the result
  have hframe : ∀ p, ¬ (xp.toNat ≤ p ∧ p < xp.toNat + LX) →
      ¬ (qp.toNat ≤ p ∧ p < qp.toNat + (LX + 1 - N)) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + (13 * N + LX + 10)) →
      (LeanExe.loop (lx - n) W8 fun i W => W.set! (xp + n + i).toNat 0)[p]! = W[p]! :=
    fun p h1 h2 h3 => by
      rw [z2 p (by omega), w2 p (by omega), v2 p (by omega), u2 p (by omega) (by omega) (by omega),
        n2 p (by omega), get3, if_neg (by omega), c2 p (by omega), m2 p (by omega),
        a2 p (by omega)]
  have hq9 : ∀ i, i < M → (LeanExe.loop (lx - n) W8 fun i W => W.set! (xp + n + i).toNat 0)[qp.toNat + i]! =
      W6[qp.toNat + i]! := fun i hi => by
    rw [z2 _ (by omega), w2 _ (by omega), v2 _ (by omega)]
  refine ⟨by rw [z1, w1, v1, u1, n1, h4s], hframe, fun i hi => ?_, ?_, ?_, ?_⟩
  · rcases Nat.lt_or_ge i N with h | h
    · rw [z2 _ (by omega)]; exact w3 i h
    · have := z3 (i - N) (by omega)
      rw [show xp.toNat + N + (i - N) = xp.toNat + i by omega] at this
      rw [this]; exact hb0
  · rw [← hM]; exact u4.congr hq9
  · rw [show LX = N + (LX - N) by omega, segVal_add, segVal_zeros z3, Nat.mul_zero, Nat.add_zero,
      ← w4]
    exact segVal_congr fun i hi => z2 _ (by omega)
  · rw [← hM, segVal_congr hq9, u6]

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The first iteration's `natDivMod` over the second iteration's shift-carry Algorithm D is the
first iteration's `natDivMod`. -/
theorem natDivModS_eq (u v : Array UInt64) : natDivModS u v = natDivMod u v := by
  unfold natDivModS natDivMod; rw [divideS_eq_divide]

/-- A canonical natural of `n ≥ 1` limbs is at least `β^(n-1)`. -/
theorem value_ge_of_canonical {v : Array UInt64} (hv : Canonical v) (h : 0 < v.size) :
    base ^ (v.size - 1) ≤ value v := by
  rw [← segVal_value]
  have htop := hv.2 h
  have hpos : 0 < v[v.size - 1]!.toNat := by
    rw [getElem!_pos v (v.size - 1) (by omega)]
    rcases Nat.eq_zero_or_pos v[v.size - 1].toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by rw [h0]; rfl)) htop
    · exact h0
  have := segVal_succ v 0 (v.size - 1)
  rw [show v.size - 1 + 1 = v.size by omega, Nat.zero_add] at this
  rw [this]
  calc base ^ (v.size - 1) = 1 * base ^ (v.size - 1) := by ring
    _ ≤ v[v.size - 1]!.toNat * base ^ (v.size - 1) := Nat.mul_le_mul_right _ hpos
    _ ≤ _ := Nat.le_add_left _ _

set_option maxHeartbeats 4000000 in
/-- The natural division of the third iteration returns the canonical limbs of the quotient and
the remainder, with `u / 0 = 0` and `u % 0 = u`, at every threshold. -/
theorem natDivModBZWith_eq (t T D : UInt64) {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModBZWith t T D u v = natDivModSpec (value u) (value v) := by
  have hmU := size_toNat64 (u := u) (by omega)
  have hnV := size_toNat64 (u := v) (by omega)
  unfold natDivModBZWith
  dsimp only
  by_cases h1 : u.size.toUInt64 < v.size.toUInt64
  · rw [if_pos h1]
    rw [UInt64.lt_iff_toNat_lt, hmU, hnV] at h1
    have hlt : value u < value v :=
      lt_of_lt_of_le (value_lt hu.1) (le_trans (Nat.pow_le_pow_right base_pos (by omega))
        (value_ge_of_canonical hv (by omega)))
    unfold natDivModSpec
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, limbsOf_zero, natTrim_eq hu.1 (by omega)]
  rw [if_neg h1]
  rw [UInt64.lt_iff_toNat_lt, hmU, hnV] at h1
  by_cases h2 : v.size.toUInt64 < 2 ∨ v.size.toUInt64 < D ∨ u.size.toUInt64 < v.size.toUInt64 + D ∨
      u.size.toUInt64 < v.size.toUInt64 + 2
  · rw [if_pos h2, natDivModS_eq, natDivMod_eq hu hv hsu hsv]
  rw [if_neg h2]
  simp only [not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, hmU, hnV, UInt64.reduceToNat] at h2
  obtain ⟨h2a, h2b, h2c, h2d⟩ := h2
  have hn2 : (v.size.toUInt64 + 2).toNat = v.size + 2 := by
    simp only [UInt64.toNat_add, hnV, UInt64.reduceToNat]; omega
  rw [hn2] at h2d
  -- the workspace
  have hsize : (3 * u.size.toUInt64 + 15 * v.size.toUInt64 + 11).toNat =
      3 * u.size + 15 * v.size + 11 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hmU, hnV, UInt64.reduceToNat]; omega
  generalize hWd : LeanExe.build (3 * u.size.toUInt64 + 15 * v.size.toUInt64 + 11) (fun i =>
    if i < u.size.toUInt64 then u[i.toNat]! else if i < u.size.toUInt64 + v.size.toUInt64 then
      v[(i - u.size.toUInt64).toNat]! else 0) = W
  have hWs : W.size = 3 * u.size + 15 * v.size + 11 := by rw [← hWd, build_size, hsize]
  have hWu : ∀ i, i < u.size → W[i]! = u[i]! := fun i hi => by
    have hi' : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
    rw [← hWd, build_get (by rw [hsize]; omega), if_pos (by rw [UInt64.lt_iff_toNat_lt, hi', hmU]; exact hi),
      hi']
  have hWv : ∀ i, i < v.size → W[u.size + i]! = v[i]! := fun i hi => by
    have hi' : (UInt64.ofNat (u.size + i)).toNat = u.size + i := toNat_ofNat_lt (by omega)
    have hln : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
      rw [toNat_add_lt (by omega), hmU, hnV]
    rw [← hWd, build_get (by rw [hsize]; omega),
      if_neg (by rw [UInt64.not_lt, UInt64.le_iff_toNat_le, hi', hmU]; omega),
      if_pos (by rw [UInt64.lt_iff_toNat_lt, hi', hln]; omega),
      toNat_sub_le' (by rw [hi', hmU]; omega), hi', hmU, Nat.add_sub_cancel_left]
  have hdu : SegDigits W 0 u.size := fun i hi => by
    simpa [hWu i hi] using hu.1 i hi
  have hdv : SegDigits W u.size v.size := fun i hi => by rw [hWv i hi]; exact hv.1 i hi
  have hUv : segVal W 0 u.size = value u := by
    rw [← segVal_value]; exact segVal_congr fun i hi => by simpa using hWu i hi
  have hVv : segVal W u.size v.size = value v := by
    rw [← segVal_value]; exact segVal_congr fun i hi => by simpa using hWv i hi
  have htop : W[u.size + v.size - 1]! ≠ 0 := by
    rw [show u.size + v.size - 1 = u.size + (v.size - 1) by omega, hWv _ (by omega),
      getElem!_pos v (v.size - 1) (by omega)]
    exact hv.2 (by omega)
  have hln : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    rw [toNat_add_lt (by omega), hmU, hnV]
  have h2l : (2 * u.size.toUInt64 + 1).toNat = 2 * u.size + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hmU, UInt64.reduceToNat]; omega
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := divSeg_spec t T W 0 u.size.toUInt64 u.size.toUInt64
    v.size.toUInt64 (u.size.toUInt64 + v.size.toUInt64) (2 * u.size.toUInt64 + 1) v.size u.size
    hnV hmU (by omega) (by omega) (by omega) (by simp only [UInt64.toNat_zero]; omega)
    (by rw [hmU, hln]) (by rw [hln, h2l]; omega) (by rw [hWs, h2l]; omega)
    (by simpa using hdu) (by rw [hmU]; exact hdv) (by rw [hmU]; exact htop)
  rw [hmU, hVv] at d5 d6
  simp only [UInt64.toNat_zero] at d3 d5 d6
  rw [hUv] at d5 d6
  rw [hln] at d4 d6
  generalize hW' : divSeg t T W 0 u.size.toUInt64 u.size.toUInt64 v.size.toUInt64
    (u.size.toUInt64 + v.size.toUInt64) (2 * u.size.toUInt64 + 1) = W' at d1 d2 d3 d4 d5 d6
  have hW's : W'.size < 2 ^ 64 := by rw [d1, hWs]; omega
  have hq1 : (u.size.toUInt64 + 1 - v.size.toUInt64).toNat = u.size + 1 - v.size := by
    have : (u.size.toUInt64 + 1).toNat = u.size + 1 := by
      simp only [UInt64.toNat_add, hmU, UInt64.reduceToNat]; omega
    rw [toNat_sub_le' (by rw [this, hnV]; omega), this, hnV]
  have hvpos : 0 < value v :=
    lt_of_lt_of_le (pow_pos base_pos _) (value_ge_of_canonical hv (by omega))
  have hrem : segVal W' 0 v.size = value u % value v := by
    have hmod := Nat.mod_lt (value u) hvpos
    have hz := segVal_high_zero (W := W') (p := 0) (a := v.size) (k := u.size - v.size)
      (by rw [show v.size + (u.size - v.size) = u.size by omega]; exact d3)
      (by rw [show v.size + (u.size - v.size) = u.size by omega, d5]
          exact lt_of_lt_of_le hmod (le_of_lt (value_lt hv.1)))
    rw [← d5, show u.size = v.size + (u.size - v.size) by omega, segVal_add W' 0 v.size, hz,
      Nat.mul_zero, Nat.add_zero]
  unfold natDivModSpec
  rw [trimSeg_eq W' _ _ hW's (by rw [hln, hq1, d1, hWs]; omega) (by rw [hln, hq1]; exact d4),
    trimSeg_eq W' _ _ hW's (by rw [hnV, d1, hWs]; simp; omega) (by
      rw [hnV]; simpa using d3.mono (k' := v.size) (by omega)), hln, hq1, d6, hnV]
  simp only [UInt64.toNat_zero]
  rw [hrem]

end Library.Numerics.Bignum

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision

/-- The natural division of the third iteration returns the canonical limbs of the quotient and
the remainder. -/
theorem natDivModBZ_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModBZ u v = natDivModSpec (value u) (value v) :=
  natDivModBZWith_eq _ _ _ hu hv hsu hsv

/-- The natural division of the third iteration returns what the first iteration's returns. -/
theorem natDivModBZ_eq_natDivMod {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) : natDivModBZ u v = natDivMod u v := by
  rw [natDivModBZ_eq hu hv hsu hsv, natDivMod_eq hu hv hsu hsv]

/-- The export of natural division with its thresholds: the status 1 and two zeros for a zero
divisor, and otherwise the status 0 and the canonical limbs of the quotient and the remainder, at
every threshold. -/
theorem natDivModCheckedBZWith_eq (t T D : UInt64) {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZWith t T D u v = natDivModCheckedSpec (value u) (value v) := by
  unfold natDivModCheckedBZWith natDivModCheckedSpec
  rw [size_toUInt64_beq_zero (by omega)]
  by_cases h0 : v.size = 0
  · rw [decide_eq_true h0, ite_eq_left rfl, ite_eq_left ((value_eq_zero_iff hv).mpr h0),
      limbsOf_zero]
  · rw [decide_eq_false h0, ite_eq_right (by decide),
      ite_eq_right fun h => h0 ((value_eq_zero_iff hv).mp h), natDivModBZWith_eq t T D hu hv hsu hsv]
    rfl

/-- The export of natural division: the status 1 and two zeros for a zero divisor, and otherwise
the status 0 and the canonical limbs of the quotient and the remainder. -/
theorem natDivModCheckedBZ_eq {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZ u v = natDivModCheckedSpec (value u) (value v) :=
  natDivModCheckedBZWith_eq _ _ _ hu hv hsu hsv

/-- The export of natural division returns what the first iteration's returns. -/
theorem natDivModCheckedBZ_eq_natDivModChecked {u v : Array UInt64} (hu : Canonical u)
    (hv : Canonical v) (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    natDivModCheckedBZ u v = natDivModChecked u v := by
  rw [natDivModCheckedBZ_eq hu hv hsu hsv, natDivModChecked_eq hu hv hsu hsv]

/-- For a divisor that is not empty, the export of natural division is the status 0 and the
division of Lean's convention. -/
theorem natDivModCheckedBZ_of_ne {u v : Array UInt64}
    (h0 : ¬ (v.size.toUInt64 == 0) = true) : natDivModCheckedBZ u v = (0, natDivModBZ u v) := by
  unfold natDivModCheckedBZ natDivModCheckedBZWith
  rw [if_neg h0]; rfl

/-- Truncated division returns what the first iteration's returns. -/
theorem intTDivModCheckedBZ_eq_intTDivModChecked {x y : BigInt} (hx : Canonical x.mag)
    (hy : Canonical y.mag) (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) :
    intTDivModCheckedBZ x y = intTDivModChecked x y := by
  unfold intTDivModCheckedBZ intTDivModChecked
  split
  · rfl
  · rename_i h0
    rw [natDivModCheckedBZ_of_ne h0]
    simp only [intTDivMod, signTDiv, natDivModBZ_eq_natDivMod hx hy hsx hsy]

/-- Euclidean division returns what the first iteration's returns. -/
theorem intEDivModCheckedBZ_eq_intEDivModChecked {x y : BigInt} (hx : Canonical x.mag)
    (hy : Canonical y.mag) (hsx : x.mag.size < 2 ^ 32) (hsy : y.mag.size < 2 ^ 32) :
    intEDivModCheckedBZ x y = intEDivModChecked x y := by
  unfold intEDivModCheckedBZ intEDivModChecked
  split
  · rfl
  · rename_i h0
    rw [natDivModCheckedBZ_of_ne h0]
    simp only [intEDivMod, intTDivMod, signEDiv, natDivModBZ_eq_natDivMod hx hy hsx hsy]
    split_ifs <;> simp_all

/-- The export of truncated division: the status 1 and two zeros for a zero divisor, and
otherwise the status 0 and the canonical integers of `Int.tdiv` and `Int.tmod`. -/
theorem intTDivModCheckedBZ_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intTDivModCheckedBZ (.ofInt a) (.ofInt b) = intTDivModCheckedSpec a b := by
  rw [intTDivModCheckedBZ_eq_intTDivModChecked (canonical_limbsOf _) (canonical_limbsOf _) ha hb,
    intTDivModChecked_eq ha hb]

/-- The export of Euclidean division: the status 1 and two zeros for a zero divisor, and
otherwise the status 0 and the canonical integers of Lean's `/` and `%`. -/
theorem intEDivModCheckedBZ_eq {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    intEDivModCheckedBZ (.ofInt a) (.ofInt b) = intEDivModCheckedSpec a b := by
  rw [intEDivModCheckedBZ_eq_intEDivModChecked (canonical_limbsOf _) (canonical_limbsOf _) ha hb,
    intEDivModChecked_eq ha hb]

/-- The quotient and the remainder of the natural division are canonical. -/
theorem natDivModBZ_canonical {u v : Array UInt64} (hu : Canonical u) (hv : Canonical v)
    (hsu : u.size < 2 ^ 32) (hsv : v.size < 2 ^ 32) :
    Canonical (natDivModBZ u v).1 ∧ Canonical (natDivModBZ u v).2 := by
  rw [natDivModBZ_eq hu hv hsu hsv]
  exact ⟨canonical_limbsOf _, canonical_limbsOf _⟩

/-- The quotient and the remainder of the integer divisions are canonical. -/
theorem intDivModCheckedBZ_canonical {a b : ℤ} (ha : (BigInt.ofInt a).mag.size < 2 ^ 32)
    (hb : (BigInt.ofInt b).mag.size < 2 ^ 32) :
    (intTDivModCheckedBZ (.ofInt a) (.ofInt b)).2.1.Canonical ∧
    (intTDivModCheckedBZ (.ofInt a) (.ofInt b)).2.2.Canonical ∧
    (intEDivModCheckedBZ (.ofInt a) (.ofInt b)).2.1.Canonical ∧
    (intEDivModCheckedBZ (.ofInt a) (.ofInt b)).2.2.Canonical := by
  rw [intTDivModCheckedBZ_eq ha hb, intEDivModCheckedBZ_eq ha hb]
  unfold intTDivModCheckedSpec intEDivModCheckedSpec
  split <;> exact ⟨canonical_ofInt _, canonical_ofInt _, canonical_ofInt _, canonical_ofInt _⟩

end Library.Numerics.Bignum
