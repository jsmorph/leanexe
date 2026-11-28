module

public import Library.Numerics.Bignum.Third.DivProd

@[expose] public section

/-!
The corrections of Algorithm 1.8, steps 4 and 5 or 7 and 8: `subFix_spec` subtracts the product
`P` in the accumulator from the `n + 1` limbs of the region at `rp`, which then hold `X - P` plus
`β^(n+1)` times the borrow, and while the borrow says the difference is negative it adds the
divisor `B` and decreases the quotient.  When `X - P + 4 B ≥ 0` and `X - P + Q B ≥ 0`, which
Brent and Zimmermann's proof of Theorem 1.4 gives for both halves, the loop ends within its fuel
of four with `X - P + j B` for some `j ≤ 4`, nonnegative, and below `B` when `j ≥ 1`, and with the
quotient `Q - j`.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-- The state of the loop of `subFix` after `j` corrections. -/
def FixInv (W : Array UInt64) (rp bp qp sp N QL : ℕ) (X P B Q : ℤ) (j : ℕ)
    (st : UInt64 × UInt64 × Array UInt64) : Prop :=
  st.2.2.size = W.size ∧
  (∀ p, ¬ (rp ≤ p ∧ p < rp + N + 1) → ¬ (qp ≤ p ∧ p < qp + QL) → p ≠ sp →
    st.2.2[p]! = W[p]!) ∧
  st.2.2[sp]! = 1 ∧ SegDigits st.2.2 rp (N + 1) ∧ SegDigits st.2.2 qp QL ∧
  st.1.toNat ≤ 1 ∧ st.2.1.toNat ≤ 1 ∧
  (segVal st.2.2 rp (N + 1) : ℤ) = X - P + j * B + st.1.toNat * (base : ℤ) ^ (N + 1) ∧
  (segVal st.2.2 qp QL : ℤ) + st.2.1.toNat * (base : ℤ) ^ QL + j = Q ∧
  (st.1.toNat = 1 ↔ X - P + j * B < 0) ∧ (1 ≤ j → X - P + (j - 1 : ℕ) * B < 0)

/-- `subFix` subtracts the product and corrects the difference and the quotient at most four
times. -/
theorem subFix_spec (W : Array UInt64) (rp bp n qp ql c sp al : UInt64)
    (N QL AL : ℕ) (hn : n.toNat = N) (hql : ql.toNat = QL) (hal : al.toNat = AL)
    (hW : W.size < 2 ^ 62) (hQL : 1 ≤ QL) (hc : c.toNat ≤ 1)
    (hqb : qp.toNat + QL ≤ bp.toNat) (hbr : bp.toNat + N ≤ rp.toNat)
    (hrs : rp.toNat + N + 1 ≤ sp.toNat) (hsz : sp.toNat + 1 + AL ≤ W.size)
    (hdr : SegDigits W rp.toNat (N + 1)) (hdb : SegDigits W bp.toNat N)
    (hdq : SegDigits W qp.toNat QL) (hdp : SegDigits W (sp.toNat + 1) AL)
    (hBpos : 0 < segVal W bp.toNat N)
    (hP : segVal W (sp.toNat + 1) AL < base ^ (N + 1))
    (h4 : (segVal W (sp.toNat + 1) AL : ℤ) ≤ segVal W rp.toNat (N + 1) + 4 * segVal W bp.toNat N)
    (hQ : (segVal W (sp.toNat + 1) AL : ℤ) ≤ segVal W rp.toNat (N + 1) +
      (segVal W qp.toNat QL + c.toNat * base ^ QL : ℕ) * segVal W bp.toNat N) :
    (subFix W rp bp n qp ql c sp al).2.size = W.size ∧
    (∀ p, ¬ (rp.toNat ≤ p ∧ p < rp.toNat + N + 1) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + QL) →
      p ≠ sp.toNat → (subFix W rp bp n qp ql c sp al).2[p]! = W[p]!) ∧
    SegDigits (subFix W rp bp n qp ql c sp al).2 rp.toNat (N + 1) ∧
    SegDigits (subFix W rp bp n qp ql c sp al).2 qp.toNat QL ∧
    (subFix W rp bp n qp ql c sp al).1.toNat ≤ 1 ∧
    ∃ j : ℕ, j ≤ 4 ∧
      (segVal (subFix W rp bp n qp ql c sp al).2 rp.toNat (N + 1) : ℤ) =
        segVal W rp.toNat (N + 1) - segVal W (sp.toNat + 1) AL + j * segVal W bp.toNat N ∧
      segVal (subFix W rp bp n qp ql c sp al).2 qp.toNat QL +
          (subFix W rp bp n qp ql c sp al).1.toNat * base ^ QL + j =
        segVal W qp.toNat QL + c.toNat * base ^ QL ∧
      (j = 0 ∨ segVal (subFix W rp bp n qp ql c sp al).2 rp.toNat (N + 1) <
        segVal W bp.toNat N) := by
  have hb0 := base_pos
  have hn1 : (n + 1).toNat = N + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  generalize hX : segVal W rp.toNat (N + 1) = X at h4 hQ
  generalize hPv : segVal W (sp.toNat + 1) AL = P at hP h4 hQ
  generalize hB : segVal W bp.toNat N = B at hBpos h4 hQ
  generalize hQ0 : segVal W qp.toNat QL + c.toNat * base ^ QL = Q0 at hQ
  -- the product's limbs within the region
  have hPm : segVal W (sp.toNat + 1) (min AL (N + 1)) = P := by
    by_cases hle : AL ≤ N + 1
    · rw [Nat.min_eq_left hle, hPv]
    · rw [Nat.min_eq_right (by omega)]
      have hsplit := segVal_add W (sp.toNat + 1) (N + 1) (AL - (N + 1))
      rw [show N + 1 + (AL - (N + 1)) = AL by omega, hPv] at hsplit
      have hz := segVal_high_zero (W := W) (p := sp.toNat + 1) (a := N + 1) (k := AL - (N + 1))
        (by rw [show N + 1 + (AL - (N + 1)) = AL by omega]; exact hdp)
        (by rw [show N + 1 + (AL - (N + 1)) = AL by omega, hPv]; exact hP)
      rw [hz, Nat.mul_zero, Nat.add_zero] at hsplit
      exact hsplit.symm
  -- the subtraction
  obtain ⟨g1, g2, g3, g4, g5⟩ := subGen_spec W rp (sp + 1) al rp (n + 1) (by omega)
    (by rw [hn1]; omega) (by rw [hs1, hal, hn1]; omega) (by rw [hn1]; omega)
    (by rw [hn1]; exact hdr) (by rw [hs1, hal, hn1]; exact hdp.mono (by omega))
    (fun i j hij _ => by omega) (fun i j _ hj => by rw [hs1]; omega)
  rw [hn1, hs1, hal, hPm, hX] at g5
  rw [hn1] at g2 g3
  unfold subFix
  dsimp only
  generalize hs : subGen W rp (sp + 1) al rp (n + 1) = s at g1 g2 g3 g4 g5
  have hsp : sp.toNat < s.2.size := by omega
  have hget := fun p => get_set s.2 sp.toNat 1 p hsp
  have hS1 := segVal_lt g3
  have hBp : (0 : ℤ) < B := by exact_mod_cast hBpos
  have hPZ : (P : ℤ) < (base : ℤ) ^ (N + 1) := by exact_mod_cast hP
  have hQZ : (P : ℤ) ≤ X + Q0 * B := by exact_mod_cast hQ
  have h4Z : (P : ℤ) ≤ X + 4 * B := by exact_mod_cast h4
  -- the loop
  obtain ⟨j, hj4, hinv, hcond⟩ := repeatWhile_count 4 (s.1, c, s.2.set! sp.toNat 1)
    (fun st => st.1 == 1)
    (fun st => ((1 : UInt64) - (addGen st.2.2 rp bp n rp (n + 1)).1,
      st.2.1 - (subGen (addGen st.2.2 rp bp n rp (n + 1)).2 qp sp 1 qp ql).1,
      (subGen (addGen st.2.2 rp bp n rp (n + 1)).2 qp sp 1 qp ql).2))
    (FixInv W rp.toNat bp.toNat qp.toNat sp.toNat N QL X P B Q0)
    (by
      have hreg : segVal (s.2.set! sp.toNat 1) rp.toNat (N + 1) = segVal s.2 rp.toNat (N + 1) :=
        segVal_congr fun i hi => by rw [hget, if_neg (by omega)]
      have hqq : segVal (s.2.set! sp.toNat 1) qp.toNat QL = segVal W qp.toNat QL :=
        segVal_congr fun i hi => by rw [hget, if_neg (by omega), g2 _ (by omega)]
      have g5Z : (segVal s.2 rp.toNat (N + 1) : ℤ) + P = X + s.1.toNat * (base : ℤ) ^ (N + 1) := by
        exact_mod_cast g5
      have hS1Z : (segVal s.2 rp.toNat (N + 1) : ℤ) < (base : ℤ) ^ (N + 1) := by exact_mod_cast hS1
      have hpow : (0 : ℤ) < (base : ℤ) ^ (N + 1) := by positivity
      refine ⟨by simp [g1], fun p h1 h2 h3 => by rw [hget, if_neg h3]; exact g2 p (by omega),
        by rw [hget, if_pos rfl], fun i hi => by rw [hget, if_neg (by omega)]; exact g3 i hi,
        fun i hi => by rw [hget, if_neg (by omega), g2 _ (by omega)]; exact hdq i hi, g4, hc, ?_,
        ?_, ?_, fun h => by omega⟩
      · rw [hreg]; push_cast; linarith
      · rw [hqq, ← hQ0]; push_cast; ring
      · have hS0 : (0 : ℤ) ≤ segVal s.2 rp.toNat (N + 1) := by positivity
        rcases (show s.1.toNat = 0 ∨ s.1.toNat = 1 by omega) with h | h
        · rw [h] at g5Z ⊢
          constructor
          · intro h'; simp at h'
          · intro hneg; exfalso; push_cast at hneg g5Z; linarith
        · rw [h] at g5Z ⊢
          constructor
          · intro _; push_cast at g5Z ⊢; linarith
          · intro _; rfl)
    (by
      intro j st hj ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ hcond
      have hb1 : st.1 = 1 := by simpa using hcond
      have hb1' : st.1.toNat = 1 := by rw [hb1]; rfl
      have hneg : (X : ℤ) - P + j * B < 0 := v10.mp hb1'
      rw [hb1'] at v8
      have hVb : ∀ i, i < N → st.2.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
        v2 _ (by omega) (by omega) (by omega)
      have hBV : segVal st.2.2 bp.toNat N = B := by rw [← hB]; exact segVal_congr hVb
      -- the addition of the divisor
      obtain ⟨a1, a2, a3, a4, a5⟩ := addGen_inplace st.2.2 rp bp n (n + 1) (by omega)
        (by rw [hn1, v1]; omega) (by rw [hn, hn1, v1]; omega) (by rw [hn1]; exact v4)
        (by rw [hn, hn1, Nat.min_eq_left (by omega)]; exact (hdb.congr hVb))
        (by rw [hn, hn1, Nat.min_eq_left (by omega)]; omega)
      rw [hn, hn1, Nat.min_eq_left (by omega), hBV] at a5
      rw [hn1] at a2 a3
      generalize hA : addGen st.2.2 rp bp n rp (n + 1) = A at a1 a2 a3 a4 a5
      have hA3 := segVal_lt a3
      -- the decrease of the quotient
      have hAsp : A.2[sp.toNat]! = 1 := by rw [a2 _ (by omega), v3]
      have hdsp : SegDigits A.2 sp.toNat (min (1 : UInt64).toNat ql.toNat) := by
        rw [hql, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left hQL]
        intro i hi
        rw [show i = 0 by omega, Nat.add_zero, hAsp]; exact one_lt_base
      obtain ⟨d1, d2, d3, d4, d5⟩ := subGen_inplace A.2 qp sp 1 ql (by omega)
        (by rw [hql, a1, v1]; omega)
        (by rw [hql, a1, v1, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left hQL]; omega)
        (by rw [hql]; exact fun i hi => by rw [a2 _ (by omega)]; exact v5 i hi) hdsp
        (by rw [hql, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left hQL]; omega)
      rw [hql, show (1 : UInt64).toNat = 1 from rfl, Nat.min_eq_left hQL] at d5
      rw [hql] at d2 d3
      have hone : segVal A.2 sp.toNat 1 = 1 := by simp [segVal, hAsp]
      have hqA : segVal A.2 qp.toNat QL = segVal st.2.2 qp.toNat QL :=
        segVal_congr fun i hi => a2 _ (by omega)
      rw [hone, hqA] at d5
      generalize hD : subGen A.2 qp sp 1 qp ql = D at d1 d2 d3 d4 d5
      have hD3 := segVal_lt d3
      have hDr : segVal D.2 rp.toNat (N + 1) = segVal A.2 rp.toNat (N + 1) :=
        segVal_congr fun i hi => d2 _ (by omega)
      -- the arithmetic of the step, over the integers
      have a5Z : (segVal A.2 rp.toNat (N + 1) : ℤ) + A.1.toNat * (base : ℤ) ^ (N + 1) =
          segVal st.2.2 rp.toNat (N + 1) + B := by exact_mod_cast a5
      have d5Z : (segVal D.2 qp.toNat QL : ℤ) + 1 =
          segVal st.2.2 qp.toNat QL + D.1.toNat * (base : ℤ) ^ QL := by exact_mod_cast d5
      have hA3Z : (segVal A.2 rp.toNat (N + 1) : ℤ) < (base : ℤ) ^ (N + 1) := by exact_mod_cast hA3
      have hD3Z : (segVal D.2 qp.toNat QL : ℤ) < (base : ℤ) ^ QL := by exact_mod_cast hD3
      have hAge : (0 : ℤ) ≤ segVal A.2 rp.toNat (N + 1) := by positivity
      have hDge : (0 : ℤ) ≤ segVal D.2 qp.toNat QL := by positivity
      have hVq0 : (0 : ℤ) ≤ segVal st.2.2 qp.toNat QL := by positivity
      have hjQ : (j : ℤ) < Q0 := by
        by_contra hcon
        push Not at hcon
        have : (Q0 : ℤ) * B ≤ j * B := mul_le_mul_of_nonneg_right hcon (le_of_lt hBp)
        linarith
      have hj1 : (((j + 1 : ℕ)) : ℤ) = j + 1 := by push_cast; ring
      have hframe : ∀ p, ¬ (rp.toNat ≤ p ∧ p < rp.toNat + N + 1) →
          ¬ (qp.toNat ≤ p ∧ p < qp.toNat + QL) → p ≠ sp.toNat → D.2[p]! = W[p]! :=
        fun p h1 h2 h3 => by rw [d2 p (by omega), a2 p (by omega)]; exact v2 p h1 h2 h3
      have hsp' : D.2[sp.toNat]! = 1 := by rw [d2 _ (by omega), hAsp]
      have hdr' : SegDigits D.2 rp.toNat (N + 1) := fun i hi => by
        rw [d2 _ (by omega)]; exact a3 i hi
      -- the top word of the quotient after the decrease
      have hc' : (st.2.1 - D.1).toNat + D.1.toNat = st.2.1.toNat ∧ (st.2.1 - D.1).toNat ≤ 1 := by
        rcases (show D.1.toNat = 0 ∨ D.1.toNat = 1 by omega) with hd | hd
        · rw [toNat_sub_le' (by omega), hd]; omega
        · rw [hd] at d5Z
          have hq0 : segVal st.2.2 qp.toNat QL = 0 := by
            have : (segVal st.2.2 qp.toNat QL : ℤ) ≤ 0 := by push_cast at d5Z; linarith
            omega
          have h1 : st.2.1.toNat = 1 := by
            rw [hq0] at v9
            by_contra hne
            have h0 : st.2.1.toNat = 0 := by omega
            rw [h0] at v9; push_cast at v9; linarith
          rw [toNat_sub_le' (by omega), h1, hd]; omega
      rcases (show (A.1 = 0 ∧ A.1.toNat = 0) ∨ (A.1 = 1 ∧ A.1.toNat = 1) by
          rcases (show A.1.toNat = 0 ∨ A.1.toNat = 1 by omega) with h | h
          · exact Or.inl ⟨UInt64.toNat_inj.mp (by rw [h]; rfl), h⟩
          · exact Or.inr ⟨UInt64.toNat_inj.mp (by rw [h]; rfl), h⟩) with
        ⟨hAc, hAc'⟩ | ⟨hAc, hAc'⟩
      · -- no carry: the difference stays negative
        rw [hAc', Nat.cast_zero, zero_mul, add_zero] at a5Z
        refine ⟨by rw [d1, a1, v1], hframe, hsp', hdr', d3, by simp [hAc], hc'.2, ?_, ?_,
          ?_, fun _ => by simpa using hneg⟩
        · rw [hDr, hAc, show (1 : UInt64) - 0 = 1 from rfl]
          push_cast at v8 a5Z ⊢; linarith
        · have : ((st.2.1 - D.1).toNat : ℤ) = st.2.1.toNat - D.1.toNat := by
            have := hc'.1; omega
          rw [this, hj1]; push_cast at v9 d5Z ⊢; linear_combination v9 + d5Z
        · rw [hAc, show (1 : UInt64) - 0 = 1 from rfl]
          constructor
          · intro _; rw [hj1]; push_cast at v8 a5Z ⊢; linarith
          · intro _; rfl
      · -- a carry: the difference became nonnegative
        rw [hAc', Nat.cast_one, one_mul] at a5Z
        refine ⟨by rw [d1, a1, v1], hframe, hsp', hdr', d3, by simp [hAc], hc'.2, ?_, ?_,
          ?_, fun _ => by simpa using hneg⟩
        · rw [hDr, hAc, show (1 : UInt64) - 1 = 0 from rfl]
          push_cast at v8 a5Z ⊢; linarith
        · have : ((st.2.1 - D.1).toNat : ℤ) = st.2.1.toNat - D.1.toNat := by
            have := hc'.1; omega
          rw [this, hj1]; push_cast at v9 d5Z ⊢; linear_combination v9 + d5Z
        · rw [hAc, show (1 : UInt64) - 1 = 0 from rfl]
          constructor
          · intro h; simp at h
          · intro h; rw [hj1] at h; push_cast at h v8 a5Z; linarith)
    (by
      rintro st ⟨-, -, -, -, -, v6, -, -, -, v10, -⟩
      have : st.1.toNat ≠ 1 := fun h => by
        have := v10.mp h; push_cast at this; linarith
      show (st.1 == 1) = false
      rw [beq_eq_false_iff_ne]
      intro h; exact this (by rw [h]; rfl))
  generalize hr : LeanExe.repeatWhile 4 (s.1, c, s.2.set! sp.toNat 1) (fun st => st.1 == 1)
    (fun st => ((1 : UInt64) - (addGen st.2.2 rp bp n rp (n + 1)).1,
      st.2.1 - (subGen (addGen st.2.2 rp bp n rp (n + 1)).2 qp sp 1 qp ql).1,
      (subGen (addGen st.2.2 rp bp n rp (n + 1)).2 qp sp 1 qp ql).2)) = r at hinv hcond
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := hinv
  have hb0 : r.1.toNat = 0 := by
    have h1 : r.1 ≠ 1 := by simpa using hcond
    have : r.1.toNat ≠ 1 := fun h => h1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
    omega
  rw [hb0, Nat.cast_zero, zero_mul, add_zero] at v8
  refine ⟨v1, v2, v4, v5, v7, j, by simpa using hj4, ?_, ?_, ?_⟩
  · exact v8
  · exact_mod_cast v9
  · rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exact Or.inl h0
    · right
      have h := v11 hpos
      have hjj : (((j - 1 : ℕ)) : ℤ) = j - 1 := by omega
      rw [hjj] at h
      have : (segVal r.2.2 rp.toNat (N + 1) : ℤ) < B := by rw [v8]; linarith
      exact_mod_cast this

/-- The low limbs of a segment are at most its value. -/
theorem segVal_le_of_le (W : Array UInt64) (p a b : ℕ) (h : a ≤ b) : segVal W p a ≤ segVal W p b := by
  rw [show b = a + (b - a) by omega, segVal_add]; exact Nat.le_add_right _ _

/-- A half of Algorithm 1.8: the product of the quotient `Q` by the low `k` limbs `B0` of the
divisor, subtracted from the `n + 1` limbs at `rp` with at most four corrections. -/
theorem halfStep_spec (t : UInt64) (W : Array UInt64) (rp bp n k qp ql c sp : UInt64)
    (N K QL AL : ℕ) (hn : n.toNat = N) (hk : k.toNat = K) (hql : ql.toNat = QL)
    (hAL : AL = (K + QL - 1) / QL * QL + QL + 1)
    (hW : W.size < 2 ^ 62) (hK1 : 1 ≤ K) (hKN : K ≤ N) (hQL : 1 ≤ QL) (hc : c.toNat ≤ 1)
    (hqb : qp.toNat + QL ≤ bp.toNat) (hbr : bp.toNat + N ≤ rp.toNat)
    (hrs : rp.toNat + N + 1 ≤ sp.toNat) (hsz : sp.toNat + 1 + AL + 10 * QL + 1 ≤ W.size)
    (hdr : SegDigits W rp.toNat (N + 1)) (hdb : SegDigits W bp.toNat N)
    (hdq : SegDigits W qp.toNat QL) (hBpos : 0 < segVal W bp.toNat N)
    (hP : (segVal W qp.toNat QL + c.toNat * base ^ QL) * segVal W bp.toNat K < base ^ (N + 1))
    (h4 : ((segVal W qp.toNat QL + c.toNat * base ^ QL) * segVal W bp.toNat K : ℕ) ≤
      (segVal W rp.toNat (N + 1) : ℤ) + 4 * segVal W bp.toNat N) :
    (halfStep t W rp bp n k qp ql c sp).2.size = W.size ∧
    (∀ p, ¬ (rp.toNat ≤ p ∧ p < rp.toNat + N + 1) → ¬ (qp.toNat ≤ p ∧ p < qp.toNat + QL) →
      ¬ (sp.toNat ≤ p ∧ p < sp.toNat + 1 + AL + 10 * QL + 1) →
      (halfStep t W rp bp n k qp ql c sp).2[p]! = W[p]!) ∧
    SegDigits (halfStep t W rp bp n k qp ql c sp).2 rp.toNat (N + 1) ∧
    SegDigits (halfStep t W rp bp n k qp ql c sp).2 qp.toNat QL ∧
    (halfStep t W rp bp n k qp ql c sp).1.toNat ≤ 1 ∧
    ∃ j : ℕ, j ≤ 4 ∧
      (segVal (halfStep t W rp bp n k qp ql c sp).2 rp.toNat (N + 1) : ℤ) =
        segVal W rp.toNat (N + 1) -
          ((segVal W qp.toNat QL + c.toNat * base ^ QL) * segVal W bp.toNat K : ℕ) +
          j * segVal W bp.toNat N ∧
      segVal (halfStep t W rp bp n k qp ql c sp).2 qp.toNat QL +
          (halfStep t W rp bp n k qp ql c sp).1.toNat * base ^ QL + j =
        segVal W qp.toNat QL + c.toNat * base ^ QL ∧
      (j = 0 ∨ segVal (halfStep t W rp bp n k qp ql c sp).2 rp.toNat (N + 1) <
        segVal W bp.toNat N) := by
  obtain ⟨NC, hNC⟩ : ∃ NC, NC = (K + QL - 1) / QL := ⟨_, rfl⟩
  rw [← hNC] at hAL
  obtain ⟨m1, m2, m3, m4⟩ := mulAcc_spec t W bp k qp ql c sp QL K NC AL hql hk hNC hAL hW hQL hK1
    hc (by omega) (by omega) hsz (hdb.mono hKN) hdq
  generalize hW1 : mulAcc t W bp k qp ql c sp = W1 at m1 m2 m3 m4
  have hal : ((k + ql - 1) / ql * ql + ql + 1).toNat = AL := by
    have hnc : ((k + ql - 1) / ql).toNat = NC := by
      rw [UInt64.toNat_div, toNat_sub_le' (by rw [toNat_add_lt] <;> simp <;> omega),
        toNat_add_lt (by omega), hql, hk, hNC]; rfl
    have hNCle : NC ≤ NC * QL := Nat.le_mul_of_pos_right _ (by omega)
    have hm : ((k + ql - 1) / ql * ql).toNat = NC * QL := by
      rw [toNat_mul_lt' (by rw [hnc, hql]; omega), hnc, hql]
    have hm1 : ((k + ql - 1) / ql * ql + ql).toNat = NC * QL + QL := by
      rw [toNat_add_lt (by rw [hm, hql]; omega), hm, hql]
    rw [toNat_add_lt (by rw [hm1]; simp; omega), hm1]; simp; omega
  have hW1W : ∀ p, p < sp.toNat + 1 → W1[p]! = W[p]! := fun p hp => m2 p (by omega)
  have hrW : segVal W1 rp.toNat (N + 1) = segVal W rp.toNat (N + 1) :=
    segVal_congr fun i hi => hW1W _ (by omega)
  have hbW : segVal W1 bp.toNat N = segVal W bp.toNat N :=
    segVal_congr fun i hi => hW1W _ (by omega)
  have hqW : segVal W1 qp.toNat QL = segVal W qp.toNat QL :=
    segVal_congr fun i hi => hW1W _ (by omega)
  have hB0 := segVal_le_of_le W bp.toNat K N hKN
  obtain ⟨f1, f2, f3, f4, f5, j, hj, f6, f7, f8⟩ := subFix_spec W1 rp bp n qp ql c sp
    ((k + ql - 1) / ql * ql + ql + 1) N QL AL hn hql hal (by omega) hQL hc hqb hbr hrs
    (by omega) (hdr.congr fun i hi => hW1W _ (by omega))
    (hdb.congr fun i hi => hW1W _ (by omega)) (hdq.congr fun i hi => hW1W _ (by omega)) m3
    (by rw [hbW]; exact hBpos) (by rw [m4]; exact hP) (by rw [m4, hrW, hbW]; exact h4)
    (by
      rw [m4, hrW, hbW, hqW]
      have : (segVal W qp.toNat QL + c.toNat * base ^ QL) * segVal W bp.toNat K ≤
          (segVal W qp.toNat QL + c.toNat * base ^ QL) * segVal W bp.toNat N :=
        Nat.mul_le_mul_left _ hB0
      push_cast at this ⊢
      have : (0 : ℤ) ≤ segVal W rp.toNat (N + 1) := by positivity
      linarith)
  rw [m4, hrW, hbW] at f6
  rw [hqW] at f7
  rw [hbW] at f8
  unfold halfStep
  rw [hW1]
  refine ⟨by rw [f1, m1], fun p h1 h2 h3 => by rw [f2 p h1 h2 (by omega), m2 p (by omega)],
    f3, f4, f5, j, hj, f6, f7, f8⟩

end Library.Numerics.Bignum
