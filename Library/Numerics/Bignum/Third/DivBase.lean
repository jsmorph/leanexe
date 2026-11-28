module

public import Library.Numerics.Bignum.Third.Program
public import Library.Numerics.Bignum.Second.Kara
public import Library.Numerics.MultiPrecision.DivideProof

@[expose] public section

/-!
The base case of the division, in place: Knuth's steps D3 (`trialAt_spec`), D4 (`mulSubSeg_spec`),
and D6, and Brent and Zimmermann's Algorithm 1.6 with them (`baseDiv_spec`).

`trialAt_spec` is MultiPrecision's `trial_spec` over segments of the workspace: for a window `X`
of `n + 1` limbs below `β V`, with `V` the normalized divisor of `n ≥ 2` limbs, the trial digit is
`X / V` or one more, and below `β`.  The bounds come from MultiPrecision's lemmas over numbers,
`quot_le_trial`, `quot_lt_of_tooBig`, `trial_le_quot_succ`, `passes_of_large`, and `top_lt`.
`mulSubSeg_spec` subtracts `q V` from the window with the final borrow.  `baseDiv_spec` states that
`baseDiv` leaves the remainder over the whole dividend's segment, so that the limbs above the
remainder are zeros, and the quotient in `m` limbs and a top word.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-! ## Step D3 -/

/-- The trial digit of step D3 over a window of the workspace is the quotient digit or one more. -/
theorem trialAt_spec (W : Array UInt64) (wp bp n : UInt64) (hn : 2 ≤ n.toNat)
    (hwn : wp.toNat + n.toNat < 2 ^ 63) (hbn : bp.toNat + n.toNat < 2 ^ 63)
    (hdw : SegDigits W wp.toNat (n.toNat + 1)) (hdb : SegDigits W bp.toNat n.toNat)
    (hv1 : base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat)
    (hX : segVal W wp.toNat (n.toNat + 1) < base * segVal W bp.toNat n.toNat) :
    segVal W wp.toNat (n.toNat + 1) / segVal W bp.toNat n.toNat ≤ (trialAt W wp bp n).toNat ∧
      (trialAt W wp bp n).toNat ≤
        segVal W wp.toNat (n.toNat + 1) / segVal W bp.toNat n.toNat + 1 ∧
      (trialAt W wp bp n).toNat < base := by
  obtain ⟨T, hT⟩ : ∃ T, n.toNat = T + 2 := ⟨n.toNat - 2, by omega⟩
  have hb := base_eq
  have hb0 := base_pos
  have i1 : (wp + n).toNat = wp.toNat + (T + 2) := by
    simp only [UInt64.toNat_add]; omega
  have i2 : (wp + n - 1).toNat = wp.toNat + (T + 1) := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  have i3 : (wp + n - 2).toNat = wp.toNat + T := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  have i4 : (bp + n - 1).toNat = bp.toNat + (T + 1) := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  have i5 : (bp + n - 2).toNat = bp.toNat + T := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [hT] at hX hv1 hdw hdb ⊢
  rw [show bp.toNat + (T + 2) - 1 = bp.toNat + (T + 1) by omega] at hv1
  have hXs : segVal W wp.toNat (T + 2 + 1) =
      ((W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat) * base +
        W[wp.toNat + T]!.toNat) * base ^ T + segVal W wp.toNat T := by
    rw [segVal_succ, segVal_succ, segVal_succ, pow_succ, pow_succ]; ring
  have hVs : segVal W bp.toNat (T + 2) =
      (W[bp.toNat + (T + 1)]!.toNat * base + W[bp.toNat + T]!.toNat) * base ^ T +
        segVal W bp.toNat T := by
    rw [segVal_succ, segVal_succ, pow_succ]; ring
  rw [hXs, hVs] at hX ⊢
  have hXl := segVal_lt (hdw.mono (k' := T) (by omega))
  have hVl := segVal_lt (hdb.mono (k' := T) (by omega))
  have hB : 0 < base ^ T := pow_pos hb0 T
  have hx2 := hdw (T + 2) (by omega)
  have hx1 := hdw (T + 1) (by omega)
  have hx0 := hdw T (by omega)
  have hv0 := hdb T (by omega)
  have hv1' := hdb (T + 1) (by omega)
  have htop := top_lt hb0 hv0 hVl hX
  have hn2 : (W[wp.toNat + (T + 2)]! * 4294967296 + W[wp.toNat + (T + 1)]!).toNat =
      W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat := by
    rw [hb] at hx2 hx1 ⊢
    have : W[wp.toNat + (T + 2)]!.toNat * 4294967296 ≤ 4294967295 * 4294967296 :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  unfold trialAt
  dsimp only
  rw [i1, i2, i3, i4, i5]
  generalize hQ : (W[wp.toNat + (T + 2)]! * 4294967296 + W[wp.toNat + (T + 1)]!) /
    W[bp.toNat + (T + 1)]! = Q0
  generalize hR : (W[wp.toNat + (T + 2)]! * 4294967296 + W[wp.toNat + (T + 1)]!) %
    W[bp.toNat + (T + 1)]! = R0
  have hQ0 : Q0.toNat = (W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat) /
      W[bp.toNat + (T + 1)]!.toNat := by rw [← hQ, UInt64.toNat_div, hn2]
  have hR0 : R0.toNat = (W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat) %
      W[bp.toNat + (T + 1)]!.toNat := by rw [← hR, UInt64.toNat_mod, hn2]
  have hv1p : 0 < W[bp.toNat + (T + 1)]!.toNat := by omega
  have hqr0 : Q0.toNat * W[bp.toNat + (T + 1)]!.toNat + R0.toNat =
      W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat := by
    rw [hQ0, hR0, Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hQb : Q0.toNat ≤ base + 1 := by
    rw [hQ0]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hv1p]
    nlinarith
  have hRb : R0.toNat < W[bp.toNat + (T + 1)]!.toNat := by rw [hR0]; exact Nat.mod_lt _ hv1p
  have hge := quot_le_trial (x2 := W[wp.toNat + (T + 2)]!.toNat)
    (x1 := W[wp.toNat + (T + 1)]!.toNat) (x0 := W[wp.toNat + T]!.toNat)
    (v0 := W[bp.toNat + T]!.toNat) (Vl := segVal W bp.toNat T) hb0 hB hx0 hXl hv1p
  rw [← hQ0] at hge
  have hRb' : R0.toNat < base := by omega
  have hR1 : (R0 + W[bp.toNat + (T + 1)]!).toNat = R0.toNat + W[bp.toNat + (T + 1)]!.toNat := by
    rw [hb] at hRb' hv1'; simp only [UInt64.toNat_add]; omega
  generalize hc : tooBig Q0 R0 W[wp.toNat + T]! W[bp.toNat + T]! = c0
  cases c0 with
  | false =>
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    have hn := (not_congr (tooBig_iff hQb hRb' hx0 hv0)).mp (by rw [hc]; decide)
    push Not at hn
    exact ⟨hge, trial_le_quot_succ hb0 hB hVl hv1p hqr0 hn.1 hn.2, hn.1⟩
  | true =>
    simp only [true_and, ↓reduceIte]
    have hlt0 := quot_lt_of_tooBig hXl hX hqr0 ((tooBig_iff hQb hRb' hx0 hv0).mp hc)
    have hQpos : 0 < Q0.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt0
    have hQ1 : (Q0 - 1).toNat = Q0.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        simp only [UInt64.reduceToNat]; omega))]
      simp only [UInt64.reduceToNat]
    have hqr1 : (Q0 - 1).toNat * W[bp.toNat + (T + 1)]!.toNat +
        (R0 + W[bp.toNat + (T + 1)]!).toNat =
        W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat := by
      rw [hQ1, hR1, ← hqr0]
      obtain ⟨k, hk⟩ : ∃ k, Q0.toNat = k + 1 := ⟨Q0.toNat - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]; ring
    have hcond : (R0 + W[bp.toNat + (T + 1)]! < 4294967296) ↔
        (R0 + W[bp.toNat + (T + 1)]!).toNat < base := by
      rw [UInt64.lt_iff_toNat_lt, hb]; rfl
    by_cases h2 : (R0 + W[bp.toNat + (T + 1)]!).toNat < base ∧
        tooBig (Q0 - 1) (R0 + W[bp.toNat + (T + 1)]!) W[wp.toNat + T]! W[bp.toNat + T]! = true
    · rw [ite_eq_left ⟨hcond.mpr h2.1, h2.2⟩]
      have hlt1 := quot_lt_of_tooBig hXl hX hqr1
        ((tooBig_iff (by omega) h2.1 hx0 hv0).mp h2.2)
      have hQ1pos : 0 < (Q0 - 1).toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt1
      have hQ2 : (Q0 - 1 - 1).toNat = Q0.toNat - 1 - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          simp only [UInt64.reduceToNat]; omega)), hQ1]
        simp only [UInt64.reduceToNat]
      have hqr2 : (Q0.toNat - 1 - 1) * W[bp.toNat + (T + 1)]!.toNat +
          ((R0 + W[bp.toNat + (T + 1)]!).toNat + W[bp.toNat + (T + 1)]!.toNat) =
          W[wp.toNat + (T + 2)]!.toNat * base + W[wp.toNat + (T + 1)]!.toNat := by
        rw [← hqr1, hQ1]
        obtain ⟨k, hk⟩ : ∃ k, Q0.toNat - 1 = k + 1 := ⟨Q0.toNat - 1 - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]; ring
      obtain ⟨hlt2, hpass⟩ := passes_of_large hb0 hv0 hX hVl hqr2 (by omega)
      rw [hQ2]
      exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr2 hlt2 hpass, hlt2⟩
    · rw [ite_eq_right fun h => h2 ⟨hcond.mp h.1, h.2⟩]
      rcases Nat.lt_or_ge (R0 + W[bp.toNat + (T + 1)]!).toNat base with hr | hr
      · have hn : ¬ (base ≤ (Q0 - 1).toNat ∨ base * (R0 + W[bp.toNat + (T + 1)]!).toNat +
            W[wp.toNat + T]!.toNat < (Q0 - 1).toNat * W[bp.toNat + T]!.toNat) :=
          fun h => h2 ⟨hr, (tooBig_iff (by omega) hr hx0 hv0).mpr h⟩
        push Not at hn
        exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr1 hn.1 hn.2, hn.1⟩
      · obtain ⟨hlt1, hpass⟩ := passes_of_large hb0 hv0 hX hVl hqr1 hr
        exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr1 hlt1 hpass, hlt1⟩

/-! ## Step D4 -/

/-- The invariant of step D4 after `i` limbs: the carry of the product, the borrow, and the
array, whose limbs from `wp` hold the difference so far. -/
def MulSubInv (W : Array UInt64) (wp bp n q : ℕ) (i : ℕ) (x : UInt64 × UInt64 × Array UInt64) :
    Prop :=
  x.2.2.size = W.size ∧ (∀ p, (p < wp ∨ wp + i ≤ p) → x.2.2[p]! = W[p]!) ∧
    SegDigits x.2.2 wp i ∧ x.2.1.toNat ≤ 1 ∧ x.1.toNat < base ∧
    x.1.toNat * base ^ i ≤ q * segVal W bp (min i n) ∧
    segVal x.2.2 wp i + q * segVal W bp (min i n) = segVal W wp i + (x.2.1.toNat + x.1.toNat) * base ^ i

/-- Step D4: `mulSubSeg` subtracts `q` times the `n` limbs at `bp` from the `n + 1` limbs at `wp`,
with the final borrow. -/
theorem mulSubSeg_spec (W : Array UInt64) (wp bp n q : UInt64) (hW : W.size < 2 ^ 64)
    (hwp : wp.toNat + n.toNat + 1 ≤ W.size) (hbp : bp.toNat + n.toNat ≤ W.size)
    (hdw : SegDigits W wp.toNat (n.toNat + 1)) (hdb : SegDigits W bp.toNat n.toNat)
    (hq : q.toNat < base) (hsep : bp.toNat + n.toNat ≤ wp.toNat ∨ wp.toNat + n.toNat + 1 ≤ bp.toNat) :
    (mulSubSeg W wp bp n q).2.size = W.size ∧
    (∀ p, (p < wp.toNat ∨ wp.toNat + n.toNat + 1 ≤ p) → (mulSubSeg W wp bp n q).2[p]! = W[p]!) ∧
    SegDigits (mulSubSeg W wp bp n q).2 wp.toNat (n.toNat + 1) ∧
    (mulSubSeg W wp bp n q).1.toNat ≤ 1 ∧
    segVal (mulSubSeg W wp bp n q).2 wp.toNat (n.toNat + 1) + q.toNat * segVal W bp.toNat n.toNat =
      segVal W wp.toNat (n.toNat + 1) + (mulSubSeg W wp bp n q).1.toNat * base ^ (n.toNat + 1) := by
  have hb := base_eq
  have hn1 : (n + 1).toNat = n.toNat + 1 := by rw [toNat_add_lt] <;> simp <;> omega
  have key := loop_induction (n := n + 1) (init := ((0 : UInt64), (0 : UInt64), W))
    (f := fun i x =>
      ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) >>> 32,
        (1 : UInt64) - ((x.2.2[(wp + i).toNat]! + 4294967296 -
          ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) &&& 0xFFFFFFFF) - x.2.1) >>> 32),
        x.2.2.set! (wp + i).toNat ((x.2.2[(wp + i).toNat]! + 4294967296 -
          ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) &&& 0xFFFFFFFF) - x.2.1) &&&
            0xFFFFFFFF)))
    (MulSubInv W wp.toNat bp.toNat n.toNat q.toNat)
    ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), by simp, by simp [base_pos],
      by simp, by simp [segVal]⟩ (by
    intro i x hi ⟨hs, hfr, hdg, hbr, hc, hcb, hv⟩
    rw [hn1] at hi
    have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
    have hwi : (wp + UInt64.ofNat i).toNat = wp.toNat + i := by rw [toNat_add_lt] <;> omega
    have hWi : x.2.2[wp.toNat + i]! = W[wp.toNat + i]! := hfr _ (by omega)
    have hXd := hdw i hi
    rw [hb] at hXd hc
    -- the multiplier's limb
    obtain ⟨Y, hYt, hYv, hYlt⟩ : ∃ Y : ℕ,
        (if UInt64.ofNat i < n then x.2.2[(bp + UInt64.ofNat i).toNat]! else 0).toNat = Y ∧
        segVal W bp.toNat (min (i + 1) n.toNat) = segVal W bp.toNat (min i n.toNat) + Y * base ^ i ∧
        Y < 4294967296 := by
      by_cases hin : i < n.toNat
      · have hbi : (bp + UInt64.ofNat i).toNat = bp.toNat + i := by rw [toNat_add_lt] <;> omega
        have hY : x.2.2[bp.toNat + i]! = W[bp.toNat + i]! := hfr _ (by omega)
        have hYd := hdb i hin
        rw [hb] at hYd
        refine ⟨W[bp.toNat + i]!.toNat, ?_, ?_, hYd⟩
        · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hin), hbi, hY]
        · rw [show min (i + 1) n.toNat = min i n.toNat + 1 by omega, segVal_succ,
            show min i n.toNat = i by omega]
      · refine ⟨0, ?_, ?_, by norm_num⟩
        · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hin)]; rfl
        · rw [show min (i + 1) n.toNat = min i n.toNat by omega]; simp
    rw [hwi]
    have hqY : q.toNat * Y ≤ 4294967295 * 4294967295 := by
      rw [hb] at hq; exact Nat.mul_le_mul (by omega) (by omega)
    have hp : (q * (if UInt64.ofNat i < n then x.2.2[(bp + UInt64.ofNat i).toNat]! else 0) +
        x.1).toNat = q.toNat * Y + x.1.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hYt]
      have : q.toNat * Y % 2 ^ 64 = q.toNat * Y := Nat.mod_eq_of_lt (by omega)
      rw [this]; omega
    generalize (q * (if UInt64.ofNat i < n then x.2.2[(bp + UInt64.ofNat i).toNat]! else 0) +
      x.1) = P at hp
    have hPm : (P &&& 0xFFFFFFFF).toNat = P.toNat % base := and_mask P
    have hPm' : P.toNat % base < 4294967296 := by rw [hb]; exact Nat.mod_lt _ (by norm_num)
    have hr : (x.2.2[wp.toNat + i]! + 4294967296 - (P &&& 0xFFFFFFFF) - x.2.1).toNat =
        W[wp.toNat + i]!.toNat + 4294967296 - P.toNat % base - x.2.1.toNat := by
      have h1 : (x.2.2[wp.toNat + i]! + 4294967296).toNat = W[wp.toNat + i]!.toNat + 4294967296 := by
        rw [UInt64.toNat_add, hWi]; simp only [UInt64.reduceToNat]; omega
      rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, h1, hPm]
      · rw [UInt64.le_iff_toNat_le, h1, hPm]; omega
      · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, h1, hPm]
        · omega
        · rw [UInt64.le_iff_toNat_le, h1, hPm]; omega
    generalize (x.2.2[wp.toNat + i]! + 4294967296 - (P &&& 0xFFFFFFFF) - x.2.1) = R at hr
    have hdin : wp.toNat + i < x.2.2.size := by omega
    have hget := fun p => get_set x.2.2 (wp.toNat + i) (R &&& 0xFFFFFFFF) p hdin
    have hRq : R.toNat / base ≤ 1 := by rw [hr, hb]; omega
    have hbrw : ((1 : UInt64) - R >>> 32).toNat = 1 - R.toNat / base := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, shr32]; simpa using hRq), shr32]
      rfl
    refine ⟨by simp [hs], fun p hp' => ?_, fun i' hi' => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hget, if_neg (by omega)]; exact hfr p (by omega)
    · rw [hget]
      split
      · rw [and_mask]; exact Nat.mod_lt _ base_pos
      · exact hdg i' (by omega)
    · rw [hbrw]; exact Nat.sub_le _ _
    · rw [shr32, hp, hb]
      have : q.toNat * Y + x.1.toNat < 4294967296 * 4294967296 := by omega
      omega
    · rw [shr32, hp, pow_succ, hYv]
      have h1 : (q.toNat * Y + x.1.toNat) / base * base ≤ q.toNat * Y + x.1.toNat :=
        Nat.div_mul_le_self _ _
      calc (q.toNat * Y + x.1.toNat) / base * (base ^ i * base)
          = (q.toNat * Y + x.1.toNat) / base * base * base ^ i := by ring
        _ ≤ (q.toNat * Y + x.1.toNat) * base ^ i := Nat.mul_le_mul_right _ h1
        _ = q.toNat * Y * base ^ i + x.1.toNat * base ^ i := by ring
        _ ≤ q.toNat * (segVal W bp.toNat (min i n.toNat) + Y * base ^ i) := by nlinarith
    · have hcongr : segVal (x.2.2.set! (wp.toNat + i) (R &&& 0xFFFFFFFF)) wp.toNat i =
          segVal x.2.2 wp.toNat i :=
        segVal_congr fun i' hi' => by rw [hget, if_neg (by omega)]
      rw [segVal_succ, hcongr, hget, if_pos rfl, and_mask, hbrw, shr32, segVal_succ, hYv, hp,
        pow_succ]
      have hdm := Nat.mod_add_div R.toNat base
      have hdp := Nat.mod_add_div (q.toNat * Y + x.1.toNat) base
      have hr' : R.toNat + P.toNat % base + x.2.1.toNat = W[wp.toNat + i]!.toNat + base := by
        rw [hr, hb]; omega
      rw [hp] at hr'
      obtain hq0 | hq1 : R.toNat / base = 0 ∨ R.toNat / base = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp hRq
      · rw [hq0] at hdm ⊢
        zify at hv hdm hdp hr' ⊢
        linear_combination hv + (base : ℤ) ^ i * hdm - (base : ℤ) ^ i * hdp + (base : ℤ) ^ i * hr'
      · rw [hq1] at hdm ⊢
        zify at hv hdm hdp hr' ⊢
        linear_combination hv + (base : ℤ) ^ i * hdm - (base : ℤ) ^ i * hdp + (base : ℤ) ^ i * hr')
  rw [hn1] at key
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := key
  rw [show min (n.toNat + 1) n.toNat = n.toNat by omega] at h6 h7
  -- the final carry is 0
  have hBl := segVal_lt hdb
  have hc0 : (LeanExe.loop (n + 1) ((0 : UInt64), (0 : UInt64), W) fun i x =>
      ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) >>> 32,
        (1 : UInt64) - ((x.2.2[(wp + i).toNat]! + 4294967296 -
          ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) &&& 0xFFFFFFFF) - x.2.1) >>> 32),
        x.2.2.set! (wp + i).toNat ((x.2.2[(wp + i).toNat]! + 4294967296 -
          ((q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1) &&& 0xFFFFFFFF) - x.2.1) &&&
            0xFFFFFFFF))).1.toNat = 0 := by
    by_contra hne
    have h8 : base ^ (n.toNat + 1) ≤ _ * base ^ (n.toNat + 1) := Nat.le_mul_of_pos_left _
      (Nat.pos_of_ne_zero hne)
    have h9 : q.toNat * segVal W bp.toNat n.toNat < base ^ (n.toNat + 1) := by
      rw [pow_succ]
      calc q.toNat * segVal W bp.toNat n.toNat ≤ q.toNat * base ^ n.toNat :=
            Nat.mul_le_mul_left _ (le_of_lt hBl)
        _ < base * base ^ n.toNat := Nat.mul_lt_mul_of_pos_right hq (pow_pos base_pos _)
        _ = base ^ n.toNat * base := by ring
    omega
  rw [hc0, Nat.add_zero] at h7
  exact ⟨h1, h2, h3, h4, h7⟩

/-! ## Additions and subtractions in place -/

/-- `addGen` in place, with the second operand apart from the first. -/
theorem addGen_inplace (W : Array UInt64) (xp yp k n : UInt64) (hW : W.size < 2 ^ 64)
    (hx : xp.toNat + n.toNat ≤ W.size) (hy : yp.toNat + min k.toNat n.toNat ≤ W.size)
    (hdx : SegDigits W xp.toNat n.toNat) (hdy : SegDigits W yp.toNat (min k.toNat n.toNat))
    (hsep : yp.toNat + min k.toNat n.toNat ≤ xp.toNat ∨ xp.toNat + n.toNat ≤ yp.toNat) :
    (addGen W xp yp k xp n).2.size = W.size ∧
    (∀ q, (q < xp.toNat ∨ xp.toNat + n.toNat ≤ q) → (addGen W xp yp k xp n).2[q]! = W[q]!) ∧
    SegDigits (addGen W xp yp k xp n).2 xp.toNat n.toNat ∧ (addGen W xp yp k xp n).1.toNat ≤ 1 ∧
    segVal (addGen W xp yp k xp n).2 xp.toNat n.toNat +
        (addGen W xp yp k xp n).1.toNat * base ^ n.toNat =
      segVal W xp.toNat n.toNat + segVal W yp.toNat (min k.toNat n.toNat) :=
  addGen_spec W xp yp k xp n hW hx hy hx hdx hdy (fun i j hij _ => by omega)
    (fun i j _ hj => by omega)

/-- `subGen` in place, with the second operand apart from the first. -/
theorem subGen_inplace (W : Array UInt64) (xp yp k n : UInt64) (hW : W.size < 2 ^ 64)
    (hx : xp.toNat + n.toNat ≤ W.size) (hy : yp.toNat + min k.toNat n.toNat ≤ W.size)
    (hdx : SegDigits W xp.toNat n.toNat) (hdy : SegDigits W yp.toNat (min k.toNat n.toNat))
    (hsep : yp.toNat + min k.toNat n.toNat ≤ xp.toNat ∨ xp.toNat + n.toNat ≤ yp.toNat) :
    (subGen W xp yp k xp n).2.size = W.size ∧
    (∀ q, (q < xp.toNat ∨ xp.toNat + n.toNat ≤ q) → (subGen W xp yp k xp n).2[q]! = W[q]!) ∧
    SegDigits (subGen W xp yp k xp n).2 xp.toNat n.toNat ∧ (subGen W xp yp k xp n).1.toNat ≤ 1 ∧
    segVal (subGen W xp yp k xp n).2 xp.toNat n.toNat + segVal W yp.toNat (min k.toNat n.toNat) =
      segVal W xp.toNat n.toNat + (subGen W xp yp k xp n).1.toNat * base ^ n.toNat :=
  subGen_spec W xp yp k xp n hW hx hy hx hdx hdy (fun i j hij _ => by omega)
    (fun i j _ hj => by omega)

/-- `addGen` with no second operand copies the `n` limbs at `xp` to the `n` limbs at `dp`. -/
theorem addGen_copy (W : Array UInt64) (xp yp dp n : UInt64) (hW : W.size < 2 ^ 64)
    (hx : xp.toNat + n.toNat ≤ W.size) (hy : yp.toNat ≤ W.size) (hd : dp.toNat + n.toNat ≤ W.size)
    (hdx : SegDigits W xp.toNat n.toNat)
    (hsep : dp.toNat + n.toNat ≤ xp.toNat ∨ xp.toNat + n.toNat ≤ dp.toNat ∨ dp = xp) :
    (addGen W xp yp 0 dp n).2.size = W.size ∧
    (∀ q, (q < dp.toNat ∨ dp.toNat + n.toNat ≤ q) → (addGen W xp yp 0 dp n).2[q]! = W[q]!) ∧
    SegDigits (addGen W xp yp 0 dp n).2 dp.toNat n.toNat ∧
    segVal (addGen W xp yp 0 dp n).2 dp.toNat n.toNat = segVal W xp.toNat n.toNat := by
  have h := addGen_spec W xp yp 0 dp n hW hx (by simp; omega) hd hdx (fun i hi => by simp at hi)
    (fun i j hij hj => by
      rcases hsep with h | h | h
      · omega
      · omega
      · subst h; omega)
    (fun i j _ hj => by simp at hj)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hlt := segVal_lt h3
  have hlx := segVal_lt hdx
  simp only [UInt64.toNat_zero, Nat.zero_min, segVal_zero, Nat.add_zero] at h5
  have hc : (addGen W xp yp 0 dp n).1.toNat = 0 := by
    by_contra hne
    have : base ^ n.toNat ≤ (addGen W xp yp 0 dp n).1.toNat * base ^ n.toNat :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  rw [hc, Nat.zero_mul, Nat.add_zero] at h5
  exact ⟨h1, h2, h3, h5⟩

/-! ## The loop of `baseDiv` -/

/-- The invariant of the loop of `baseDiv` once the quotient limbs from `J` on are written: they
hold `A / (B β^J)`, and the dividend's segment holds `A % (B β^J)`. -/
def BaseInv (W0 : Array UInt64) (ap qp n m A B J : ℕ) (W : Array UInt64) : Prop :=
  W.size = W0.size ∧
  (∀ p, ¬ (ap ≤ p ∧ p < ap + n + m) → ¬ (qp + J ≤ p ∧ p < qp + m) → W[p]! = W0[p]!) ∧
  SegDigits W ap (n + m) ∧ SegDigits W (qp + J) (m - J) ∧
  segVal W (qp + J) (m - J) = A / (B * base ^ J) ∧ segVal W ap (n + m) = A % (B * base ^ J)

/-- The dividend's segment under the invariant at `j + 1`: its limbs below `j`, the window of
`n + 1` limbs from `j`, and zeros above. -/
theorem BaseInv.split {W0 W : Array UInt64} {ap qp n m A B j : ℕ}
    (hinv : BaseInv W0 ap qp n m A B (j + 1) W) (hj : j < m) (hBpos : 0 < B)
    (hBlt : B < base ^ n) :
    segVal W ap (n + m) = segVal W ap j + base ^ j * segVal W (ap + j) (n + 1) ∧
      segVal W (ap + j + (n + 1)) (m - j - 1) = 0 := by
  obtain ⟨-, -, hda, -, -, hrv⟩ := hinv
  have he : n + m = j + (n + 1) + (m - j - 1) := by omega
  have hlt : segVal W ap (j + (n + 1) + (m - j - 1)) < base ^ (j + (n + 1)) := by
    rw [← he, hrv]
    calc A % (B * base ^ (j + 1)) < B * base ^ (j + 1) :=
          Nat.mod_lt _ (Nat.mul_pos hBpos (pow_pos base_pos _))
      _ ≤ base ^ n * base ^ (j + 1) := Nat.mul_le_mul_right _ (le_of_lt hBlt)
      _ = base ^ (j + (n + 1)) := by rw [← pow_add]; congr 1; omega
  have hda' : SegDigits W ap (j + (n + 1) + (m - j - 1)) := by rw [← he]; exact hda
  have hz : segVal W (ap + (j + (n + 1))) (m - j - 1) = 0 := segVal_high_zero hda' hlt
  refine ⟨?_, by rw [Nat.add_assoc]; exact hz⟩
  rw [he, segVal_add W ap (j + (n + 1)) (m - j - 1), hz, Nat.mul_zero, Nat.add_zero,
    segVal_add W ap j (n + 1)]

/-- The end of a step of the loop: the window of `n + 1` limbs at `j` replaced by its remainder
`X % B` and the quotient digit `X / B` written at `qp + j` give the invariant at `j`. -/
theorem baseStep_finish {W0 W W3 : Array UInt64} {ap qp n m A B j : ℕ} (d : UInt64)
    (hinv : BaseInv W0 ap qp n m A B (j + 1) W) (hj : j < m) (hBpos : 0 < B)
    (hBlt : B < base ^ n) (hqa : qp + m ≤ ap) (hsz : ap + n + m ≤ W0.size)
    (hd : d.toNat = segVal W (ap + j) (n + 1) / B) (h3s : W3.size = W.size)
    (h3fr : ∀ p, (p < ap + j ∨ ap + j + (n + 1) ≤ p) → W3[p]! = W[p]!)
    (h3d : SegDigits W3 (ap + j) (n + 1))
    (h3v : segVal W3 (ap + j) (n + 1) = segVal W (ap + j) (n + 1) % B) :
    BaseInv W0 ap qp n m A B j (W3.set! (qp + j) d) := by
  obtain ⟨hsp, hz⟩ := hinv.split hj hBpos hBlt
  obtain ⟨hs, hfr, hda, hdq, hqv, hrv⟩ := hinv
  have hb0 := base_pos
  generalize hX : segVal W (ap + j) (n + 1) = X at hsp hd h3v
  generalize hL : segVal W ap j = L at hsp
  have hLlt : L < base ^ j := by rw [← hL]; exact segVal_lt (hda.mono (by omega))
  have hBj : 0 < base ^ j := pow_pos hb0 j
  have hXlt : X < base * B := by
    have h1 : base ^ j * X < base ^ j * (base * B) := by
      calc base ^ j * X ≤ segVal W ap (n + m) := by rw [hsp]; omega
        _ = A % (B * base ^ (j + 1)) := hrv
        _ < B * base ^ (j + 1) := Nat.mod_lt _ (Nat.mul_pos hBpos (pow_pos hb0 _))
        _ = base ^ j * (base * B) := by rw [pow_succ]; ring
    exact Nat.lt_of_mul_lt_mul_left h1
  have hin : qp + j < W3.size := by omega
  have hget := fun p => get_set W3 (qp + j) d p hin
  -- the words of the result outside the window and the digit
  have hout : ∀ p, (p < ap + j ∨ ap + j + (n + 1) ≤ p) → p ≠ qp + j →
      (W3.set! (qp + j) d)[p]! = W[p]! := fun p hp hne => by
    rw [hget, if_neg hne]; exact h3fr p hp
  have hwin : ∀ i, i < n + 1 → (W3.set! (qp + j) d)[ap + j + i]! = W3[ap + j + i]! := fun i hi => by
    rw [hget, if_neg (by omega)]
  refine ⟨by simp [h3s, hs], fun p hp1 hp2 => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [hout p (by omega) (by omega)]
    exact hfr p hp1 (by omega)
  · by_cases hiw : ap + j ≤ ap + i ∧ ap + i < ap + j + (n + 1)
    · have := hwin (i - j) (by omega)
      rw [show ap + j + (i - j) = ap + i by omega] at this
      rw [this]
      have := h3d (i - j) (by omega)
      rwa [show ap + j + (i - j) = ap + i by omega] at this
    · rw [hout (ap + i) (by omega) (by omega)]; exact hda i hi
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [Nat.add_zero, hget, if_pos rfl, hd]
      exact (Nat.div_lt_iff_lt_mul hBpos).mpr hXlt
    · rw [hout (qp + j + i) (by omega) (by omega)]
      have := hdq (i - 1) (by omega)
      rwa [show qp + (j + 1) + (i - 1) = qp + j + i by omega] at this
  · -- the quotient limbs
    have hsplit : segVal (W3.set! (qp + j) d) (qp + j) (m - j) =
        d.toNat + base * segVal W (qp + (j + 1)) (m - (j + 1)) := by
      rw [show m - j = 1 + (m - (j + 1)) by omega, segVal_add]
      have h1 : segVal (W3.set! (qp + j) d) (qp + j) 1 = d.toNat := by
        simp only [segVal, Nat.add_zero, pow_zero, Nat.mul_one, Nat.zero_add]
        rw [hget, if_pos rfl]
      rw [h1, pow_one, show qp + j + 1 = qp + (j + 1) by omega]
      congr 2
      exact segVal_congr fun i hi => by
        rw [hout (qp + (j + 1) + i) (by omega) (by omega)]
    rw [hsplit, hqv, hd]
    have hdiv : A % (B * base ^ (j + 1)) / (B * base ^ j) = X / B := by
      rw [← hrv, hsp, Nat.mul_comm B, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hBj, Nat.div_eq_of_lt hLlt, Nat.zero_add]
    rw [div_split A (B * base ^ j) base, show B * base ^ j * base = B * base ^ (j + 1) by
      rw [pow_succ]; ring, hdiv]
    ring
  · -- the remainder
    have hsplit' : segVal (W3.set! (qp + j) d) ap (n + m) = L + base ^ j * (X % B) := by
      have he : n + m = j + (n + 1) + (m - j - 1) := by omega
      rw [he, segVal_add _ ap (j + (n + 1)) (m - j - 1), segVal_add _ ap j (n + 1)]
      have e1 : segVal (W3.set! (qp + j) d) ap j = L := by
        rw [← hL]; exact segVal_congr fun i hi => hout (ap + i) (by omega) (by omega)
      have e2 : segVal (W3.set! (qp + j) d) (ap + j) (n + 1) = X % B := by
        rw [← h3v]; exact segVal_congr fun i hi => hwin i hi
      have e3 : segVal (W3.set! (qp + j) d) (ap + (j + (n + 1))) (m - j - 1) = 0 := by
        rw [← hz]; exact segVal_congr fun i hi => by
          rw [show ap + j + (n + 1) + i = ap + (j + (n + 1)) + i by omega]
          exact hout _ (by omega) (by omega)
      rw [e1, e2, e3]; ring
    rw [hsplit']
    have hU := Nat.div_add_mod A (B * base ^ (j + 1))
    rw [← hrv, hsp] at hU
    have hXV := Nat.div_add_mod X B
    have hXm := Nat.mod_lt X hBpos
    have h1 : base ^ j * (X % B) + base ^ j ≤ B * base ^ j := by
      calc base ^ j * (X % B) + base ^ j = (X % B + 1) * base ^ j := by ring
        _ ≤ B * base ^ j := Nat.mul_le_mul_right _ hXm
    have hbound : L + base ^ j * (X % B) < B * base ^ j := by omega
    have hU' : A = (L + base ^ j * (X % B)) +
        (A / (B * base ^ (j + 1)) * base + X / B) * (B * base ^ j) := by
      zify at hU hXV ⊢
      linear_combination -hU - ((base : ℤ) ^ j) * hXV
    rw [hU', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbound]

/-- A normalized divisor of `n` limbs is at least `β^n / 2`, and positive. -/
theorem normalized_ge {W : Array UInt64} {bp n : ℕ} (hn : 1 ≤ n) (hdb : SegDigits W bp n)
    (hv1 : base ≤ 2 * W[bp + n - 1]!.toNat) :
    base ^ n ≤ 2 * segVal W bp n ∧ 0 < segVal W bp n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show bp + (k + 1) - 1 = bp + k by omega] at hv1
  rw [segVal_succ, pow_succ]
  have h1 : base * base ^ k ≤ 2 * (W[bp + k]!.toNat * base ^ k) := by
    calc base * base ^ k ≤ 2 * W[bp + k]!.toNat * base ^ k := Nat.mul_le_mul_right _ hv1
      _ = 2 * (W[bp + k]!.toNat * base ^ k) := by ring
  have h2 : 0 < W[bp + k]!.toNat * base ^ k := Nat.mul_pos (by
    have := base_pos; omega) (pow_pos base_pos _)
  constructor
  · calc base ^ k * base = base * base ^ k := by ring
      _ ≤ 2 * (W[bp + k]!.toNat * base ^ k) := h1
      _ ≤ 2 * (segVal W bp k + W[bp + k]!.toNat * base ^ k) := by omega
  · omega

/-- One step of the loop of `baseDiv`, from the invariant at `j + 1` to the invariant at `j`. -/
theorem baseStep (W0 W : Array UInt64) (ap bp qp n jj : UInt64) (m A : ℕ)
    (hW : W0.size < 2 ^ 62) (hn : 2 ≤ n.toNat) (hj : jj.toNat < m)
    (hqb : qp.toNat + m ≤ bp.toNat) (hba : bp.toNat + n.toNat ≤ ap.toNat)
    (hsz : ap.toNat + n.toNat + m ≤ W0.size) (hdb : SegDigits W0 bp.toNat n.toNat)
    (hv1 : base ≤ 2 * W0[bp.toNat + n.toNat - 1]!.toNat)
    (hinv : BaseInv W0 ap.toNat qp.toNat n.toNat m A (segVal W0 bp.toNat n.toNat)
      (jj.toNat + 1) W) :
    BaseInv W0 ap.toNat qp.toNat n.toNat m A (segVal W0 bp.toNat n.toNat) jj.toNat
      (let qh := trialAt W (ap + jj) bp n
       let ms := mulSubSeg W (ap + jj) bp n qh
       if ms.1 == 1 then
         (addGen ms.2 (ap + jj) bp n (ap + jj) (n + 1)).2.set! (qp + jj).toNat (qh - 1)
       else ms.2.set! (qp + jj).toNat qh) := by
  dsimp only
  have hinv' := hinv
  obtain ⟨hs, hfr, hda, hdq, hqv, hrv⟩ := hinv'
  generalize hB : segVal W0 bp.toNat n.toNat = B at hinv hrv hqv
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  rw [hB] at hBge hBpos
  have hBlt : B < base ^ n.toNat := by rw [← hB]; exact segVal_lt hdb
  -- the divisor is unchanged in `W`
  have hWb : ∀ i, i < n.toNat → W[bp.toNat + i]! = W0[bp.toNat + i]! := fun i hi =>
    hfr _ (by omega) (by omega)
  have hBW : segVal W bp.toNat n.toNat = B := by rw [← hB]; exact segVal_congr hWb
  have hdbW : SegDigits W bp.toNat n.toNat := hdb.congr hWb
  have hv1W : base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat := by
    rw [show bp.toNat + n.toNat - 1 = bp.toNat + (n.toNat - 1) by omega,
      hWb _ (by omega), show bp.toNat + (n.toNat - 1) = bp.toNat + n.toNat - 1 by omega]
    exact hv1
  have hj' : (ap + jj).toNat = ap.toNat + jj.toNat := by rw [toNat_add_lt] <;> omega
  have hqj : (qp + jj).toNat = qp.toNat + jj.toNat := by rw [toNat_add_lt] <;> omega
  obtain ⟨hsp, -⟩ := hinv.split hj hBpos hBlt
  have hdw : SegDigits W (ap.toNat + jj.toNat) (n.toNat + 1) := fun i hi => by
    have := hda (jj.toNat + i) (by omega); rwa [← Nat.add_assoc] at this
  generalize hX : segVal W (ap.toNat + jj.toNat) (n.toNat + 1) = X at hsp
  have hXlt : X < base * B := by
    have h1 : base ^ jj.toNat * X < base ^ jj.toNat * (base * B) := by
      calc base ^ jj.toNat * X ≤ segVal W ap.toNat (n.toNat + m) := by rw [hsp]; omega
        _ = A % (B * base ^ (jj.toNat + 1)) := hrv
        _ < B * base ^ (jj.toNat + 1) := Nat.mod_lt _ (Nat.mul_pos hBpos (pow_pos base_pos _))
        _ = base ^ jj.toNat * (base * B) := by rw [pow_succ]; ring
    exact Nat.lt_of_mul_lt_mul_left h1
  -- step D3
  obtain ⟨hq1, hq2, hq3⟩ := trialAt_spec W (ap + jj) bp n hn (by omega) (by omega)
    (by rw [hj']; exact hdw) hdbW hv1W (by rw [hj', hX, hBW]; exact hXlt)
  rw [hj', hX, hBW] at hq1 hq2
  generalize hqh : trialAt W (ap + jj) bp n = qh at hq1 hq2 hq3
  -- step D4
  obtain ⟨m1, m2, m3, m4, m5⟩ := mulSubSeg_spec W (ap + jj) bp n qh (by omega)
    (by rw [hj']; omega) (by omega) (by rw [hj']; exact hdw) hdbW hq3 (by rw [hj']; omega)
  rw [hj', hX, hBW] at m5
  rw [hj'] at m2 m3
  generalize hms : mulSubSeg W (ap + jj) bp n qh = ms at m1 m2 m3 m4 m5
  have hXs := segVal_lt m3
  have hqB : qh.toNat * B < base ^ (n.toNat + 1) := by
    rw [pow_succ]
    calc qh.toNat * B < base * B := Nat.mul_lt_mul_of_pos_right hq3 hBpos
      _ ≤ base * base ^ n.toNat := Nat.mul_le_mul_left _ (le_of_lt hBlt)
      _ = base ^ n.toNat * base := by ring
  have hXV := Nat.div_add_mod' X B
  have hXm := Nat.mod_lt X hBpos
  by_cases hb1 : ms.1 = 1
  · have hb1' : ms.1.toNat = 1 := by rw [hb1]; rfl
    rw [hb1', Nat.one_mul] at m5
    rw [if_pos (by rw [hb1]; rfl)]
    have hlt : X < qh.toNat * B := by omega
    have hqq : qh.toNat = X / B + 1 := by
      have : X / B < qh.toNat := (Nat.div_lt_iff_lt_mul hBpos).mpr hlt
      omega
    -- step D6
    have hmb : ∀ i, i < n.toNat → ms.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
      m2 _ (by omega)
    have hn1 : (n + 1).toNat = n.toNat + 1 := by rw [toNat_add_lt (by simp; omega)]; simp
    have hmin : min n.toNat (n + 1).toNat = n.toNat := by rw [hn1]; omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := addGen_inplace ms.2 (ap + jj) bp n (n + 1) (by omega)
      (by rw [hj', m1, hn1]; omega) (by rw [m1, hmin]; omega) (by rw [hj', hn1]; exact m3)
      (by rw [hmin]; exact hdbW.congr hmb) (by rw [hmin, hj', hn1]; omega)
    rw [hj', hmin, hn1, segVal_congr (W := ms.2) (W' := W) (p := bp.toNat) (p' := bp.toNat)
      hmb, hBW] at a5
    rw [hj', hn1] at a2 a3
    have hw2 : segVal (addGen ms.2 (ap + jj) bp n (ap + jj) (n + 1)).2
        (ap.toNat + jj.toNat) (n.toNat + 1) = X % B := by
      have ha3 := segVal_lt a3
      rw [hqq, Nat.succ_mul] at m5
      rcases (show (addGen ms.2 (ap + jj) bp n (ap + jj) (n + 1)).1.toNat = 0 ∨
          (addGen ms.2 (ap + jj) bp n (ap + jj) (n + 1)).1.toNat = 1 by omega) with h | h
      · rw [h, Nat.zero_mul, Nat.add_zero] at a5; omega
      · rw [h, Nat.one_mul] at a5; omega
    have hd : (qh - 1).toNat = X / B := by
      have h1 : (1 : UInt64) ≤ qh := UInt64.le_iff_toNat_le.mpr (by
        rw [hqq]; exact Nat.le_add_left _ _)
      rw [UInt64.toNat_sub_of_le qh 1 h1, hqq]
      rfl
    rw [hqj]
    refine baseStep_finish (qh - 1) hinv hj hBpos hBlt (by omega) hsz (by rw [hd, hX])
      (by rw [a1, m1]) (fun p hp => by rw [a2 p hp, m2 p hp]) a3 (by rw [hw2, hX])
  · have hb0 : ms.1.toNat = 0 := by
      have : ms.1.toNat ≠ 1 := fun h => hb1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
      omega
    rw [hb0, Nat.zero_mul, Nat.add_zero] at m5
    rw [if_neg (by intro h; exact hb1 (by simpa using h))]
    have hqq : qh.toNat = X / B := by
      have : qh.toNat ≤ X / B := (Nat.le_div_iff_mul_le hBpos).mpr (by omega)
      omega
    have hw1 : segVal ms.2 (ap.toNat + jj.toNat) (n.toNat + 1) = X % B := by
      rw [hqq] at m5; omega
    rw [hqj]
    exact baseStep_finish qh hinv hj hBpos hBlt (by omega) hsz (by rw [hqq, hX]) m1 m2 m3
      (by rw [hw1, hX])

/-! ## Algorithm 1.6 -/

/-- What a division in place leaves: the dividend's segment of `n + m` limbs at `ap` holds the
remainder by the `n` limbs at `bp`, the `m` limbs at `qp` and the returned top word hold the
quotient, and every word outside those two segments and the `S` words of scratch at `sp` keeps its
value. -/
def DivPost (W : Array UInt64) (ap bp qp sp n m S : ℕ) (r : UInt64 × Array UInt64) : Prop :=
  r.2.size = W.size ∧
  (∀ p, ¬ (ap ≤ p ∧ p < ap + n + m) → ¬ (qp ≤ p ∧ p < qp + m) → ¬ (sp ≤ p ∧ p < sp + S) →
    r.2[p]! = W[p]!) ∧
  SegDigits r.2 ap (n + m) ∧ SegDigits r.2 qp m ∧ r.1.toNat ≤ 1 ∧
  segVal r.2 ap (n + m) = segVal W ap (n + m) % segVal W bp n ∧
  segVal r.2 qp m + r.1.toNat * base ^ m = segVal W ap (n + m) / segVal W bp n

/-- Algorithm 1.6 with Knuth's steps: `baseDiv` divides the `n + m` limbs at `ap` by the
normalized `n ≥ 2` limbs at `bp`, for the quotient below the divisor and the divisor below the
dividend. -/
theorem baseDiv_spec (W : Array UInt64) (ap bp qp n m : UInt64) (hW : W.size < 2 ^ 62)
    (hn : 2 ≤ n.toNat) (hqb : qp.toNat + m.toNat ≤ bp.toNat) (hba : bp.toNat + n.toNat ≤ ap.toNat)
    (hsz : ap.toNat + n.toNat + m.toNat ≤ W.size)
    (hda : SegDigits W ap.toNat (n.toNat + m.toNat)) (hdb : SegDigits W bp.toNat n.toNat)
    (hv1 : base ≤ 2 * W[bp.toNat + n.toNat - 1]!.toNat) (sp : ℕ) :
    DivPost W ap.toNat bp.toNat qp.toNat sp n.toNat m.toNat 0 (baseDiv W ap bp qp n m) := by
  obtain ⟨hBge, hBpos⟩ := normalized_ge (by omega) hdb hv1
  generalize hB : segVal W bp.toNat n.toNat = B at hBge hBpos
  have hBlt : B < base ^ n.toNat := by rw [← hB]; exact segVal_lt hdb
  have ham : (ap + m).toNat = ap.toNat + m.toNat := by rw [toNat_add_lt] <;> omega
  have hsplitA : segVal W ap.toNat (n.toNat + m.toNat) =
      segVal W ap.toNat m.toNat + base ^ m.toNat * segVal W (ap.toNat + m.toNat) n.toNat := by
    rw [Nat.add_comm n.toNat, segVal_add]
  have hdtop : SegDigits W (ap.toNat + m.toNat) n.toNat := fun i hi => by
    have := hda (m.toNat + i) (by omega); rwa [← Nat.add_assoc] at this
  -- the top step
  obtain ⟨s1, s2, s3, s4, s5⟩ := subGen_inplace W (ap + m) bp n n (by omega) (by rw [ham]; omega)
    (by simp; omega) (by rw [ham]; exact hdtop) (by simpa using hdb) (by rw [min_self, ham]; omega)
  simp only [min_self] at s5
  rw [ham, hB] at s5
  rw [ham] at s2 s3
  generalize hs : subGen W (ap + m) bp n (ap + m) n = s at s1 s2 s3 s4 s5
  have hsb : ∀ i, i < n.toNat → s.2[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
    s2 _ (by omega)
  have hsl : ∀ i, i < m.toNat → s.2[ap.toNat + i]! = W[ap.toNat + i]! := fun i hi =>
    s2 _ (by omega)
  have hAtop := segVal_lt hdtop
  -- the dividend after the top step, `A - τ β^m B`, below `β^m B`
  obtain ⟨W1, τ, hW1, hτ, hτ1, h1s, h1fr, h1d, h1v, h1lt⟩ : ∃ (W1 : Array UInt64) (τ : UInt64),
      (if s.1 == 1 then (addGen s.2 (ap + m) bp n (ap + m) n).2 else s.2) = W1 ∧
      (1 : UInt64) - s.1 = τ ∧ τ.toNat ≤ 1 ∧ W1.size = W.size ∧
      (∀ p, (p < ap.toNat + m.toNat ∨ ap.toNat + m.toNat + n.toNat ≤ p) → W1[p]! = W[p]!) ∧
      SegDigits W1 ap.toNat (n.toNat + m.toNat) ∧
      segVal W1 ap.toNat (n.toNat + m.toNat) + τ.toNat * (base ^ m.toNat * B) =
        segVal W ap.toNat (n.toNat + m.toNat) ∧
      segVal W1 ap.toNat (n.toNat + m.toNat) < B * base ^ m.toNat := by
    by_cases hb1 : s.1 = 1
    · have hb1' : s.1.toNat = 1 := by rw [hb1]; rfl
      rw [hb1', Nat.one_mul] at s5
      obtain ⟨a1, a2, a3, a4, a5⟩ := addGen_inplace s.2 (ap + m) bp n n (by omega)
        (by rw [ham, s1]; omega) (by rw [s1]; simp; omega) (by rw [ham]; exact s3)
        (by simpa using hdb.congr hsb) (by rw [min_self, ham]; omega)
      simp only [min_self] at a5
      rw [ham, segVal_congr hsb, hB] at a5
      rw [ham] at a2 a3
      have ha3 := segVal_lt a3
      have hc1 : (addGen s.2 (ap + m) bp n (ap + m) n).1.toNat = 1 := by
        rcases (show (addGen s.2 (ap + m) bp n (ap + m) n).1.toNat = 0 ∨
            (addGen s.2 (ap + m) bp n (ap + m) n).1.toNat = 1 by omega) with h | h
        · rw [h, Nat.zero_mul, Nat.add_zero] at a5; omega
        · exact h
      rw [hc1, Nat.one_mul] at a5
      have htop : segVal (addGen s.2 (ap + m) bp n (ap + m) n).2 (ap.toNat + m.toNat) n.toNat =
          segVal W (ap.toNat + m.toNat) n.toNat := by omega
      have hlow : segVal (addGen s.2 (ap + m) bp n (ap + m) n).2 ap.toNat m.toNat =
          segVal W ap.toNat m.toNat := segVal_congr fun i hi => by
        rw [a2 _ (by omega), hsl i hi]
      refine ⟨_, 0, by rw [if_pos (by rw [hb1]; rfl)], by rw [hb1]; rfl, by simp, by rw [a1, s1],
        fun p hp => by rw [a2 p hp, s2 p hp], ?_, ?_, ?_⟩
      · intro i hi
        by_cases hit : i < m.toNat
        · rw [a2 _ (by omega), hsl i hit]; exact hda i hi
        · have := a3 (i - m.toNat) (by omega)
          rwa [show ap.toNat + m.toNat + (i - m.toNat) = ap.toNat + i by omega] at this
      · rw [Nat.add_comm n.toNat, segVal_add, hlow, htop, ← segVal_add, Nat.add_comm m.toNat]
        simp
      · rw [Nat.add_comm n.toNat, segVal_add, hlow, htop]
        have hlo := segVal_lt (hda.mono (k' := m.toNat) (by omega))
        have hs3 := segVal_lt s3
        have : segVal W (ap.toNat + m.toNat) n.toNat < B := by omega
        calc segVal W ap.toNat m.toNat + base ^ m.toNat * segVal W (ap.toNat + m.toNat) n.toNat
            < base ^ m.toNat + base ^ m.toNat * segVal W (ap.toNat + m.toNat) n.toNat := by omega
          _ = base ^ m.toNat * (segVal W (ap.toNat + m.toNat) n.toNat + 1) := by ring
          _ ≤ base ^ m.toNat * B := Nat.mul_le_mul_left _ (by omega)
          _ = B * base ^ m.toNat := by ring
    · have hb0 : s.1.toNat = 0 := by
        have : s.1.toNat ≠ 1 := fun h => hb1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
        omega
      rw [hb0, Nat.zero_mul, Nat.add_zero] at s5
      have hlow : segVal s.2 ap.toNat m.toNat = segVal W ap.toNat m.toNat :=
        segVal_congr fun i hi => hsl i hi
      refine ⟨_, 1, by rw [if_neg (by intro h; exact hb1 (by simpa using h))], by
        rw [show s.1 = 0 from UInt64.toNat_inj.mp (by rw [hb0]; rfl)]; rfl, by simp, s1, s2,
        ?_, ?_, ?_⟩
      · intro i hi
        by_cases hit : i < m.toNat
        · rw [hsl i hit]; exact hda i hi
        · have := s3 (i - m.toNat) (by omega)
          rwa [show ap.toNat + m.toNat + (i - m.toNat) = ap.toNat + i by omega] at this
      · rw [hsplitA, Nat.add_comm n.toNat, segVal_add, hlow]
        simp only [show (1 : UInt64).toNat = 1 from rfl, Nat.one_mul]
        rw [← s5]; ring
      · rw [Nat.add_comm n.toNat, segVal_add, hlow]
        have hlo := segVal_lt (hda.mono (k' := m.toNat) (by omega))
        have : segVal s.2 (ap.toNat + m.toNat) n.toNat < B := by omega
        calc segVal W ap.toNat m.toNat + base ^ m.toNat * segVal s.2 (ap.toNat + m.toNat) n.toNat
            < base ^ m.toNat + base ^ m.toNat * segVal s.2 (ap.toNat + m.toNat) n.toNat := by omega
          _ = base ^ m.toNat * (segVal s.2 (ap.toNat + m.toNat) n.toNat + 1) := by ring
          _ ≤ base ^ m.toNat * B := Nat.mul_le_mul_left _ (by omega)
          _ = B * base ^ m.toNat := by ring
  -- the divisor in `W1`
  have h1b : ∀ i, i < n.toNat → W1[bp.toNat + i]! = W[bp.toNat + i]! := fun i hi =>
    h1fr _ (by omega)
  have hdb1 : SegDigits W1 bp.toNat n.toNat := hdb.congr h1b
  have hB1 : segVal W1 bp.toNat n.toNat = B := by rw [← hB]; exact segVal_congr h1b
  have hv11 : base ≤ 2 * W1[bp.toNat + n.toNat - 1]!.toNat := by
    rw [show bp.toNat + n.toNat - 1 = bp.toNat + (n.toNat - 1) by omega, h1b _ (by omega),
      show bp.toNat + (n.toNat - 1) = bp.toNat + n.toNat - 1 by omega]
    exact hv1
  -- the loop
  generalize hA' : segVal W1 ap.toNat (n.toNat + m.toNat) = A' at h1v h1lt
  have hloop := loop_down (n := m) (init := W1)
    (f := fun e W => let j := m - 1 - e
      let qh := trialAt W (ap + j) bp n
      let ms := mulSubSeg W (ap + j) bp n qh
      if ms.1 == 1 then
        (addGen ms.2 (ap + j) bp n (ap + j) (n + 1)).2.set! (qp + j).toNat (qh - 1)
      else ms.2.set! (qp + j).toNat qh)
    (fun J W => BaseInv W1 ap.toNat qp.toNat n.toNat m.toNat A' B J W) m.toNat rfl
    ⟨rfl, fun _ _ _ => rfl, h1d, fun i hi => by omega, by
      rw [Nat.sub_self, segVal_zero, Nat.div_eq_of_lt h1lt], by
      rw [Nat.mod_eq_of_lt h1lt, hA']⟩ (by
      intro k s' hk hinv
      have hkk : (UInt64.ofNat k).toNat = k := toNat_ofNat_lt (by omega)
      have hjj : (m - 1 - UInt64.ofNat k).toNat = m.toNat - k - 1 := by
        simp only [UInt64.toNat_sub, hkk, UInt64.reduceToNat]; omega
      have := baseStep W1 s' ap bp qp n (m - 1 - UInt64.ofNat k) m.toNat A' (by omega) hn
        (by omega) hqb hba (by omega) hdb1 hv11 (by
          rw [hjj, hB1, show m.toNat - k - 1 + 1 = m.toNat - k by omega]; exact hinv)
      rw [hjj, hB1] at this
      exact this)
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hloop
  simp only [Nat.add_zero, pow_zero, Nat.mul_one, Nat.sub_zero] at l4 l5 l6
  -- the result
  unfold baseDiv
  rw [hs]
  dsimp only
  rw [hW1, hτ]
  have hA : segVal W ap.toNat (n.toNat + m.toNat) = A' + τ.toNat * base ^ m.toNat * B := by
    rw [← h1v]; ring
  refine ⟨l1.trans h1s, fun p hp1 hp2 _ => (l2 p hp1 hp2).trans (h1fr p (by omega)), l3, l4, hτ1,
    l6.trans ?_, ?_⟩
  · rw [hA, hB, Nat.add_mul_mod_self_right]
  · refine (congrArg (· + τ.toNat * base ^ m.toNat) l5).trans ?_
    rw [hA, hB, Nat.add_mul_div_right _ _ hBpos]

end Library.Numerics.Bignum
