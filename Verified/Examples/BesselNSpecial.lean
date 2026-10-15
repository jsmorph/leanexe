import Verified.Examples.BesselYnTheorem

/-!
The exceptional results of `Bessel.jn` and `Bessel.yn`, the arguments outside `jn_accuracy` and
`yn_accuracy`.  A NaN argument gives the canonical NaN for both functions (`jn_nan`, `yn_nan`).  At
`±∞`, `jn` returns a signed zero, negative when `|N|` is odd and the argument after the change of
sign for a negative order is `-∞` (`jn_infinity`); for `|N| ≥ 2` the same holds at `±0`
(`jn_zero_order`).  `yn` returns `-∞` at both zeros (`yn_zero`), the canonical NaN for an argument
with the sign bit set other than `-0`, `-∞` included (`yn_negative`), and `+0` at `+∞` except
`-0` for the order -1 (`yn_pos_infinity`), from fdlibm's `sign * y1(x)`.  These are the values
of the table of exceptional results in `Bessel.md`.

The proofs unfold the code with `dsimp (config := { etaStruct := .none }) only`, as in
`BesselYnTheorem.yn_eq`, so that `dsimp` leaves the pattern matches on the loop states in place.
-/

namespace Verified.Examples.BesselNSpecial
open CodeLib.IEEE64 LeanExe.ProofKit BesselJnTheorem BesselSpecial

set_option exponentiation.threshold 4096

/-- A NaN word passes the NaN guard `u <<< 1 > 0xFFE0000000000000` of `jn` and `yn`. -/
theorem nan_guard (w : UInt64) (h : Wasm.IEEE64.isNaN w = true) :
    w <<< 1 > 0xFFE0000000000000 := by
  have hs := TrigWords.shl_toNat w 1
  have hw := w.toNat_lt
  simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hs]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, pow_one] at hw h ⊢
  omega

/-- **`jn` at a NaN** is the canonical NaN. -/
theorem jn_nan (n : UInt64) (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Bessel.jn n x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.jn Bessel.jnWith
  dsimp (config := { etaStruct := .none }) only
  rw [ite_eq_left (nan_guard x.toBits h), F64Bits.toBits_add, add_nan _ _ h]

/-- **`yn` at a NaN** is the canonical NaN. -/
theorem yn_nan (n : UInt64) (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Bessel.yn n x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.yn Bessel.ynWith
  dsimp (config := { etaStruct := .none }) only
  rw [ite_eq_left (nan_guard x.toBits h), F64Bits.toBits_add, add_nan _ _ h]

/-- **`yn` at `±0`** is `-∞`. -/
theorem yn_zero (n : UInt64) (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Bessel.yn n x).toBits = 0xFFF0000000000000 := by
  unfold Bessel.yn Bessel.ynWith
  dsimp (config := { etaStruct := .none }) only
  rcases h with h | h <;>
  · rw [ite_eq_right (show ¬ x.toBits <<< 1 > 0xFFE0000000000000 by rw [h]; decide),
      ite_eq_left (show (x.toBits <<< 1 == 0) = true by rw [h]; decide)]
    exact neg_one_div_zero

/-- **`yn` at a negative argument** other than `-0`, `-∞` included, is the canonical NaN. -/
theorem yn_negative (n : UInt64) (x : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hz : x.toBits ≠ 0x8000000000000000) (hnan : Wasm.IEEE64.isNaN x.toBits = false) :
    (Bessel.yn n x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.yn Bessel.ynWith
  dsimp (config := { etaStruct := .none }) only
  have hs' : 2 ^ 63 ≤ x.toBits.toNat := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
    exact hs
  rcases negative_cases _ hs hz with h1 | h1 | ⟨h1, h2⟩
  · rw [ite_eq_right (show ¬ x.toBits <<< 1 > 0xFFE0000000000000 by rw [h1]; decide),
      ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by rw [h1]; decide),
      ite_eq_left (show (x.toBits >>> 63 == 1) = true by rw [h1]; decide)]
    exact zero_div_zero
  · rw [hnan] at h1
    exact absurd h1 Bool.false_ne_true
  · rw [ite_eq_right (not_nan_guard _ h1), double_zero, decide_eq_false h2,
      ite_eq_right Bool.false_ne_true, sign_bit, decide_eq_true hs', ite_eq_left rfl]
    exact zero_div_zero

theorem mul_one_zero : Wasm.IEEE64.mul 0x3FF0000000000000 0 = 0 := by decide +kernel

theorem mul_neg_one_zero : Wasm.IEEE64.mul 0xBFF0000000000000 0 = 0x8000000000000000 := by
  decide +kernel

/-- **`yn` at `+∞`** is `+0`, except `-0` for the order -1. -/
theorem yn_pos_infinity (n : UInt64) (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Bessel.yn n x).toBits = if orderZ n = -1 then 0x8000000000000000 else 0 := by
  obtain ⟨hm, hneg⟩ := order_spec n
  unfold Bessel.yn Bessel.ynWith
  dsimp (config := { etaStruct := .none }) only
  rw [ite_eq_right (show ¬ x.toBits <<< 1 > 0xFFE0000000000000 by rw [h]; decide),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by rw [h]; decide),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by rw [h]; decide)]
  generalize Bessel.order n = p at hm hneg ⊢
  obtain ⟨m, neg⟩ := p
  dsimp (config := { etaStruct := .none }) only at hm hneg ⊢
  by_cases h0 : (m == 0) = true
  · rw [ite_eq_left h0]
    have hm0 : m.toNat = 0 := by rw [beq_iff_eq] at h0; rw [h0]; rfl
    rw [ite_eq_right (by omega)]
    exact y0_pos_infinity x h
  rw [ite_eq_right h0]
  by_cases h1 : (m == 1) = true
  · rw [ite_eq_left h1, F64Bits.toBits_mul]
    have hm1 : m = 1 := by rw [beq_iff_eq] at h1; exact h1
    have hy1 : (Bessel.y1With Trig.invPi Trig.halfPi Log.logTable Log.logTable2 Bessel.j1Table
        x).toBits = 0 := y1_pos_infinity x h
    rw [hy1]
    by_cases hn : neg = true
    · have hN : orderZ n = -1 := by
        rw [hn, eq_comm, decide_eq_true_iff] at hneg
        rw [hm1] at hm
        simp only [UInt64.reduceToNat] at hm
        omega
      rw [ite_eq_left (by rw [hn, hm1]; decide), ite_eq_left hN, BesselYnTheorem.neg_one_bits]
      exact mul_neg_one_zero
    · have hN : ¬ orderZ n = -1 := by
        intro hc
        apply hn
        rw [hneg, decide_eq_true_iff, hc]
        norm_num
      rw [ite_eq_right (by simp [hn]), ite_eq_right hN,
        show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
      exact mul_one_zero
  rw [ite_eq_right h1,
    ite_eq_left (show ((x.toBits >>> 32) &&& 0x7fffffff == 0x7ff00000) = true by rw [h]; decide)]
  have hm2 : 2 ≤ m.toNat := by
    have a0 : m.toNat ≠ 0 := fun h' => h0 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h')
    have a1 : m.toNat ≠ 1 := fun h' => h1 (by rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h')
    omega
  rw [ite_eq_right (by omega)]
  rfl

theorem jnAbs_zero (u m : UInt64) (xa : Float)
    (h : (u <<< 1 == 0 || (u >>> 32) &&& 0x7fffffff ≥ 0x7ff00000) = true) :
    jnAbs u m xa = 0.0 :=
  ite_eq_left h

/-- **`jn` at `±0` and `±∞` for `|N| ≥ 2`** is a signed zero, negative when `|N|` is odd and the
argument after the change of sign for a negative order has the sign bit set. -/
theorem jn_zero_order (n : UInt64) (x : Float)
    (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000 ∨ x.toBits = 0x7FF0000000000000 ∨
      x.toBits = 0xFFF0000000000000) (hN : 2 ≤ (orderZ n).natAbs) :
    (Bessel.jn n x).toBits =
      if (orderZ n).natAbs % 2 = 1 ∧ (2 ^ 63 ≤ x.toBits.toNat ↔ 0 ≤ orderZ n) then
        0x8000000000000000 else 0 := by
  obtain ⟨hm, hneg⟩ := order_spec n
  have hnan : ¬ x.toBits <<< 1 > 0xFFE0000000000000 := by
    rcases h with h | h | h | h <;> rw [h] <;> decide
  have hguard : (x.toBits <<< 1 == 0 || (x.toBits >>> 32) &&& 0x7fffffff ≥ 0x7ff00000) = true := by
    rcases h with h | h | h | h <;> rw [h] <;> decide
  rw [jn_eq n x hnan]
  have h0 : ¬ ((Bessel.order n).1 == 0) = true := by
    rw [beq_iff_eq]; intro h'; rw [h'] at hm; simp only [UInt64.reduceToNat] at hm; omega
  have h1 : ¬ ((Bessel.order n).1 == 1) = true := by
    rw [beq_iff_eq]; intro h'; rw [h'] at hm; simp only [UInt64.reduceToNat] at hm; omega
  rw [ite_eq_right h0, ite_eq_right h1, jnAbs_zero _ _ _ hguard]
  have hmodd : ((Bessel.order n).1 &&& 1 == 1) = decide ((orderZ n).natAbs % 2 = 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and,
      hm]
    simp only [UInt64.reduceToNat]
    rw [Nat.and_one_is_mod]
  have hflag : (((if (Bessel.order n).2 = true then (x.toBits >>> 32) ^^^ 0x80000000
      else x.toBits >>> 32) >>> 31 == 1) = true) ↔ (2 ^ 63 ≤ x.toBits.toNat ↔ 0 ≤ orderZ n) := by
    by_cases hn : orderZ n < 0
    · rw [ite_eq_left (by rw [hneg]; exact decide_eq_true hn), xor_sign, decide_eq_true_iff]
      constructor
      · intro h'
        exact iff_of_false (not_le.mpr h') (by omega)
      · intro h'
        by_contra hc
        exact absurd (h'.mp (not_lt.mp hc)) (by omega)
    · rw [ite_eq_right (by rw [hneg]; exact fun h' => hn (of_decide_eq_true h')),
        BesselJ1Large.shr_sign, decide_eq_true_iff]
      constructor
      · intro h'
        exact iff_of_true h' (by omega)
      · intro h'
        exact h'.mpr (by omega)
  by_cases hf : ((Bessel.order n).1 &&& 1 == 1 && (if (Bessel.order n).2 = true then
      (x.toBits >>> 32) ^^^ 0x80000000 else x.toBits >>> 32) >>> 31 == 1) = true
  · rw [ite_eq_left hf]
    rw [Bool.and_eq_true, hmodd, decide_eq_true_iff] at hf
    rw [ite_eq_left ⟨hf.1, hflag.mp hf.2⟩,
      BesselYnTheorem.neg_bits _ (by rw [show (0.0 : Float).toBits = 0 from rfl]; decide),
      show (0.0 : Float).toBits = 0 from rfl]
    decide
  · rw [ite_eq_right hf]
    rw [Bool.and_eq_true, hmodd, decide_eq_true_iff] at hf
    rw [ite_eq_right (fun hc => hf ⟨hc.1, hflag.mpr hc.2⟩)]
    rfl

/-- **`jn` at `±∞`** is a signed zero, negative when `|N|` is odd and the argument after the
change of sign for a negative order is `-∞`. -/
theorem jn_infinity (n : UInt64) (x : Float)
    (h : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    (Bessel.jn n x).toBits =
      if (orderZ n).natAbs % 2 = 1 ∧ (2 ^ 63 ≤ x.toBits.toNat ↔ 0 ≤ orderZ n) then
        0x8000000000000000 else 0 := by
  obtain ⟨hm, hneg⟩ := order_spec n
  by_cases hN : 2 ≤ (orderZ n).natAbs
  · exact jn_zero_order n x (Or.inr (Or.inr h)) hN
  have hnan : ¬ x.toBits <<< 1 > 0xFFE0000000000000 := by
    rcases h with h | h <;> rw [h] <;> decide
  rw [jn_eq n x hnan]
  -- the reflected argument
  have hneg_inf : (-x).toBits = Wasm.IEEE64.negate x.toBits :=
    BesselYnTheorem.neg_bits x (by rcases h with h | h <;> rw [h] <;> decide)
  by_cases h0 : ((Bessel.order n).1 == 0) = true
  · rw [ite_eq_left h0]
    have hN0 : (orderZ n).natAbs = 0 := by
      rw [← hm]; rw [beq_iff_eq] at h0; rw [h0]; rfl
    rw [ite_eq_right (show ¬ ((orderZ n).natAbs % 2 = 1 ∧
      (2 ^ 63 ≤ x.toBits.toNat ↔ 0 ≤ orderZ n)) from fun hc => absurd hc.1 (by rw [hN0]; norm_num))]
    apply j0_infinity
    split
    · rw [hneg_inf]
      rcases h with h | h <;> rw [h] <;> decide
    · exact h
  rw [ite_eq_right h0]
  have hN1 : (orderZ n).natAbs = 1 := by
    have : (Bessel.order n).1.toNat ≠ 0 := fun h' => h0 (by
      rw [beq_iff_eq]; exact UInt64.toNat_inj.mp h')
    rw [hm] at this
    omega
  have h1 : ((Bessel.order n).1 == 1) = true := by
    rw [beq_iff_eq]
    apply UInt64.toNat_inj.mp
    rw [hm, hN1]
    rfl
  rw [ite_eq_left h1]
  by_cases hn : orderZ n < 0
  · have hb : (Bessel.order n).2 = true := by rw [hneg]; exact decide_eq_true hn
    rw [ite_eq_left hb]
    rcases h with h | h
    · have hx' : (-x).toBits = 0xFFF0000000000000 := by rw [hneg_inf, h]; decide
      have hx63 : ¬ 2 ^ 63 ≤ x.toBits.toNat := by rw [h]; decide
      rw [j1_neg_infinity _ hx', ite_eq_left ⟨by omega, iff_of_false hx63 (by omega)⟩]
    · have hx' : (-x).toBits = 0x7FF0000000000000 := by rw [hneg_inf, h]; decide
      have hx63 : 2 ^ 63 ≤ x.toBits.toNat := by rw [h]; decide
      rw [j1_pos_infinity _ hx', ite_eq_right (fun hc => absurd (hc.2.mp hx63) (by omega))]
  · have hb : ¬ (Bessel.order n).2 = true := by
      rw [hneg]; exact fun h' => hn (of_decide_eq_true h')
    rw [ite_eq_right hb]
    rcases h with h | h
    · have hx63 : ¬ 2 ^ 63 ≤ x.toBits.toNat := by rw [h]; decide
      rw [j1_pos_infinity _ h, ite_eq_right (fun hc => hx63 (hc.2.mpr (by omega)))]
    · have hx63 : 2 ^ 63 ≤ x.toBits.toNat := by rw [h]; decide
      rw [j1_neg_infinity _ h, ite_eq_left ⟨by omega, iff_of_true hx63 (by omega)⟩]

#print axioms jn_nan
#print axioms yn_nan
#print axioms yn_zero
#print axioms yn_negative
#print axioms yn_pos_infinity
#print axioms jn_zero_order
#print axioms jn_infinity

end Verified.Examples.BesselNSpecial
