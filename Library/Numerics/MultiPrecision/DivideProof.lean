import Library.Numerics.MultiPrecision.Proof
import Library.Numerics.Arithmetic.Uscale.UscaleDiv

/-! The proof that Algorithm D computes the digits of the quotient and the remainder.  Algorithm D
calls the Uscale module's `mulSmall` and `wordBits`, whose theorems state values with `val`, so
`value_eq_val` relates the two definitions of a number's value.  `quot_le_trial`,
`quot_lt_of_tooBig`, `passes_of_large`, and `trial_le_quot_succ` are Knuth's bounds on the trial
quotient digit: the first trial digit is at least the quotient digit, each decrease of step D3
happens only above it, a digit whose remainder `r̂` reaches the base passes the test, and a digit
that passes the test of step D3 is at most one above the quotient digit.  `trial_spec` applies them
to the program.  `MulsubInv` and `AddbackInv` state the invariants of the loops of steps D4 and D6
on the `t + 1` digits from position `j`, and `DivInv` states the invariant of the main loop: for
the normalized arguments `U` and `V`, the quotient digits so far are `U / (V b^J) * b^J`, and the
partial remainder is `U % (V b^J)`.  `main_step` keeps `DivInv`, `normalize` states the shift of
step D1, `shortDiv_spec` states the short division of step D8 and of a divisor of one digit, and
`longDiv_eq` and `divide_eq` combine them. -/

namespace Library.Numerics.MultiPrecision

open LeanExe.Dialect
open Library.Numerics.Arithmetic.Uscale.UscaleTheorem (val valL Limbs valL_append mulSmall_spec
  wordBits_spec shl_one)

/-! ### Values in the Uscale module's form -/

theorem prefixValue_take (a : Array UInt64) {n : Nat} (hn : n ≤ a.size) :
    prefixValue a n = valL (a.toList.take n) := by
  induction n with
  | zero => simp [prefixValue_zero, valL]
  | succ n ih =>
    have hna : n < a.size := by omega
    have hl : (a.toList.take n).length = n := by simp; omega
    rw [prefixValue_succ, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by simpa using hna), Option.toList_some, valL_append, hl]
    simp only [valL, Nat.mul_zero, Nat.add_zero]
    rw [get_toList a hna, show base ^ n = 2 ^ (32 * n) by unfold base; rw [pow_mul]]
    ring

theorem value_eq_val (a : Array UInt64) : value a = val a := by
  unfold value val
  rw [prefixValue_take a (le_refl _), List.take_of_length_le (by simp)]

theorem digits_of_limbs {a : Array UInt64} (h : Limbs a) : Digits a := fun i hi => by
  rw [get_toList a hi, base_eq]
  exact h _ (List.getElem_mem _)

theorem limbs_of_digits {a : Array UInt64} (h : Digits a) : Limbs a := fun x hx => by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i (by simpa using hi)
  rw [get_toList a (by simpa using hi), base_eq] at this
  exact this



section TrialBounds

variable {b B x2 x1 x0 v1 v0 Xl Vl : Nat}

/-- The trial digit `⌊(x2 b + x1) / v1⌋` is at least the quotient digit. -/
theorem quot_le_trial (hb : 0 < b) (hB : 0 < B) (hx0 : x0 < b) (hXl : Xl < B) (hv1 : 0 < v1) :
    (((x2 * b + x1) * b + x0) * B + Xl) / ((v1 * b + v0) * B + Vl) ≤ (x2 * b + x1) / v1 := by
  have h1 : x2 * b + x1 < v1 * ((x2 * b + x1) / v1 + 1) := Nat.lt_mul_div_succ _ hv1
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc ((x2 * b + x1) * b + x0) * B + Xl < ((x2 * b + x1) * b + x0 + 1) * B := by nlinarith
    _ ≤ (x2 * b + x1 + 1) * b * B := Nat.mul_le_mul_right _ (by rw [Nat.succ_mul]; omega)
    _ ≤ v1 * ((x2 * b + x1) / v1 + 1) * b * B :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ ≤ ((x2 * b + x1) / v1 + 1) * ((v1 * b + v0) * B + Vl) := by
        have e : ((x2 * b + x1) / v1 + 1) * ((v1 * b + v0) * B + Vl) =
            v1 * ((x2 * b + x1) / v1 + 1) * b * B +
              (((x2 * b + x1) / v1 + 1) * v0 * B + ((x2 * b + x1) / v1 + 1) * Vl) := by ring
        rw [e]; exact Nat.le_add_right _ _

/-- A digit `qh` with `qh v1 + rh = x2 b + x1` that fails the test of step D3 is too large. -/
theorem quot_lt_of_tooBig {qh rh : Nat} (hXl : Xl < B)
    (hX : ((x2 * b + x1) * b + x0) * B + Xl < b * ((v1 * b + v0) * B + Vl))
    (hqr : qh * v1 + rh = x2 * b + x1) (h : b ≤ qh ∨ b * rh + x0 < qh * v0) :
    (((x2 * b + x1) * b + x0) * B + Xl) / ((v1 * b + v0) * B + Vl) < qh := by
  have hV : 0 < (v1 * b + v0) * B + Vl := by
    rcases Nat.eq_zero_or_pos ((v1 * b + v0) * B + Vl) with h0 | h0
    · rw [h0, Nat.mul_zero] at hX; omega
    · exact h0
  rw [Nat.div_lt_iff_lt_mul hV]
  rcases h with h | h
  · calc ((x2 * b + x1) * b + x0) * B + Xl < b * ((v1 * b + v0) * B + Vl) := hX
      _ ≤ qh * ((v1 * b + v0) * B + Vl) := Nat.mul_le_mul_right _ h
  · have h3 : (x2 * b + x1) * b + x0 + 1 ≤ qh * (v1 * b + v0) := by nlinarith
    calc ((x2 * b + x1) * b + x0) * B + Xl < ((x2 * b + x1) * b + x0 + 1) * B := by nlinarith
      _ ≤ qh * (v1 * b + v0) * B := Nat.mul_le_mul_right _ h3
      _ ≤ qh * ((v1 * b + v0) * B + Vl) := by nlinarith

/-- A digit `qh < b` that passes the test of step D3 is at most one more than the quotient digit. -/
theorem trial_le_quot_succ {qh rh : Nat} (hb : 0 < b) (hB : 0 < B) (hVl : Vl < B) (hv1 : 0 < v1)
    (hqr : qh * v1 + rh = x2 * b + x1) (hq : qh < b) (h : qh * v0 ≤ b * rh + x0) :
    qh ≤ (((x2 * b + x1) * b + x0) * B + Xl) / ((v1 * b + v0) * B + Vl) + 1 := by
  have hV : 0 < (v1 * b + v0) * B + Vl := by positivity
  generalize hq0 : (((x2 * b + x1) * b + x0) * B + Xl) / ((v1 * b + v0) * B + Vl) = q
  by_contra hc
  push Not at hc
  have hq2 : (q + 2) * ((v1 * b + v0) * B + Vl) ≤ qh * ((v1 * b + v0) * B + Vl) :=
    Nat.mul_le_mul_right _ hc
  have hlt := Nat.lt_mul_div_succ (((x2 * b + x1) * b + x0) * B + Xl) hV
  rw [hq0] at hlt
  have h3 : qh * (v1 * b + v0) ≤ (x2 * b + x1) * b + x0 := by nlinarith
  have h4a : qh * Vl < qh * B := Nat.mul_lt_mul_of_pos_left hVl (by omega)
  have h4b : qh * ((v1 * b + v0) * B) ≤ ((x2 * b + x1) * b + x0) * B := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h3
  have e1 : qh * ((v1 * b + v0) * B + Vl) = qh * ((v1 * b + v0) * B) + qh * Vl := by ring
  have e2 : (q + 2) * ((v1 * b + v0) * B + Vl) =
      ((v1 * b + v0) * B + Vl) * (q + 1) + ((v1 * b + v0) * B + Vl) := by ring
  have h6 : b * B ≤ (v1 * b + v0) * B + Vl := by
    have : b * B ≤ v1 * b * B := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hv1)
    have e3 : (v1 * b + v0) * B + Vl = v1 * b * B + (v0 * B + Vl) := by ring
    omega
  have h7 : qh * B < b * B := Nat.mul_lt_mul_of_pos_right hq hB
  omega

/-- A digit with a remainder `rh ≥ b` passes the test of step D3, when the partial remainder is
below `b` times the divisor. -/
theorem passes_of_large {qh rh : Nat} (hb : 0 < b) (hv0 : v0 < b)
    (hX : ((x2 * b + x1) * b + x0) * B + Xl < b * ((v1 * b + v0) * B + Vl)) (hVl : Vl < B)
    (hqr : qh * v1 + rh = x2 * b + x1) (hr : b ≤ rh) :
    qh < b ∧ qh * v0 ≤ b * rh + x0 := by
  have h1 : ((x2 * b + x1) * b + x0) * B < b * (v1 * b + v0 + 1) * B := by nlinarith
  have h2 : (x2 * b + x1) * b + x0 < b * (v1 * b + v0 + 1) := Nat.lt_of_mul_lt_mul_right h1
  have h3 : x2 * b + x1 < v1 * b + b := by nlinarith
  have hq : qh < b := by nlinarith
  exact ⟨hq, by nlinarith⟩

/-- The top two digits of a partial remainder below `b` times the divisor are at most the top digit
of the divisor followed by the largest digit. -/
theorem top_lt (hb : 0 < b) (hv0 : v0 < b) (hVl : Vl < B)
    (hX : ((x2 * b + x1) * b + x0) * B + Xl < b * ((v1 * b + v0) * B + Vl)) :
    x2 * b + x1 < v1 * b + b := by
  have h1 : ((x2 * b + x1) * b + x0) * B < b * (v1 * b + v0 + 1) * B := by nlinarith
  have h2 : (x2 * b + x1) * b + x0 < b * (v1 * b + v0 + 1) := Nat.lt_of_mul_lt_mul_right h1
  nlinarith

end TrialBounds


/-! ### Significant digits -/

theorem prefixValue_zero_tail {v : Array UInt64} {t n : Nat} (htn : t ≤ n)
    (h : ∀ i, t ≤ i → i < n → v[i]! = 0) : prefixValue v n = prefixValue v t := by
  induction n, htn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [prefixValue_succ, ih fun i h1 h2 => h i h1 (by omega), h n hn (by omega),
      show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem significant_spec (v : Array UInt64) (hs : v.size < 2 ^ 64) :
    (significant v).toNat ≤ v.size ∧ (∀ i, (significant v).toNat ≤ i → v[i]! = 0) ∧
      (0 < (significant v).toNat → v[(significant v).toNat - 1]! ≠ 0) := by
  have hn := size_toNat hs
  have h := loop_induction (n := v.size.toUInt64) (init := (0 : UInt64))
    (f := fun i t => if v[i.toNat]! = 0 then t else i + 1)
    (P := fun k t => t.toNat ≤ k ∧ (∀ i, t.toNat ≤ i → i < k → v[i]! = 0) ∧
      (0 < t.toNat → v[t.toNat - 1]! ≠ 0))
    ⟨by simp, fun i _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by simp)⟩
    (by
      intro k t hk ⟨h1, h2, h3⟩
      rw [hn] at hk
      have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      have hk1 : (UInt64.ofNat k + 1).toNat = k + 1 := by
        simp only [UInt64.toNat_add, hkk, UInt64.reduceToNat]; omega
      rw [hkk]
      split
      · rename_i h0
        refine ⟨by omega, fun i hi hik => ?_, h3⟩
        rcases Nat.lt_or_ge i k with h | h
        · exact h2 i hi h
        · rw [show i = k by omega]; exact h0
      · rename_i h0
        rw [hk1]
        exact ⟨le_refl _, fun i hi hik => absurd hik (by omega), fun _ => h0⟩)
  rw [hn] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun i hi => ?_, h3⟩
  rcases Nat.lt_or_ge i v.size with h | h
  · exact h2 i hi h
  · exact getElem!_neg v i (by omega)

/-! ### Short division -/

theorem prefixValue_set {q : Array UInt64} {p L : Nat} {y : UInt64} (hp : p < L) (hq : p < q.size)
    (h0 : q[p]! = 0) : prefixValue (q.set! p y) L = prefixValue q L + y.toNat * base ^ p := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [prefixValue_succ, prefixValue_succ, get_set q p y L hq]
    rcases Nat.lt_or_ge p L with h | h
    · rw [ih h, ite_eq_right (show ¬ L = p by omega)]; ring
    · have hpL : p = L := by omega
      subst hpL
      have hc : prefixValue (q.set! p y) p = prefixValue q p :=
        prefixValue_congr fun i hi => by rw [get_set q p y i hq, ite_eq_right (show ¬ i = p by omega)]
      rw [ite_eq_left rfl, h0, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, hc]

theorem div_step {H b x d : Nat} (hd : 0 < d) :
    (H * b + x) / d = H / d * b + (H % d * b + x) / d ∧ (H * b + x) % d = (H % d * b + x) % d := by
  have e : H * b + x = (H % d * b + x) + d * (H / d * b) := by
    have h := Nat.div_add_mod H d
    calc H * b + x = (d * (H / d) + H % d) * b + x := by rw [h]
      _ = (H % d * b + x) + d * (H / d * b) := by ring
  rw [e, Nat.add_mul_div_left _ _ hd, Nat.add_mul_mod_self_left]
  exact ⟨by ring, rfl⟩

/-- Short division from the most significant digit: the first `len` digits of the result are the
quotient of the first `len` digits of `x` by `d`, and the last is the remainder. -/
theorem shortDiv_spec (x : Array UInt64) (d len : UInt64) (hx : ∀ p : Nat, x[p]!.toNat < base)
    (hd : 0 < d.toNat) (hdb : d.toNat < base) (hlen : len.toNat < 2 ^ 63) :
    (shortDiv x d len).size = len.toNat + 1 ∧
      (∀ p : Nat, p < len.toNat → (shortDiv x d len)[p]!.toNat < base) ∧
      prefixValue (shortDiv x d len) len.toNat = prefixValue x len.toNat / d.toNat ∧
      (shortDiv x d len)[len.toNat]!.toNat = prefixValue x len.toNat % d.toNat := by
  have hb := base_eq
  have hdig : ∀ p, p < len.toNat →
      prefixValue x len.toNat / base ^ p % base = x[p]!.toNat :=
    fun p hp => prefixValue_digit (fun q _ => hx q) hp
  have hH : ∀ e, e < len.toNat → prefixValue x len.toNat / base ^ (len.toNat - e - 1) =
      prefixValue x len.toNat / base ^ (len.toNat - e) * base + x[len.toNat - e - 1]!.toNat := by
    intro e he
    have h := Nat.div_add_mod (prefixValue x len.toNat / base ^ (len.toNat - e - 1)) base
    rw [Nat.div_div_eq_div_mul, ← pow_succ, show len.toNat - e - 1 + 1 = len.toNat - e by omega,
      hdig _ (by omega)] at h
    linarith
  have h := loop_induction (n := len)
    (init := ((0 : UInt64), LeanExe.build len fun _ => (0 : UInt64)))
    (f := fun e s => ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) % d,
      s.2.set! (len - 1 - e).toNat ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) / d)))
    (P := fun e s => s.2.size = len.toNat ∧ s.1.toNat < d.toNat ∧
      (∀ p : Nat, s.2[p]!.toNat < base) ∧ (∀ p, p < len.toNat - e → s.2[p]! = 0) ∧
      prefixValue s.2 len.toNat = prefixValue x len.toNat / base ^ (len.toNat - e) / d.toNat *
        base ^ (len.toNat - e) ∧
      s.1.toNat = prefixValue x len.toNat / base ^ (len.toNat - e) % d.toNat)
    (by
      have hz : ∀ p : Nat, (LeanExe.build len fun _ => (0 : UInt64))[p]! = 0 := by
        intro p
        by_cases hp : p < len.toNat
        · rw [build_get hp]
        · rw [build_get_out hp]; rfl
      have hX : prefixValue x len.toNat / base ^ (len.toNat - 0) = 0 :=
        Nat.div_eq_of_lt (prefixValue_lt fun q _ => hx q)
      refine ⟨build_size _ _, hd, fun p => by rw [hz]; exact base_pos, fun p _ => hz p, ?_, ?_⟩
      · rw [prefixValue_zeros hz, hX]; simp
      · rw [hX]; rfl)
    (by
      intro e s he ⟨hs, hr, hd', hz, hval, hrem⟩
      obtain ⟨p, hpe⟩ : ∃ p, len.toNat - e = p + 1 := ⟨len.toNat - e - 1, by omega⟩
      have hp1 : len.toNat - e - 1 = p := by omega
      have hp2 : len.toNat - (e + 1) = p := by omega
      rw [hpe] at hval hrem hz
      have hH' := hH e he
      rw [hp1, hpe] at hH'
      have hee : (UInt64.ofNat e).toNat = e := UInt64.toNat_ofNat_of_lt' (show e < 2 ^ 64 by omega)
      have hp : (len - 1 - UInt64.ofNat e).toNat = p := by
        simp only [UInt64.toNat_sub, hee, UInt64.reduceToNat]; omega
      have hX := hx p
      rw [hb] at hX hdb
      have ht : (s.1 * 4294967296 + x[p]!).toNat = s.1.toNat * 4294967296 + x[p]!.toNat := by
        have : s.1.toNat * 4294967296 ≤ 4294967295 * 4294967296 := Nat.mul_le_mul_right _ (by omega)
        simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
      simp only [hp, hp2]
      have hget := fun (q : Nat) => get_set s.2 p ((s.1 * 4294967296 + x[p]!) / d) q (by omega)
      obtain ⟨hdiv, hmod⟩ := div_step (H := prefixValue x len.toNat / base ^ (p + 1))
        (b := base) (x := x[p]!.toNat) hd
      have hq : (s.1.toNat * 4294967296 + x[p]!.toNat) / d.toNat < base := by
        rw [Nat.div_lt_iff_lt_mul hd, hb]; nlinarith
      refine ⟨by simp [hs], ?_, fun q => ?_, fun q hq' => ?_, ?_, ?_⟩
      · rw [UInt64.toNat_mod, ht]; exact Nat.mod_lt _ hd
      · rw [hget]; split
        · rw [UInt64.toNat_div, ht]; exact hq
        · exact hd' q
      · rw [hget, ite_eq_right (show ¬ q = p by omega)]; exact hz q (by omega)
      · rw [prefixValue_set (by omega) (by omega) (hz p (by omega)), hval, UInt64.toNat_div, ht, hH',
          hdiv, ← hrem, hb, pow_succ]
        ring
      · rw [UInt64.toNat_mod, ht, hH', hmod, ← hrem, hb])
  obtain ⟨hs, -, hd', -, hval, hrem⟩ := h
  rw [Nat.sub_self, pow_zero, Nat.div_one, Nat.mul_one] at hval
  rw [Nat.sub_self, pow_zero, Nat.div_one] at hrem
  unfold shortDiv
  dsimp only
  have hlast : ∀ (r : UInt64) (q : Array UInt64), q.size = len.toNat →
      (q.push r)[len.toNat]! = r := fun r q hq => by rw [← hq]; exact push_get_size _ _
  refine ⟨by rw [Array.size_push, hs], fun p hp => ?_, ?_, by rw [hlast _ _ hs]; exact hrem⟩
  · rw [push_get_lt _ _ (by omega)]; exact hd' p
  · have hc : prefixValue ((LeanExe.loop len ((0 : UInt64), LeanExe.build len fun _ => (0 : UInt64))
        fun e s => ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) % d,
          s.2.set! (len - 1 - e).toNat ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) / d))).2.push
        (LeanExe.loop len ((0 : UInt64), LeanExe.build len fun _ => (0 : UInt64))
        fun e s => ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) % d,
          s.2.set! (len - 1 - e).toNat ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) / d))).1)
        len.toNat = prefixValue (LeanExe.loop len ((0 : UInt64), LeanExe.build len fun _ => (0 : UInt64))
        fun e s => ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) % d,
          s.2.set! (len - 1 - e).toNat ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) / d))).2 len.toNat :=
      prefixValue_congr fun p hp => push_get_lt _ _ (by omega)
    rw [hc, hval]

/-! ### Runs of digits -/

/-- The number of the `n` digits of `w` from position `j`. -/
def segValue (w : Array UInt64) (j n : Nat) : Nat :=
  ((List.range n).map fun i => w[j + i]!.toNat * base ^ i).sum

theorem segValue_succ (w : Array UInt64) (j n : Nat) :
    segValue w j (n + 1) = segValue w j n + w[j + n]!.toNat * base ^ n := by
  simp [segValue, List.range_succ]

theorem segValue_lt {w : Array UInt64} {j n : Nat} (h : ∀ p : Nat, w[p]!.toNat < base) :
    segValue w j n < base ^ n := by
  induction n with
  | zero => simp [segValue]
  | succ n ih =>
    rw [segValue_succ, pow_succ]
    have h2 := h (j + n)
    have h3 : w[j + n]!.toNat * base ^ n + base ^ n ≤ base ^ n * base := by
      calc w[j + n]!.toNat * base ^ n + base ^ n = (w[j + n]!.toNat + 1) * base ^ n := by ring
        _ ≤ base * base ^ n := Nat.mul_le_mul_right _ h2
        _ = base ^ n * base := by ring
    omega

/-- The first `j + n` digits split at `j`. -/
theorem prefixValue_split (w : Array UInt64) (j n : Nat) :
    prefixValue w (j + n) = prefixValue w j + base ^ j * segValue w j n := by
  induction n with
  | zero => simp [segValue]
  | succ n ih =>
    rw [← Nat.add_assoc, prefixValue_succ, ih, segValue_succ, pow_add]
    ring

/-! ### Step D3 -/

theorem tooBig_iff {q r x v : UInt64} (hq : q.toNat ≤ base + 1) (hr : r.toNat < base)
    (hx : x.toNat < base) (hv : v.toNat < base) :
    tooBig q r x v = true ↔ (base ≤ q.toNat ∨ base * r.toNat + x.toNat < q.toNat * v.toNat) := by
  rw [base_eq] at *
  have h1 : (4294967296 * r + x).toNat = 4294967296 * r.toNat + x.toNat := by
    have : 4294967296 * r.toNat ≤ 4294967296 * 4294967295 := Nat.mul_le_mul_left _ (by omega)
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have h2 : (q * v).toNat = q.toNat * v.toNat := by
    have : q.toNat * v.toNat ≤ 4294967297 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    simp only [UInt64.toNat_mul]; omega
  unfold tooBig
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, h1, h2, UInt64.reduceToNat]
  split <;> simp_all

/-- Step D3 of the program: when the `t + 1` digits of `w` from position `j` hold a number `X` below
`b` times the normalized divisor `V`, `trial` returns the quotient digit `X / V` or one more, and a
digit. -/
theorem trial_spec (w v : Array UInt64) (j t : UInt64) (hw : ∀ p : Nat, w[p]!.toNat < base)
    (hv : ∀ p : Nat, v[p]!.toNat < base) (ht : 2 ≤ t.toNat) (hjt : j.toNat + t.toNat < 2 ^ 63)
    (hv1 : base ≤ 2 * v[t.toNat - 1]!.toNat)
    (hX : segValue w j.toNat (t.toNat + 1) < base * prefixValue v t.toNat) :
    segValue w j.toNat (t.toNat + 1) / prefixValue v t.toNat ≤ (trial w v j t).toNat ∧
      (trial w v j t).toNat ≤ segValue w j.toNat (t.toNat + 1) / prefixValue v t.toNat + 1 ∧
      (trial w v j t).toNat < base := by
  obtain ⟨T, hT⟩ : ∃ T, t.toNat = T + 2 := ⟨t.toNat - 2, by omega⟩
  have hb := base_eq
  have hb0 := base_pos
  have i1 : (j + t).toNat = j.toNat + (T + 2) := by
    simp only [UInt64.toNat_add]; omega
  have i2 : (j + t - 1).toNat = j.toNat + (T + 1) := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  have i3 : (j + t - 2).toNat = j.toNat + T := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]; omega
  have i4 : (t - 1).toNat = T + 1 := by
    simp only [UInt64.toNat_sub, UInt64.reduceToNat]; omega
  have i5 : (t - 2).toNat = T := by
    simp only [UInt64.toNat_sub, UInt64.reduceToNat]; omega
  rw [hT] at hX hv1 ⊢
  rw [show T + 2 - 1 = T + 1 by omega] at hv1
  have hXs : segValue w j.toNat (T + 2 + 1) =
      ((w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat) * base +
        w[j.toNat + T]!.toNat) * base ^ T + segValue w j.toNat T := by
    rw [segValue_succ, segValue_succ, segValue_succ, pow_succ, pow_succ]; ring
  have hVs : prefixValue v (T + 2) =
      (v[T + 1]!.toNat * base + v[T]!.toNat) * base ^ T + prefixValue v T := by
    rw [prefixValue_succ, prefixValue_succ, pow_succ]; ring
  rw [hXs, hVs] at hX ⊢
  have hXl := segValue_lt (j := j.toNat) (n := T) hw
  have hVl := prefixValue_lt (u := v) (q := T) fun p _ => hv p
  have hB : 0 < base ^ T := pow_pos hb0 T
  have hx2 := hw (j.toNat + (T + 2))
  have hx1 := hw (j.toNat + (T + 1))
  have hx0 := hw (j.toNat + T)
  have hv0 := hv T
  have hv1' := hv (T + 1)
  have htop := top_lt hb0 hv0 hVl hX
  have hn2 : (w[j.toNat + (T + 2)]! * 4294967296 + w[j.toNat + (T + 1)]!).toNat =
      w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat := by
    rw [hb] at hx2 hx1 ⊢
    have : w[j.toNat + (T + 2)]!.toNat * 4294967296 ≤ 4294967295 * 4294967296 :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  unfold trial
  dsimp only
  rw [i1, i2, i3, i4, i5]
  generalize hQ : (w[j.toNat + (T + 2)]! * 4294967296 + w[j.toNat + (T + 1)]!) / v[T + 1]! = Q0
  generalize hR : (w[j.toNat + (T + 2)]! * 4294967296 + w[j.toNat + (T + 1)]!) % v[T + 1]! = R0
  have hQ0 : Q0.toNat = (w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat) /
      v[T + 1]!.toNat := by rw [← hQ, UInt64.toNat_div, hn2]
  have hR0 : R0.toNat = (w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat) %
      v[T + 1]!.toNat := by rw [← hR, UInt64.toNat_mod, hn2]
  have hv1p : 0 < v[T + 1]!.toNat := by omega
  have hqr0 : Q0.toNat * v[T + 1]!.toNat + R0.toNat =
      w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat := by
    rw [hQ0, hR0, Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hQb : Q0.toNat ≤ base + 1 := by
    rw [hQ0]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hv1p]
    nlinarith
  have hRb : R0.toNat < v[T + 1]!.toNat := by rw [hR0]; exact Nat.mod_lt _ hv1p
  have hge := quot_le_trial (x2 := w[j.toNat + (T + 2)]!.toNat) (x1 := w[j.toNat + (T + 1)]!.toNat)
    (x0 := w[j.toNat + T]!.toNat) (v0 := v[T]!.toNat) (Vl := prefixValue v T) hb0 hB hx0 hXl hv1p
  rw [← hQ0] at hge
  have hRb' : R0.toNat < base := by omega
  have hR1 : (R0 + v[T + 1]!).toNat = R0.toNat + v[T + 1]!.toNat := by
    rw [hb] at hRb' hv1'; simp only [UInt64.toNat_add]; omega
  generalize hc : tooBig Q0 R0 w[j.toNat + T]! v[T]! = c0
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
    have hqr1 : (Q0 - 1).toNat * v[T + 1]!.toNat + (R0 + v[T + 1]!).toNat =
        w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat := by
      rw [hQ1, hR1, ← hqr0]
      obtain ⟨k, hk⟩ : ∃ k, Q0.toNat = k + 1 := ⟨Q0.toNat - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]; ring
    have hcond : (R0 + v[T + 1]! < 4294967296) ↔ (R0 + v[T + 1]!).toNat < base := by
      rw [UInt64.lt_iff_toNat_lt, hb]; rfl
    by_cases h2 : (R0 + v[T + 1]!).toNat < base ∧ tooBig (Q0 - 1) (R0 + v[T + 1]!) w[j.toNat + T]! v[T]! = true
    · rw [ite_eq_left ⟨hcond.mpr h2.1, h2.2⟩]
      have hlt1 := quot_lt_of_tooBig hXl hX hqr1
        ((tooBig_iff (by omega) h2.1 hx0 hv0).mp h2.2)
      have hQ1pos : 0 < (Q0 - 1).toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt1
      have hQ2 : (Q0 - 1 - 1).toNat = Q0.toNat - 1 - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          simp only [UInt64.reduceToNat]; omega)), hQ1]
        simp only [UInt64.reduceToNat]
      have hqr2 : (Q0.toNat - 1 - 1) * v[T + 1]!.toNat + ((R0 + v[T + 1]!).toNat + v[T + 1]!.toNat) =
          w[j.toNat + (T + 2)]!.toNat * base + w[j.toNat + (T + 1)]!.toNat := by
        rw [← hqr1, hQ1]
        obtain ⟨k, hk⟩ : ∃ k, Q0.toNat - 1 = k + 1 := ⟨Q0.toNat - 1 - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]; ring
      obtain ⟨hlt2, hpass⟩ := passes_of_large hb0 hv0 hX hVl hqr2 (by omega)
      rw [hQ2]
      exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr2 hlt2 hpass, hlt2⟩
    · rw [ite_eq_right fun h => h2 ⟨hcond.mp h.1, h.2⟩]
      rcases Nat.lt_or_ge (R0 + v[T + 1]!).toNat base with hr | hr
      · have hn : ¬ (base ≤ (Q0 - 1).toNat ∨ base * (R0 + v[T + 1]!).toNat + w[j.toNat + T]!.toNat <
            (Q0 - 1).toNat * v[T]!.toNat) := fun h => h2 ⟨hr, (tooBig_iff (by omega) hr hx0 hv0).mpr h⟩
        push Not at hn
        exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr1 hn.1 hn.2, hn.1⟩
      · obtain ⟨hlt1, hpass⟩ := passes_of_large hb0 hv0 hX hVl hqr1 hr
        exact ⟨by omega, trial_le_quot_succ hb0 hB hVl hv1p hqr1 hlt1 hpass, hlt1⟩

theorem segValue_congr {w w' : Array UInt64} {j n : Nat} (h : ∀ i, i < n → w[j + i]! = w'[j + i]!) :
    segValue w j n = segValue w' j n := by
  unfold segValue
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-! ### Steps D4 and D6 -/

/-- The invariant of step D4 after `k` digits: the carry `x.1` of the product, the borrow `x.2.1`,
and the array `x.2.2`, whose digits from position `j` hold the difference so far. -/
def MulsubInv (w vn : Array UInt64) (qh j : UInt64) (k : Nat)
    (x : UInt64 × UInt64 × Array UInt64) : Prop :=
  x.2.2.size = w.size ∧ (∀ p : Nat, x.2.2[p]!.toNat < base) ∧ x.2.1.toNat ≤ 1 ∧
    x.1.toNat < base ∧ x.1.toNat * base ^ k ≤ qh.toNat * prefixValue vn k ∧
    (∀ p, p < j.toNat ∨ j.toNat + k ≤ p → x.2.2[p]! = w[p]!) ∧
    segValue x.2.2 j.toNat k + qh.toNat * prefixValue vn k =
      segValue w j.toNat k + (x.2.1.toNat + x.1.toNat) * base ^ k

/-- Step D4: the loop subtracts `qh` times the first `t + 1` digits of `vn` from the `t + 1` digits
of `w` from position `j`.  Its state holds the carry of the product, the borrow, and the array. -/
theorem mulsub_spec (w vn : Array UInt64) (qh j t : UInt64) (hw : ∀ p : Nat, w[p]!.toNat < base)
    (hvn : ∀ p : Nat, vn[p]!.toNat < base) (hq : qh.toNat < base)
    (hjt : j.toNat + t.toNat + 1 ≤ w.size) (hsz : w.size < 2 ^ 63) :
    MulsubInv w vn qh j (t.toNat + 1)
      (LeanExe.loop (t + 1) ((0 : UInt64), (0 : UInt64), w) fun i x =>
        ((qh * vn[i.toNat]! + x.1) / 4294967296,
          1 - (x.2.2[(i + j).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
            - x.2.1) / 4294967296,
          x.2.2.set! (i + j).toNat
            ((x.2.2[(i + j).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
              - x.2.1) % 4294967296))) := by
  have ht1 : (t + 1).toNat = t.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [← ht1]
  refine loop_induction (P := MulsubInv w vn qh j) ?_ ?_
  · refine ⟨rfl, hw, by simp, base_pos, by simp [prefixValue_zero], fun _ _ => rfl, ?_⟩
    simp [segValue, prefixValue_zero]
  · intro k x hk ⟨hs, hd, hbr, hc, hcb, hun, hval⟩
    rw [ht1] at hk
    have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
    have hidx : (UInt64.ofNat k + j).toNat = j.toNat + k := by
      simp only [UInt64.toNat_add, hkk]; omega
    have hb := base_eq
    have ha := hvn k
    have hww := hd (j.toNat + k)
    have hwk : x.2.2[j.toNat + k]! = w[j.toNat + k]! := hun _ (Or.inr (by omega))
    rw [hb] at ha hww hc hq
    have hprod : qh.toNat * vn[k]!.toNat ≤ 4294967295 * 4294967295 :=
      Nat.mul_le_mul (by omega) (by omega)
    have hp : (qh * vn[k]! + x.1).toNat = qh.toNat * vn[k]!.toNat + x.1.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul]; omega
    have hpd : ((qh * vn[k]! + x.1) % 4294967296).toNat =
        (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 := by
      rw [UInt64.toNat_mod, hp]; rfl
    have ht' : (x.2.2[j.toNat + k]! + 4294967296 - (qh * vn[k]! + x.1) % 4294967296 - x.2.1).toNat =
        x.2.2[j.toNat + k]!.toNat + 4294967296 -
          (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 - x.2.1.toNat := by
      have := Nat.mod_lt (qh.toNat * vn[k]!.toNat + x.1.toNat) (show 0 < 4294967296 by norm_num)
      simp only [UInt64.toNat_sub, UInt64.toNat_add, hpd, UInt64.reduceToNat]; omega
    simp only [hkk, hidx]
    have hget := fun (p : Nat) => get_set x.2.2 (j.toNat + k)
      ((x.2.2[j.toNat + k]! + 4294967296 - (qh * vn[k]! + x.1) % 4294967296 - x.2.1) % 4294967296)
      p (by omega)
    refine ⟨by simp [hs], fun p => ?_, ?_, ?_, ?_, fun p hp' => ?_, ?_⟩
    · rw [hget]; split
      · rw [UInt64.toNat_mod, ht', hb]; simp only [UInt64.reduceToNat]; omega
      · exact hd p
    · simp only [UInt64.toNat_sub, UInt64.toNat_div, ht', UInt64.reduceToNat]; omega
    · rw [UInt64.toNat_div, hp, hb]; simp only [UInt64.reduceToNat]; omega
    · rw [UInt64.toNat_div, hp, prefixValue_succ, pow_succ]
      have h1 : (qh.toNat * vn[k]!.toNat + x.1.toNat) / (4294967296 : UInt64).toNat * base ≤
          qh.toNat * vn[k]!.toNat + x.1.toNat := by
        rw [hb]; exact Nat.div_mul_le_self _ _
      nlinarith [h1, hcb, pow_pos base_pos k]
    · rw [hget, ite_eq_right (show ¬ p = j.toNat + k by omega)]
      exact hun p (by omega)
    · have hc' : segValue (x.2.2.set! (j.toNat + k)
          ((x.2.2[j.toNat + k]! + 4294967296 - (qh * vn[k]! + x.1) % 4294967296 - x.2.1) %
            4294967296)) j.toNat k = segValue x.2.2 j.toNat k :=
        segValue_congr fun i hi => by rw [hget, ite_eq_right (show ¬ j.toNat + i = j.toNat + k by omega)]
      have hb' : (1 - (x.2.2[j.toNat + k]! + 4294967296 - (qh * vn[k]! + x.1) % 4294967296 -
          x.2.1) / 4294967296).toNat = 1 - (x.2.2[j.toNat + k]!.toNat + 4294967296 -
          (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 - x.2.1.toNat) / 4294967296 := by
        simp only [UInt64.toNat_sub, UInt64.toNat_div, ht', UInt64.reduceToNat]; omega
      dsimp only
      rw [segValue_succ, segValue_succ, hc', hget, ite_eq_left rfl, prefixValue_succ,
        UInt64.toNat_mod, ht', UInt64.toNat_div, hp, hb']
      simp only [UInt64.reduceToNat]
      rw [hwk]
      rw [hwk] at hww
      have hd1 := Nat.mod_add_div (qh.toNat * vn[k]!.toNat + x.1.toNat) 4294967296
      have hd2 : (w[j.toNat + k]!.toNat + 4294967296 -
            (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 - x.2.1.toNat) % 4294967296 +
          (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 + x.2.1.toNat =
          w[j.toNat + k]!.toNat + (1 - (w[j.toNat + k]!.toNat + 4294967296 -
            (qh.toNat * vn[k]!.toNat + x.1.toNat) % 4294967296 - x.2.1.toNat) / 4294967296) *
            4294967296 := by omega
      rw [hb] at hval ⊢
      zify at hval hd1 hd2 ⊢
      linear_combination hval + (4294967296 : ℤ) ^ k * hd2 - (4294967296 : ℤ) ^ k * hd1

/-- The invariant of step D6 after `k` digits: the carry `x.1` and the array `x.2`, whose digits
from position `j` hold the sum so far. -/
def AddbackInv (w vn : Array UInt64) (j : UInt64) (k : Nat) (x : UInt64 × Array UInt64) : Prop :=
  x.2.size = w.size ∧ (∀ p : Nat, x.2[p]!.toNat < base) ∧ x.1.toNat ≤ 1 ∧
    (∀ p, p < j.toNat ∨ j.toNat + k ≤ p → x.2[p]! = w[p]!) ∧
    segValue x.2 j.toNat k + x.1.toNat * base ^ k = segValue w j.toNat k + prefixValue vn k

/-- Step D6: the loop adds the first `t + 1` digits of `vn` to the `t + 1` digits of `w` from
position `j`. -/
theorem addback_spec (w vn : Array UInt64) (j t : UInt64) (hw : ∀ p : Nat, w[p]!.toNat < base)
    (hvn : ∀ p : Nat, vn[p]!.toNat < base) (hjt : j.toNat + t.toNat + 1 ≤ w.size)
    (hsz : w.size < 2 ^ 63) :
    AddbackInv w vn j (t.toNat + 1)
      (LeanExe.loop (t + 1) ((0 : UInt64), w) fun i x =>
        ((x.2[(i + j).toNat]! + vn[i.toNat]! + x.1) / 4294967296,
          x.2.set! (i + j).toNat ((x.2[(i + j).toNat]! + vn[i.toNat]! + x.1) % 4294967296))) := by
  have ht1 : (t + 1).toNat = t.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  rw [← ht1]
  refine loop_induction (P := AddbackInv w vn j) ?_ ?_
  · refine ⟨rfl, hw, by simp, fun _ _ => rfl, ?_⟩
    simp [segValue, prefixValue_zero]
  · intro k x hk ⟨hs, hd, hc, hun, hval⟩
    rw [ht1] at hk
    have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
    have hidx : (UInt64.ofNat k + j).toNat = j.toNat + k := by
      simp only [UInt64.toNat_add, hkk]; omega
    have hb := base_eq
    have ha := hvn k
    have hww := hd (j.toNat + k)
    have hwk : x.2[j.toNat + k]! = w[j.toNat + k]! := hun _ (Or.inr (by omega))
    rw [hb] at ha hww
    have hsum : (x.2[j.toNat + k]! + vn[k]! + x.1).toNat =
        x.2[j.toNat + k]!.toNat + vn[k]!.toNat + x.1.toNat := by
      simp only [UInt64.toNat_add]; omega
    simp only [hkk, hidx]
    have hget := fun (p : Nat) => get_set x.2 (j.toNat + k)
      ((x.2[j.toNat + k]! + vn[k]! + x.1) % 4294967296) p (by omega)
    refine ⟨by simp [hs], fun p => ?_, ?_, fun p hp' => ?_, ?_⟩
    · rw [hget]; split
      · rw [UInt64.toNat_mod, hsum, hb]; simp only [UInt64.reduceToNat]; omega
      · exact hd p
    · rw [UInt64.toNat_div, hsum]; simp only [UInt64.reduceToNat]; omega
    · rw [hget, ite_eq_right (show ¬ p = j.toNat + k by omega)]
      exact hun p (by omega)
    · have hc' : segValue (x.2.set! (j.toNat + k) ((x.2[j.toNat + k]! + vn[k]! + x.1) % 4294967296))
          j.toNat k = segValue x.2 j.toNat k :=
        segValue_congr fun i hi => by rw [hget, ite_eq_right (show ¬ j.toNat + i = j.toNat + k by omega)]
      dsimp only
      rw [segValue_succ, segValue_succ, hc', hget, ite_eq_left rfl, prefixValue_succ,
        UInt64.toNat_mod, hsum, UInt64.toNat_div, hsum]
      simp only [UInt64.reduceToNat]
      rw [hwk]
      have hd1 := Nat.mod_add_div (w[j.toNat + k]!.toNat + vn[k]!.toNat + x.1.toNat) 4294967296
      rw [hb] at hval ⊢
      zify at hval hd1 ⊢
      linear_combination hval + (4294967296 : ℤ) ^ k * hd1

/-! ### The main loop -/

theorem segValue_zero_tail {w : Array UInt64} {j n r : Nat}
    (h : ∀ i, n ≤ i → i < n + r → w[j + i]! = 0) : segValue w j (n + r) = segValue w j n := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← Nat.add_assoc, segValue_succ, ih fun i h1 h2 => h i h1 (by omega), h (n + r) (by omega)
      (by omega)]
    simp

/-- The digits of an array of digits at and above `k` are 0 when its first `N` digits hold a number
below `base ^ k`. -/
theorem digit_zero_of_lt {w : Array UInt64} {N k p : Nat} (hw : ∀ q : Nat, w[q]!.toNat < base)
    (hsz : w.size ≤ N) (hlt : prefixValue w N < base ^ k) (hp : k ≤ p) : w[p]! = 0 := by
  rcases Nat.lt_or_ge p N with h | h
  · have hd := prefixValue_digit (fun q _ => hw q) h
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right base_pos hp)), Nat.zero_mod] at hd
    exact UInt64.toNat_inj.mp (by rw [← hd]; rfl)
  · exact getElem!_neg w p (by omega)

/-- The quotient by `V b^j` from the quotient and the remainder by `V b^(j + 1)`. -/
theorem div_split (U D b : Nat) : U / D = U / (D * b) * b + U % (D * b) / D := by
  rw [Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' (U / D) b).symm

/-- The invariant of the main loop of Algorithm D when the positions from `J` on are done: the
quotient digits so far are the top part of `U / V`, and the partial remainder is `U` modulo
`V b^J`. -/
def DivInv (U V m J : Nat) (s : Array UInt64 × Array UInt64) : Prop :=
  s.1.size = m ∧ (∀ p : Nat, s.1[p]!.toNat < base) ∧ (∀ p, p < J → s.1[p]! = 0) ∧
    prefixValue s.1 m = U / (V * base ^ J) * base ^ J ∧
    s.2.size = m + 1 ∧ (∀ p : Nat, s.2[p]!.toNat < base) ∧
    prefixValue s.2 (m + 1) = U % (V * base ^ J)

/-- The end of a step of the main loop: writing the quotient digit `d` at position `j` and the
window `X % V` of the partial remainder at positions `j` to `j + t` gives the invariant at `j`. -/
theorem div_step_finish (U V m J T : Nat) (s : Array UInt64 × Array UInt64) (d : UInt64)
    (w' : Array UInt64) (hT : 2 ≤ T) (hJm : J + T ≤ m) (hVpos : 0 < V) (hVlt : V < base ^ T)
    (hinv : DivInv U V m (J + 1) s) (hd : d.toNat = segValue s.2 J (T + 1) / V)
    (hws : w'.size = m + 1) (hwd : ∀ p : Nat, w'[p]!.toNat < base)
    (hun : ∀ p, p < J ∨ J + T + 1 ≤ p → w'[p]! = s.2[p]!)
    (hseg : segValue w' J (T + 1) = segValue s.2 J (T + 1) % V) :
    DivInv U V m J (s.1.set! J d, w') := by
  obtain ⟨hqs, hqd, hqz, hqv, hss, hsd, hsv⟩ := hinv
  have hb0 := base_pos
  have hBJ : 0 < base ^ J := pow_pos hb0 J
  have hD : V * base ^ (J + 1) = V * base ^ J * base := by rw [pow_succ]; ring
  have hWlt : U % (V * base ^ (J + 1)) < V * base ^ (J + 1) := Nat.mod_lt _ (by positivity)
  have hzs : ∀ p, J + T + 1 ≤ p → s.2[p]! = 0 := fun p hp =>
    digit_zero_of_lt (N := m + 1) (k := J + T + 1) hsd (by omega) (by
      rw [hsv]
      calc U % (V * base ^ (J + 1)) < V * base ^ (J + 1) := hWlt
        _ ≤ base ^ T * base ^ (J + 1) := Nat.mul_le_mul_right _ (le_of_lt hVlt)
        _ = base ^ (J + T + 1) := by rw [← pow_add]; congr 1; omega) hp
  have htail : m + 1 = J + (T + 1 + (m + 1 - J - (T + 1))) := by omega
  have hsplit : prefixValue s.2 (m + 1) = prefixValue s.2 J + base ^ J * segValue s.2 J (T + 1) := by
    rw [htail, prefixValue_split, segValue_zero_tail fun i h1 h2 => hzs (J + i) (by omega)]
  have hsplit' : prefixValue w' (m + 1) = prefixValue s.2 J + base ^ J * segValue w' J (T + 1) := by
    rw [htail, prefixValue_split, segValue_zero_tail fun i h1 h2 => by
      rw [hun _ (Or.inr (by omega))]; exact hzs (J + i) (by omega)]
    congr 1
    exact prefixValue_congr fun p hp => hun p (Or.inl hp)
  have hlow := prefixValue_lt (u := s.2) (q := J) fun p _ => hsd p
  generalize hX : segValue s.2 J (T + 1) = X at hsplit hseg hd
  generalize hL : prefixValue s.2 J = L at hsplit hsplit' hlow
  -- the quotient digit
  have hWq : U % (V * base ^ (J + 1)) / (V * base ^ J) = X / V := by
    rw [← hsv, hsplit, Nat.mul_comm V, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ hBJ, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hq : U / (V * base ^ J) = U / (V * base ^ (J + 1)) * base + X / V := by
    rw [div_split U (V * base ^ J) base, ← hD, hWq]
  have hXV := Nat.div_add_mod X V
  have hXm := Nat.mod_lt X hVpos
  refine ⟨by simp [hqs], fun p => ?_, fun p hp => ?_, ?_, hws, hwd, ?_⟩
  · rw [get_set s.1 J d p (by omega)]; split
    · rw [hd]
      have hXlt : X < base * V := by
        have h1 : base ^ J * X < base ^ J * (base * V) := by
          calc base ^ J * X ≤ prefixValue s.2 (m + 1) := by rw [hsplit]; omega
            _ < V * base ^ (J + 1) := by rw [hsv]; exact hWlt
            _ = base ^ J * (base * V) := by rw [pow_succ]; ring
        exact Nat.lt_of_mul_lt_mul_left h1
      exact (Nat.div_lt_iff_lt_mul hVpos).mpr hXlt
    · exact hqd p
  · rw [get_set s.1 J d p (by omega), ite_eq_right (show ¬ p = J by omega)]; exact hqz p (by omega)
  · rw [prefixValue_set (by omega) (by omega) (hqz J (by omega)), hqv, hd, hq, pow_succ]
    ring
  · rw [hsplit', hseg]
    have hU := Nat.div_add_mod U (V * base ^ (J + 1))
    rw [← hsv, hsplit] at hU
    have h1 : base ^ J * (X % V) + base ^ J ≤ V * base ^ J := by
      calc base ^ J * (X % V) + base ^ J = (X % V + 1) * base ^ J := by ring
        _ ≤ V * base ^ J := Nat.mul_le_mul_right _ hXm
    have hbound : L + base ^ J * (X % V) < V * base ^ J := by omega
    have hU' : U = (L + base ^ J * (X % V)) + U / (V * base ^ J) * (V * base ^ J) := by
      rw [hq]
      zify at hU hXV ⊢
      linear_combination -hU - ((base : ℤ) ^ J) * hXV
    rw [hU', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbound]

/-- A step of the main loop from the bounds on the trial digit `qh` and the invariants of steps D4
and D6: a negative difference, a borrow of 1, means that `qh` is one too large, and the add-back
restores the window `X % V`. -/
theorem div_step_core (U V m : Nat) (vn : Array UInt64) (j t qh : UInt64)
    (s : Array UInt64 × Array UInt64) (ms : UInt64 × UInt64 × Array UInt64)
    (ab : UInt64 × Array UInt64) (hT : 2 ≤ t.toNat) (hjm : j.toNat + t.toNat ≤ m)
    (hvn : ∀ p : Nat, vn[p]!.toNat < base) (hvT : vn[t.toNat]! = 0)
    (hV : prefixValue vn t.toNat = V) (hVpos : 0 < V) (hinv : DivInv U V m (j.toNat + 1) s)
    (hq1 : segValue s.2 j.toNat (t.toNat + 1) / V ≤ qh.toNat)
    (hq2 : qh.toNat ≤ segValue s.2 j.toNat (t.toNat + 1) / V + 1) (hq3 : qh.toNat < base)
    (hms : MulsubInv s.2 vn qh j (t.toNat + 1) ms) (hab : AddbackInv ms.2.2 vn j (t.toNat + 1) ab) :
    DivInv U V m j.toNat (s.1.set! j.toNat (if ms.2.1 = 1 then qh - 1 else qh),
      if ms.2.1 = 1 then ab.2 else ms.2.2) := by
  have hb0 := base_pos
  have hVlt : V < base ^ t.toNat := by rw [← hV]; exact prefixValue_lt fun p _ => hvn p
  have hpv : prefixValue vn (t.toNat + 1) = V := by
    rw [prefixValue_succ, hvT, hV, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
  obtain ⟨hs1, hd1, hbr, hc, hcb, hun1, hval1⟩ := hms
  obtain ⟨hs2, hd2, hc2, hun2, hval2⟩ := hab
  rw [hpv] at hcb hval1 hval2
  have hsz := hinv.2.2.2.2.1
  have hseg1 := segValue_lt (j := j.toNat) (n := t.toNat + 1) hd1
  have hseg2 := segValue_lt (j := j.toNat) (n := t.toNat + 1) hd2
  have hqV : qh.toNat * V < base ^ (t.toNat + 1) := by
    rw [pow_succ]
    calc qh.toNat * V < base * V := Nat.mul_lt_mul_of_pos_right hq3 hVpos
      _ ≤ base * base ^ t.toNat := Nat.mul_le_mul_left _ (le_of_lt hVlt)
      _ = base ^ t.toNat * base := by ring
  have hc0 : ms.1.toNat = 0 := by
    by_contra h
    have : base ^ (t.toNat + 1) ≤ ms.1.toNat * base ^ (t.toNat + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [hc0, Nat.add_zero] at hval1
  generalize hX : segValue s.2 j.toNat (t.toNat + 1) = X at hq1 hq2 hval1 hval2 ⊢
  have hXV := Nat.div_add_mod' X V
  have hXm := Nat.mod_lt X hVpos
  by_cases hb1 : ms.2.1 = 1
  · rw [ite_eq_left hb1, ite_eq_left hb1]
    have hb1' : ms.2.1.toNat = 1 := by rw [hb1]; rfl
    rw [hb1', Nat.one_mul] at hval1
    have hlt : X < qh.toNat * V := by omega
    have hqq : qh.toNat = X / V + 1 := by
      have : X / V < qh.toNat := (Nat.div_lt_iff_lt_mul hVpos).mpr hlt
      omega
    have hd : (qh - 1).toNat = X / V := by
      have h1 : (1 : UInt64) ≤ qh := UInt64.le_iff_toNat_le.mpr (by
        rw [hqq]; exact Nat.le_add_left _ _)
      rw [UInt64.toNat_sub_of_le qh 1 h1, hqq]
      rfl
    have hw2 : segValue ab.2 j.toNat (t.toNat + 1) = X % V := by
      rw [hqq, Nat.succ_mul] at hval1
      rcases (show ab.1.toNat = 0 ∨ ab.1.toNat = 1 by omega) with h | h
      · rw [h, Nat.zero_mul, Nat.add_zero] at hval2; omega
      · rw [h, Nat.one_mul] at hval2; omega
    exact div_step_finish U V m j.toNat t.toNat s (qh - 1) ab.2 hT hjm hVpos hVlt hinv
      (by rw [hd, hX]) (by rw [hs2, hs1, hsz]) hd2
      (fun p hp => by
        rw [hun2 p (by omega), hun1 p (by omega)])
      (by rw [hw2, hX])
  · rw [ite_eq_right hb1, ite_eq_right hb1]
    have hb0' : ms.2.1.toNat = 0 := by
      have : ms.2.1.toNat ≠ 1 := fun h => hb1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
      omega
    rw [hb0', Nat.zero_mul, Nat.add_zero] at hval1
    have hqq : qh.toNat = X / V := by
      have : qh.toNat ≤ X / V := (Nat.le_div_iff_mul_le hVpos).mpr (by omega)
      omega
    have hw1 : segValue ms.2.2 j.toNat (t.toNat + 1) = X % V := by
      rw [hqq] at hval1
      omega
    exact div_step_finish U V m j.toNat t.toNat s qh ms.2.2 hT hjm hVpos hVlt hinv
      (by rw [hqq, hX]) (by rw [hs1, hsz]) hd1 (fun p hp => hun1 p (by omega)) (by rw [hw1, hX])

/-- Under the invariant at `J + 1`, the window of `t + 1` digits from position `J` holds a number
below `b` times the divisor. -/
theorem DivInv.window_lt {U V m J T : Nat} {s : Array UInt64 × Array UInt64}
    (hinv : DivInv U V m (J + 1) s) (hJm : J + T ≤ m) (hVpos : 0 < V) (hVlt : V < base ^ T) :
    segValue s.2 J (T + 1) < base * V := by
  obtain ⟨-, -, -, -, hss, hsd, hsv⟩ := hinv
  have hWlt : U % (V * base ^ (J + 1)) < V * base ^ (J + 1) :=
    Nat.mod_lt _ (by have := base_pos; positivity)
  have hzs : ∀ p, J + T + 1 ≤ p → s.2[p]! = 0 := fun p hp =>
    digit_zero_of_lt (N := m + 1) (k := J + T + 1) hsd (by omega) (by
      rw [hsv]
      calc U % (V * base ^ (J + 1)) < V * base ^ (J + 1) := hWlt
        _ ≤ base ^ T * base ^ (J + 1) := Nat.mul_le_mul_right _ (le_of_lt hVlt)
        _ = base ^ (J + T + 1) := by rw [← pow_add]; congr 1; omega) hp
  have hsplit : prefixValue s.2 (m + 1) = prefixValue s.2 J + base ^ J * segValue s.2 J (T + 1) := by
    rw [show m + 1 = J + (T + 1 + (m + 1 - J - (T + 1))) by omega, prefixValue_split,
      segValue_zero_tail fun i h1 h2 => hzs (J + i) (by omega)]
  have h1 : base ^ J * segValue s.2 J (T + 1) < base ^ J * (base * V) := by
    calc base ^ J * segValue s.2 J (T + 1) ≤ prefixValue s.2 (m + 1) := by rw [hsplit]; omega
      _ < V * base ^ (J + 1) := by rw [hsv]; exact hWlt
      _ = base ^ J * (base * V) := by rw [pow_succ]; ring
  exact Nat.lt_of_mul_lt_mul_left h1

/-- One step of the main loop of the program. -/
theorem main_step (U V m : Nat) (vn : Array UInt64) (j t : UInt64) (s : Array UInt64 × Array UInt64)
    (hT : 2 ≤ t.toNat) (hjm : j.toNat + t.toNat ≤ m) (hm : m < 2 ^ 62)
    (hvn : ∀ p : Nat, vn[p]!.toNat < base) (hvT : vn[t.toNat]! = 0)
    (hvtop : base ≤ 2 * vn[t.toNat - 1]!.toNat) (hV : prefixValue vn t.toNat = V)
    (hinv : DivInv U V m (j.toNat + 1) s) :
    DivInv U V m j.toNat
      (let qh := trial s.2 vn j t
       let ms := LeanExe.loop (t + 1) ((0 : UInt64), (0 : UInt64), s.2) fun i x =>
         ((qh * vn[i.toNat]! + x.1) / 4294967296,
           1 - (x.2.2[(i + j).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
             - x.2.1) / 4294967296,
           x.2.2.set! (i + j).toNat
             ((x.2.2[(i + j).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
               - x.2.1) % 4294967296))
       (s.1.set! j.toNat (if ms.2.1 = 1 then qh - 1 else qh),
         if ms.2.1 = 1 then
           (LeanExe.loop (t + 1) ((0 : UInt64), ms.2.2) fun i x =>
             ((x.2[(i + j).toNat]! + vn[i.toNat]! + x.1) / 4294967296,
               x.2.set! (i + j).toNat ((x.2[(i + j).toNat]! + vn[i.toNat]! + x.1) % 4294967296))).2
         else ms.2.2)) := by
  have hVlt : V < base ^ t.toNat := by rw [← hV]; exact prefixValue_lt fun p _ => hvn p
  have hVpos : 0 < V := by
    rw [← hV, show t.toNat = t.toNat - 1 + 1 by omega, prefixValue_succ]
    have : 0 < vn[t.toNat - 1]!.toNat := by rw [base_eq] at hvtop; omega
    have := Nat.mul_pos this (pow_pos base_pos (t.toNat - 1))
    omega
  have hss := hinv.2.2.2.2.1
  have hsd := hinv.2.2.2.2.2.1
  have hX := hinv.window_lt hjm hVpos hVlt
  obtain ⟨hq1, hq2, hq3⟩ := trial_spec s.2 vn j t hsd hvn hT (by omega) hvtop (by rw [hV]; exact hX)
  rw [hV] at hq1 hq2
  have hms := mulsub_spec s.2 vn (trial s.2 vn j t) j t hsd hvn hq3 (by omega) (by omega)
  have hab := addback_spec _ vn j t hms.2.1 hvn (by rw [hms.1]; omega) (by rw [hms.1]; omega)
  exact div_step_core U V m vn j t (trial s.2 vn j t) s _ _ hT hjm hvn hvT hV hVpos hinv hq1 hq2
    hq3 hms hab

/-! ### Normalization -/

/-- Step D1: the shift `d = 2^(32 - L)` for the bit length `L` of the digit `x > 0` makes `x d` at
least `b / 2` and leaves `(x + 1) d` at most `b`. -/
theorem normalize (x : UInt64) (hx0 : 0 < x.toNat) (hx : x.toNat < base) :
    0 < ((1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits x)).toNat ∧
      ((1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits x)).toNat < base ∧
      base ≤ 2 * (x.toNat *
        ((1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits x)).toNat) ∧
      (x.toNat + 1) *
        ((1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits x)).toNat ≤ base := by
  have hw := wordBits_spec x
  have hL1 : 0 < Nat.size x.toNat := Nat.size_pos.mpr hx0
  have hL2 : Nat.size x.toNat ≤ 32 := Nat.size_le.mpr (by rw [base_eq] at hx; norm_num; exact hx)
  have hs : (32 - Library.Numerics.Arithmetic.Uscale.wordBits x).toNat = 32 - Nat.size x.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [hw]; simp only [UInt64.reduceToNat]; omega)), hw]
    rfl
  have hd : ((1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits x)).toNat =
      2 ^ (32 - Nat.size x.toNat) := by
    rw [shl_one _ (by rw [hs]; omega), hs]
  have hlow : 2 ^ (Nat.size x.toNat - 1) ≤ x.toNat := Nat.lt_size.mp (by omega)
  have hhigh : x.toNat < 2 ^ Nat.size x.toNat := Nat.lt_size_self _
  rw [hd, base_eq]
  have e1 : 2 ^ (Nat.size x.toNat - 1) * 2 ^ (32 - Nat.size x.toNat) * 2 = 4294967296 := by
    rw [← pow_add, ← pow_succ, show Nat.size x.toNat - 1 + (32 - Nat.size x.toNat) + 1 = 32 by
      omega]; norm_num
  have e2 : 2 ^ Nat.size x.toNat * 2 ^ (32 - Nat.size x.toNat) = 4294967296 := by
    rw [← pow_add, show Nat.size x.toNat + (32 - Nat.size x.toNat) = 32 by omega]; norm_num
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · calc 2 ^ (32 - Nat.size x.toNat) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 4294967296 := by norm_num
  · calc 4294967296 = 2 * (2 ^ (Nat.size x.toNat - 1) * 2 ^ (32 - Nat.size x.toNat)) := by
          rw [← e1]; ring
      _ ≤ 2 * (x.toNat * 2 ^ (32 - Nat.size x.toNat)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlow)
  · calc (x.toNat + 1) * 2 ^ (32 - Nat.size x.toNat)
        ≤ 2 ^ Nat.size x.toNat * 2 ^ (32 - Nat.size x.toNat) := Nat.mul_le_mul_right _ hhigh
      _ = 4294967296 := e2

/-! ### Algorithm D -/

/-- Induction over a loop whose invariant counts a position down from `J0` to 0. -/
theorem loop_down {α : Type} {n : UInt64} {init : α} {f : UInt64 → α → α} (Q : Nat → α → Prop)
    (J0 : Nat) (hn : n.toNat = J0) (h0 : Q J0 init)
    (hs : ∀ k s, k < J0 → Q (J0 - k) s → Q (J0 - k - 1) (f (UInt64.ofNat k) s)) :
    Q 0 (LeanExe.loop n init f) := by
  have h := loop_induction (n := n) (init := init) (f := f) (P := fun k s => Q (J0 - k) s)
    (by simpa using h0) (fun k s hk h => by
      rw [hn] at hk
      rw [show J0 - (k + 1) = J0 - k - 1 by omega]
      exact hs k s hk h)
  rw [hn, Nat.sub_self] at h
  exact h

/-- The main loop of Algorithm D, from the invariant at the first position `J0`, ends with the
invariant at 0. -/
theorem longDiv_loop (u vn w0 : Array UInt64) (t : UInt64) (U V : Nat) (hT : 2 ≤ t.toNat)
    (hm : u.size < 2 ^ 62) (hvn : ∀ p : Nat, vn[p]!.toNat < base) (hvT : vn[t.toNat]! = 0)
    (hvtop : base ≤ 2 * vn[t.toNat - 1]!.toNat) (hV : prefixValue vn t.toNat = V)
    (h0 : DivInv U V u.size (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0)
      (LeanExe.build u.size.toUInt64 (fun _ => (0 : UInt64)), w0)) :
    DivInv U V u.size 0
      (LeanExe.loop (if t ≤ u.size.toUInt64 then u.size.toUInt64 - t + 1 else 0)
        (LeanExe.build u.size.toUInt64 (fun _ => (0 : UInt64)), w0) fun e s =>
          let qh := trial s.2 vn (u.size.toUInt64 - t - e) t
          let ms := LeanExe.loop (t + 1) ((0 : UInt64), (0 : UInt64), s.2) fun i x =>
            ((qh * vn[i.toNat]! + x.1) / 4294967296,
              1 - (x.2.2[(i + (u.size.toUInt64 - t - e)).toNat]! + 4294967296 -
                (qh * vn[i.toNat]! + x.1) % 4294967296 - x.2.1) / 4294967296,
              x.2.2.set! (i + (u.size.toUInt64 - t - e)).toNat
                ((x.2.2[(i + (u.size.toUInt64 - t - e)).toNat]! + 4294967296 -
                  (qh * vn[i.toNat]! + x.1) % 4294967296 - x.2.1) % 4294967296))
          (s.1.set! (u.size.toUInt64 - t - e).toNat (if ms.2.1 = 1 then qh - 1 else qh),
            if ms.2.1 = 1 then
              (LeanExe.loop (t + 1) ((0 : UInt64), ms.2.2) fun i x =>
                ((x.2[(i + (u.size.toUInt64 - t - e)).toNat]! + vn[i.toNat]! + x.1) / 4294967296,
                  x.2.set! (i + (u.size.toUInt64 - t - e)).toNat
                    ((x.2[(i + (u.size.toUInt64 - t - e)).toNat]! + vn[i.toNat]! + x.1) %
                      4294967296))).2
            else ms.2.2)) := by
  have hmU := size_toNat (u := u) (by omega)
  have hK : (if t ≤ u.size.toUInt64 then u.size.toUInt64 - t + 1 else 0).toNat =
      (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0) := by
    by_cases h : t.toNat ≤ u.size
    · have h' : t ≤ u.size.toUInt64 := UInt64.le_iff_toNat_le.mpr (by rw [hmU]; exact h)
      rw [ite_eq_left h', ite_eq_left h, UInt64.toNat_add,
        UInt64.toNat_sub_of_le _ _ h', hmU]
      simp only [UInt64.reduceToNat]; omega
    · have h' : ¬ t ≤ u.size.toUInt64 := fun h' => h (by
        have := UInt64.le_iff_toNat_le.mp h'; rwa [hmU] at this)
      rw [ite_eq_right h', ite_eq_right h]; rfl
  refine loop_down (Q := fun J s => DivInv U V u.size J s) _ hK h0 ?_
  intro k s hk hinv
  have hTm : t.toNat ≤ u.size := by
    by_contra h; rw [ite_eq_right h] at hk; omega
  rw [ite_eq_left hTm] at hk hinv ⊢
  have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
  have hj : (u.size.toUInt64 - t - UInt64.ofNat k).toNat = u.size - t.toNat - k := by
    simp only [UInt64.toNat_sub, hmU, hkk]; omega
  rw [show u.size - t.toNat + 1 - k = (u.size.toUInt64 - t - UInt64.ofNat k).toNat + 1 by
    rw [hj]; omega] at hinv
  rw [show u.size - t.toNat + 1 - k - 1 = (u.size.toUInt64 - t - UInt64.ofNat k).toNat by
    rw [hj]; omega]
  exact main_step U V u.size vn (u.size.toUInt64 - t - UInt64.ofNat k) t s hT (by rw [hj]; omega)
    hm hvn hvT hvtop hV hinv

theorem array_ext {a b : Array UInt64} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b :=
  Array.ext hs fun i h1 h2 => by rw [← getElem!_pos a i h1, ← getElem!_pos b i h2]; exact h i h1

theorem append_get_left {a b : Array UInt64} {i : Nat} (hi : i < a.size) : (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp; omega), getElem!_pos a i hi, Array.getElem_append_left hi]

theorem append_get_right {a b : Array UInt64} {i : Nat} (hi : a.size ≤ i) (hi2 : i < a.size + b.size) :
    (a ++ b)[i]! = b[i - a.size]! := by
  rw [getElem!_pos (a ++ b) i (by simp; omega), getElem!_pos b (i - a.size) (by omega),
    Array.getElem_append_right hi]

theorem prefixValue_eq_of_zero {w : Array UInt64} {a c : Nat}
    (h : ∀ i, min a c ≤ i → w[i]! = 0) : prefixValue w a = prefixValue w c := by
  rcases Nat.le_total a c with hac | hac
  · exact (prefixValue_zero_tail hac fun i h1 _ => h i (by omega)).symm
  · exact prefixValue_zero_tail hac fun i h1 _ => h i (by omega)

/-- The end of Algorithm D: the quotient digits are `U / V`, and the short division of the
remainder of the normalized numbers by `d` gives the remainder, step D8. -/
theorem longDiv_final (u v : Array UInt64) (t d : UInt64) (s : Array UInt64 × Array UInt64)
    (hu : Digits u) (hsize : u.size + v.size < 2 ^ 62) (htn : t.toNat ≤ v.size)
    (hd0 : 0 < d.toNat) (hdb : d.toNat < base) (hVpos : 0 < value v)
    (hV'lt : value v * d.toNat < base ^ t.toNat)
    (hs : DivInv (value u * d.toNat) (value v * d.toNat) u.size 0 s) :
    LeanExe.build (u.size.toUInt64 + v.size.toUInt64) (fun i =>
      if i < u.size.toUInt64 then s.1[i.toNat]!
      else if i - u.size.toUInt64 < t then (shortDiv s.2 d t)[(i - u.size.toUInt64).toNat]!
      else 0) = divSpec (u, v) := by
  obtain ⟨hqs, hqd, -, hqv, hws, hwd, hwv⟩ := hs
  simp only [pow_zero, Nat.mul_one] at hqv hwv
  rw [Nat.mul_div_mul_right _ _ hd0] at hqv
  rw [Nat.mul_mod_mul_right] at hwv
  have hmU := size_toNat (u := u) (by omega)
  have hnU := size_toNat (u := v) (by omega)
  have hRV := Nat.mod_lt (value u) hVpos
  have hVle : value v ≤ value v * d.toNat := Nat.le_mul_of_pos_right _ hd0
  have hzr : ∀ p, t.toNat ≤ p → s.2[p]! = 0 := fun p hp =>
    digit_zero_of_lt (N := u.size + 1) (k := t.toNat) hwd (le_of_eq hws) (by
      rw [hwv]
      calc value u % value v * d.toNat < value v * d.toNat := Nat.mul_lt_mul_of_pos_right hRV hd0
        _ < base ^ t.toNat := hV'lt) hp
  have hpT : prefixValue s.2 t.toNat = value u % value v * d.toNat := by
    rw [prefixValue_eq_of_zero (c := u.size + 1) fun i hi =>
      if h : t.toNat ≤ i then hzr i h else getElem!_neg s.2 i (by omega), hwv]
  obtain ⟨hrs, hrd, hrv, -⟩ := shortDiv_spec s.2 d t hwd hd0 hdb (by omega)
  rw [hpT, Nat.mul_div_cancel _ hd0] at hrv
  have hQ : s.1 = digits u.size (value u / value v) := by
    symm
    apply digits_eq hqs fun p _ => hqd p
    have hv1 : value s.1 = value u / value v := by
      show prefixValue s.1 s.1.size = _
      rw [hqs, hqv]
    rw [hv1, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (value_lt hu))]
  have hRlt : value u % value v < base ^ t.toNat :=
    lt_of_lt_of_le (lt_of_lt_of_le hRV hVle) (le_of_lt hV'lt)
  unfold divSpec
  apply array_ext (by rw [build_size, Array.size_append, digits_size, digits_size]; simp only
    [UInt64.toNat_add, hmU, hnU]; omega)
  intro i hi
  rw [build_size] at hi
  have hmn : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    simp only [UInt64.toNat_add, hmU, hnU]; omega
  rw [hmn] at hi
  have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
  rw [build_get (by rw [hmn]; exact hi)]
  dsimp only
  by_cases him : i < u.size
  · have h1 : UInt64.ofNat i < u.size.toUInt64 := UInt64.lt_iff_toNat_lt.mpr (by rw [hii, hmU]; exact him)
    rw [ite_eq_left h1, hii, hQ, append_get_left (by rw [digits_size]; exact him)]
  · have h1 : ¬ UInt64.ofNat i < u.size.toUInt64 := fun h => him (by
      have := UInt64.lt_iff_toNat_lt.mp h; rwa [hii, hmU] at this)
    have hsub : (UInt64.ofNat i - u.size.toUInt64).toNat = i - u.size := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hii, hmU]; omega)), hii, hmU]
    rw [ite_eq_right h1, append_get_right (by rw [digits_size]; omega)
      (by rw [digits_size, digits_size]; exact hi), digits_size,
      digits_get (by omega)]
    by_cases hit : i - u.size < t.toNat
    · have h2 : UInt64.ofNat i - u.size.toUInt64 < t := UInt64.lt_iff_toNat_lt.mpr (by rw [hsub]; exact hit)
      rw [ite_eq_left h2, hsub, ← hrv, prefixValue_digit (fun p hp => hrd p hp) hit, UInt64.ofNat_toNat]
    · have h2 : ¬ UInt64.ofNat i - u.size.toUInt64 < t := fun h => hit (by
        have := UInt64.lt_iff_toNat_lt.mp h; rwa [hsub] at this)
      rw [ite_eq_right h2, Nat.div_eq_of_lt (lt_of_lt_of_le hRlt
        (Nat.pow_le_pow_right base_pos (by omega))), Nat.zero_mod]
      rfl

theorem sub_one_toNat {t : UInt64} (h : 1 ≤ t.toNat) : (t - 1).toNat = t.toNat - 1 := by
  have h1 : (1 : UInt64) ≤ t := UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega)
  rw [UInt64.toNat_sub_of_le t 1 h1]
  rfl

/-- Algorithm D for a divisor of at least two significant digits. -/
theorem longDiv_eq (u v : Array UInt64) (hu : Digits u) (hv : Digits v)
    (hsize : u.size + v.size < 2 ^ 62) (hT : 2 ≤ (significant v).toNat) :
    longDiv u v (significant v) = divSpec (u, v) := by
  obtain ⟨hts, hz, htop⟩ := significant_spec v (by omega)
  generalize significant v = t at hts hz htop hT ⊢
  have hb0 := base_pos
  have hmU := size_toNat (u := u) (by omega)
  have ht1 := sub_one_toNat (t := t) (by omega)
  have hx0 : 0 < v[(t - 1).toNat]!.toNat := by
    rw [ht1]
    rcases Nat.eq_zero_or_pos v[t.toNat - 1]!.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) (htop (by omega))
    · exact h
  have hxb : v[(t - 1).toNat]!.toNat < base := digit_all hv _
  obtain ⟨hd0, hdb, hdtop, hdx⟩ := normalize _ hx0 hxb
  unfold longDiv
  dsimp only
  generalize (1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!) = d
    at hd0 hdb hdtop hdx ⊢
  rw [ht1] at hx0 hdtop hdx
  -- the divisor
  have hVT : value v = prefixValue v t.toNat := by
    unfold value; exact prefixValue_zero_tail hts fun i h1 _ => hz i h1
  have hsplitV := prefixValue_succ v (t.toNat - 1)
  rw [show t.toNat - 1 + 1 = t.toNat by omega, ← hVT] at hsplitV
  have hlowV := prefixValue_lt (u := v) (q := t.toNat - 1) fun p _ => digit_all hv p
  have hVge : v[t.toNat - 1]!.toNat * base ^ (t.toNat - 1) ≤ value v := by omega
  have hVpos : 0 < value v := lt_of_lt_of_le (Nat.mul_pos hx0 (pow_pos hb0 _)) hVge
  have hVlt' : value v < (v[t.toNat - 1]!.toNat + 1) * base ^ (t.toNat - 1) := by
    rw [Nat.succ_mul]; omega
  have hbT : base * base ^ (t.toNat - 1) = base ^ t.toNat := by
    rw [← pow_succ']; congr 1; omega
  have hV'lt : value v * d.toNat < base ^ t.toNat := by
    calc value v * d.toNat < (v[t.toNat - 1]!.toNat + 1) * base ^ (t.toNat - 1) * d.toNat :=
          Nat.mul_lt_mul_of_pos_right hVlt' hd0
      _ = (v[t.toNat - 1]!.toNat + 1) * d.toNat * base ^ (t.toNat - 1) := by ring
      _ ≤ base * base ^ (t.toNat - 1) := Nat.mul_le_mul_right _ hdx
      _ = base ^ t.toNat := hbT
  -- the normalized divisor
  have hd32 : d.toNat < 2 ^ 32 := by have := hdb; rw [base_eq] at this; omega
  obtain ⟨hvnL, hvnV, hvnS⟩ := mulSmall_spec v d 0 (limbs_of_digits hv) (by omega) hd32 (by simp)
  have hvnD : ∀ p : Nat, (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)[p]!.toNat < base :=
    digit_all (digits_of_limbs hvnL)
  have hvnval : prefixValue (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0) (v.size + 1) =
      value v * d.toNat := by
    have := value_eq_val (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)
    unfold value at this
    rw [hvnS] at this
    rw [this, hvnV, ← value_eq_val]; simp
  have hvnz : ∀ p, t.toNat ≤ p → (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)[p]! = 0 :=
    fun p hp => digit_zero_of_lt (N := v.size + 1) (k := t.toNat) hvnD (le_of_eq hvnS)
      (by rw [hvnval]; exact hV'lt) hp
  have hvnT : prefixValue (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0) t.toNat =
      value v * d.toNat := by
    rw [prefixValue_eq_of_zero (c := v.size + 1) fun i hi =>
      if h : t.toNat ≤ i then hvnz i h else getElem!_neg _ i (by rw [hvnS]; omega), hvnval]
  have hvntop : base ≤ 2 * (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)[t.toNat - 1]!.toNat := by
    have hdig := prefixValue_digit (u := Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)
      (n := t.toNat) (i := t.toNat - 1) (fun p _ => hvnD p) (by omega)
    rw [hvnT] at hdig
    have h1 : value v * d.toNat / base ^ (t.toNat - 1) < base := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hb0 _), hbT]; exact hV'lt
    have h2 : v[t.toNat - 1]!.toNat * d.toNat ≤ value v * d.toNat / base ^ (t.toNat - 1) := by
      rw [Nat.le_div_iff_mul_le (pow_pos hb0 _)]
      calc v[t.toNat - 1]!.toNat * d.toNat * base ^ (t.toNat - 1) =
            v[t.toNat - 1]!.toNat * base ^ (t.toNat - 1) * d.toNat := by ring
        _ ≤ value v * d.toNat := Nat.mul_le_mul_right _ hVge
    rw [Nat.mod_eq_of_lt h1] at hdig
    rw [← hdig]; omega
  -- the normalized dividend and the first invariant
  obtain ⟨hunL, hunV, hunS⟩ := mulSmall_spec u d 0 (limbs_of_digits hu) (by omega) hd32 (by simp)
  have hunval : prefixValue (Library.Numerics.Arithmetic.Uscale.mulSmall u d 0) (u.size + 1) =
      value u * d.toNat := by
    have := value_eq_val (Library.Numerics.Arithmetic.Uscale.mulSmall u d 0)
    unfold value at this
    rw [hunS] at this
    rw [this, hunV, ← value_eq_val]; simp
  have h0 : DivInv (value u * d.toNat) (value v * d.toNat) u.size
      (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0)
      (LeanExe.build u.size.toUInt64 (fun _ => (0 : UInt64)),
        Library.Numerics.Arithmetic.Uscale.mulSmall u d 0) := by
    have hVb : base ^ u.size ≤ value v * base ^ (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0) := by
      have hx1 : base ^ (t.toNat - 1) ≤ value v :=
        le_trans (Nat.le_mul_of_pos_left _ hx0) hVge
      split
      · calc base ^ u.size = base ^ (t.toNat - 1) * base ^ (u.size - t.toNat + 1) := by
              rw [← pow_add]; congr 1; omega
          _ ≤ value v * base ^ (u.size - t.toNat + 1) := Nat.mul_le_mul_right _ hx1
      · rw [pow_zero, Nat.mul_one]
        exact le_trans (Nat.pow_le_pow_right hb0 (by omega)) hx1
    have hlt : value u * d.toNat < value v * d.toNat *
        base ^ (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0) := by
      calc value u * d.toNat < base ^ u.size * d.toNat := Nat.mul_lt_mul_of_pos_right (value_lt hu) hd0
        _ ≤ value v * base ^ (if t.toNat ≤ u.size then u.size - t.toNat + 1 else 0) * d.toNat :=
            Nat.mul_le_mul_right _ hVb
        _ = _ := by ring
    have hz0 : ∀ p : Nat, (LeanExe.build u.size.toUInt64 fun _ => (0 : UInt64))[p]! = 0 := by
      intro p
      by_cases hp : p < u.size.toUInt64.toNat
      · rw [build_get hp]
      · rw [build_get_out hp]; rfl
    refine ⟨by rw [build_size, hmU], fun p => by rw [hz0]; exact hb0, fun p _ => hz0 p, ?_, hunS,
      digit_all (digits_of_limbs hunL), ?_⟩
    · rw [prefixValue_zeros hz0, Nat.div_eq_of_lt hlt, Nat.zero_mul]
    · rw [hunval, Nat.mod_eq_of_lt hlt]
  exact longDiv_final u v t d _ hu hsize hts hd0 hdb hVpos hV'lt
    (longDiv_loop u (Library.Numerics.Arithmetic.Uscale.mulSmall v d 0)
      (Library.Numerics.Arithmetic.Uscale.mulSmall u d 0) t _ _ hT (by omega) hvnD
      (hvnz _ (le_refl _)) hvntop hvnT h0)

/-- Every digit of the value of a digit array, including those past its end, is its word. -/
theorem value_digit {u : Array UInt64} (hu : Digits u) (p : Nat) :
    value u / base ^ p % base = u[p]!.toNat := by
  rcases Nat.lt_or_ge p u.size with h | h
  · exact prefixValue_digit (fun q _ => digit_all hu q) h
  · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (value_lt hu) (Nat.pow_le_pow_right base_pos h)),
      getElem!_neg u p (by omega)]
    rfl

/-- Algorithm D and its two special cases compute `divSpec`. -/
theorem divide_eq (u v : Array UInt64) (hu : Digits u) (hv : Digits v)
    (hsize : u.size + v.size < 2 ^ 62) : divide u v = divSpec (u, v) := by
  obtain ⟨hts, hz, htop⟩ := significant_spec v (by omega)
  have hmU := size_toNat (u := u) (by omega)
  have hnU := size_toNat (u := v) (by omega)
  have hmn : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    simp only [UInt64.toNat_add, hmU, hnU]; omega
  unfold divide
  by_cases h0 : significant v = 0
  · rw [ite_eq_left h0]
    have ht0 : (significant v).toNat = 0 := by rw [h0]; rfl
    have hV0 : value v = 0 := by
      unfold value
      rw [prefixValue_zero_tail (Nat.zero_le _) fun i _ _ => hz i (by omega), prefixValue_zero]
    unfold divSpec
    dsimp only
    rw [hV0, Nat.div_zero, Nat.mod_zero]
    apply array_ext (by rw [build_size, hmn, Array.size_append, digits_size, digits_size])
    intro i hi
    rw [build_size, hmn] at hi
    have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    rw [build_get (by rw [hmn]; exact hi)]
    by_cases him : i < u.size
    · have h1 : UInt64.ofNat i < u.size.toUInt64 :=
        UInt64.lt_iff_toNat_lt.mpr (by rw [hii, hmU]; exact him)
      rw [ite_eq_left h1, append_get_left (by rw [digits_size]; exact him), digits_get him,
        Nat.zero_div, Nat.zero_mod]
      rfl
    · have h1 : ¬ UInt64.ofNat i < u.size.toUInt64 := fun h => him (by
        have := UInt64.lt_iff_toNat_lt.mp h; rwa [hii, hmU] at this)
      have hsub : (UInt64.ofNat i - u.size.toUInt64).toNat = i - u.size := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hii, hmU]; omega)), hii,
          hmU]
      rw [ite_eq_right h1, append_get_right (by rw [digits_size]; omega)
        (by rw [digits_size, digits_size]; exact hi), digits_size, digits_get (by omega),
        value_digit hu, hsub, UInt64.ofNat_toNat]
  · rw [ite_eq_right h0]
    by_cases h1 : significant v = 1
    · rw [ite_eq_left h1]
      have ht1 : (significant v).toNat = 1 := by rw [h1]; rfl
      have hv0 : v[0]! ≠ 0 := by have := htop (by omega); rwa [ht1] at this
      have hV : value v = v[0]!.toNat := by
        unfold value
        rw [prefixValue_zero_tail (show 1 ≤ v.size by omega) fun i h2 _ => hz i (by omega),
          prefixValue_succ, prefixValue_zero]
        simp
      have hv0' : 0 < v[0]!.toNat := by
        rcases Nat.eq_zero_or_pos v[0]!.toNat with h | h
        · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hv0
        · exact h
      have hvb := digit_all hv 0
      have hz0 : (0 : UInt64).toNat = 0 := rfl
      rw [hz0]
      obtain ⟨hrs, hrd, hrv, hrr⟩ := shortDiv_spec u v[0]! u.size.toUInt64 (digit_all hu) hv0' hvb
        (by rw [hmU]; omega)
      rw [hmU] at hrs hrd hrv hrr
      have hpu : prefixValue u u.size = value u := rfl
      rw [hpu, ← hV] at hrv hrr
      have hRV := Nat.mod_lt (value u) (show 0 < value v by omega)
      unfold divSpec
      dsimp only
      apply array_ext (by rw [build_size, hmn, Array.size_append, digits_size, digits_size])
      intro i hi
      rw [build_size, hmn] at hi
      have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      rw [build_get (by rw [hmn]; exact hi)]
      by_cases him : i ≤ u.size
      · have h2 : UInt64.ofNat i ≤ u.size.toUInt64 :=
          UInt64.le_iff_toNat_le.mpr (by rw [hii, hmU]; exact him)
        rw [ite_eq_left h2, hii]
        rcases Nat.lt_or_ge i u.size with h3 | h3
        · rw [append_get_left (by rw [digits_size]; exact h3), digits_get h3, ← hrv,
            prefixValue_digit (fun p hp => hrd p hp) h3, UInt64.ofNat_toNat]
        · have h4 : i = u.size := by omega
          rw [h4, append_get_right (by rw [digits_size]) (by rw [digits_size, digits_size]; omega),
            digits_size, Nat.sub_self, digits_get (by omega), pow_zero, Nat.div_one,
            Nat.mod_eq_of_lt (by omega), ← hrr, UInt64.ofNat_toNat]
      · have h2 : ¬ UInt64.ofNat i ≤ u.size.toUInt64 := fun h => him (by
          have := UInt64.le_iff_toNat_le.mp h; rwa [hii, hmU] at this)
        rw [ite_eq_right h2, append_get_right (by rw [digits_size]; omega)
          (by rw [digits_size, digits_size]; exact hi), digits_size, digits_get (by omega),
          Nat.div_eq_of_lt (lt_of_lt_of_le (show value u % value v < base by omega)
            (by calc base = base ^ 1 := (pow_one _).symm
                  _ ≤ base ^ (i - u.size) := Nat.pow_le_pow_right base_pos (by omega))),
          Nat.zero_mod]
        rfl
    · rw [ite_eq_right h1]
      have h2 : 2 ≤ (significant v).toNat := by
        have a : (significant v).toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
        have b : (significant v).toNat ≠ 1 := fun h => h1 (UInt64.toNat_inj.mp (by rw [h]; rfl))
        omega
      exact longDiv_eq u v hu hv hsize h2

end Library.Numerics.MultiPrecision
