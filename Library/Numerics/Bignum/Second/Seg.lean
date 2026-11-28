module

public import Library.Numerics.Bignum.OfText
public import Library.Numerics.Bignum.Second.Program

@[expose] public section

/-!
Values of segments of a workspace and the in-place loops over them.  `segVal W p k` is the number
that the `k` words of `W` from position `p` represent in base `2^32`, least significant first, and
`SegDigits W p k` states that those words are limbs.  Each loop of the second iteration reads and
writes one array, the workspace, and its theorem states the value written in terms of the values
read, that the array keeps its size, and that every word outside the written range keeps its
value.  A loop that writes position `d + i` at step `i` reads position `x + j` at a later step `j`
only when `x + j` is not among the positions already written, which the hypotheses `hix` and
`hiy` state and which holds both for disjoint ranges and for a loop that updates its range in
place.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

/-! ## Values of segments -/

/-- The number that the `k` words of `W` from position `p` represent, least significant first. -/
def segVal (W : Array UInt64) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => segVal W p k + W[p + k]!.toNat * base ^ k

/-- The `k` words of `W` from `p` are limbs. -/
def SegDigits (W : Array UInt64) (p k : ℕ) : Prop := ∀ i, i < k → W[p + i]!.toNat < base

theorem segVal_zero (W : Array UInt64) (p : ℕ) : segVal W p 0 = 0 := rfl

theorem segVal_succ (W : Array UInt64) (p k : ℕ) :
    segVal W p (k + 1) = segVal W p k + W[p + k]!.toNat * base ^ k := rfl

theorem segVal_congr {W W' : Array UInt64} {p p' k : ℕ}
    (h : ∀ i, i < k → W[p + i]! = W'[p' + i]!) : segVal W p k = segVal W' p' k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [segVal_succ, segVal_succ, ih fun i hi => h i (by omega), h k (by omega)]

theorem segVal_add (W : Array UInt64) (p a b : ℕ) :
    segVal W p (a + b) = segVal W p a + base ^ a * segVal W (p + a) b := by
  induction b with
  | zero => simp [segVal]
  | succ b ih =>
    rw [← Nat.add_assoc, segVal_succ, ih, segVal_succ, Nat.add_assoc p a b, pow_add]
    ring

theorem segVal_lt {W : Array UInt64} {p k : ℕ} (h : SegDigits W p k) : segVal W p k < base ^ k := by
  induction k with
  | zero => simp [segVal]
  | succ k ih =>
    rw [segVal_succ, pow_succ]
    have h1 := ih fun i hi => h i (by omega)
    have h2 := h k (by omega)
    have h3 : W[p + k]!.toNat * base ^ k + base ^ k ≤ base ^ k * base := by
      calc W[p + k]!.toNat * base ^ k + base ^ k = (W[p + k]!.toNat + 1) * base ^ k := by ring
        _ ≤ base * base ^ k := Nat.mul_le_mul_right _ h2
        _ = base ^ k * base := by ring
    omega

theorem segVal_zeros {W : Array UInt64} {p k : ℕ} (h : ∀ i, i < k → W[p + i]! = 0) :
    segVal W p k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [segVal_succ, ih fun i hi => h i (by omega), h k (by omega)]; simp

theorem segVal_eq_prefixValue (u : Array UInt64) (k : ℕ) : segVal u 0 k = prefixValue u k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [segVal_succ, ih, prefixValue_succ, Nat.zero_add]

theorem segVal_value (u : Array UInt64) : segVal u 0 u.size = value u :=
  segVal_eq_prefixValue u u.size

theorem SegDigits.mono {W : Array UInt64} {p k k' : ℕ} (h : SegDigits W p k) (hk : k' ≤ k) :
    SegDigits W p k' := fun i hi => h i (by omega)

theorem SegDigits.shift {W : Array UInt64} {p a k : ℕ} (h : SegDigits W p (a + k)) :
    SegDigits W (p + a) k := fun i hi => by rw [Nat.add_assoc]; exact h (a + i) (by omega)

theorem SegDigits.join {W : Array UInt64} {p a k : ℕ} (h1 : SegDigits W p a)
    (h2 : SegDigits W (p + a) k) : SegDigits W p (a + k) := fun i hi => by
  by_cases hi' : i < a
  · exact h1 i hi'
  · have := h2 (i - a) (by omega)
    rwa [show p + a + (i - a) = p + i by omega] at this

theorem SegDigits.congr {W W' : Array UInt64} {p k : ℕ} (h : SegDigits W p k)
    (he : ∀ i, i < k → W'[p + i]! = W[p + i]!) : SegDigits W' p k := fun i hi => by
  rw [he i hi]; exact h i hi

/-- A segment of limbs whose value is below `base ^ a` has zeros from position `a` on. -/
theorem segVal_high_zero {W : Array UInt64} {p a k : ℕ} (hd : SegDigits W p (a + k))
    (hlt : segVal W p (a + k) < base ^ a) : segVal W (p + a) k = 0 := by
  rw [segVal_add] at hlt
  by_contra hne
  have hpos : 1 ≤ segVal W (p + a) k := Nat.one_le_iff_ne_zero.mpr hne
  have : base ^ a * 1 ≤ base ^ a * segVal W (p + a) k := Nat.mul_le_mul_left _ hpos
  omega

/-- The digit at position `i` of a segment of limbs. -/
theorem segVal_digit {W : Array UInt64} {p k i : ℕ} (hd : SegDigits W p k) (hi : i < k) :
    segVal W p k / base ^ i % base = W[p + i]!.toNat := by
  have hsplit := segVal_add W p i (k - i)
  rw [show i + (k - i) = k by omega] at hsplit
  have hlo := segVal_lt (hd.mono (k' := i) (by omega))
  have hhi := segVal_add W (p + i) 1 (k - i - 1)
  rw [show 1 + (k - i - 1) = k - i by omega] at hhi
  have h1 : segVal W (p + i) 1 = W[p + i]!.toNat := by simp [segVal]
  rw [hsplit, hhi, h1, Nat.add_mul_div_left _ _ (pow_pos base_pos i), Nat.div_eq_of_lt hlo,
    Nat.zero_add, pow_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd i hi)]

/-! ## Positions as words -/

theorem toNat_add_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_lt {i : ℕ} (h : i < 2 ^ 64) : (UInt64.ofNat i).toNat = i :=
  UInt64.toNat_ofNat_of_lt' h

/-- A word below the base. -/
theorem toNat_lt_base_of {x : UInt64} {X : ℕ} (hx : x.toNat = X) (h : X < base) : x.toNat < base :=
  hx ▸ h

/-! ## Addition in place -/

/-- The value of a read that the earlier steps of a loop left alone. -/
theorem read_kept {W W' : Array UInt64} {d x i : ℕ}
    (hfr : ∀ q, (q < d ∨ d + i ≤ q) → W'[q]! = W[q]!)
    (hix : ∀ i', i' < i → d + i' ≠ x + i) : W'[x + i]! = W[x + i]! := by
  apply hfr
  by_contra hcon
  push_neg at hcon
  exact hix (x + i - d) (by omega) (by omega)

/-- `addGen` writes over the `n` words from `dp` the sum of the `n` words from `xp` and the first
`min k n` words from `yp`, with the final carry. -/
theorem addGen_spec (W : Array UInt64) (xp yp k dp n : UInt64) (hW : W.size < 2 ^ 64)
    (hx : xp.toNat + n.toNat ≤ W.size) (hy : yp.toNat + min k.toNat n.toNat ≤ W.size)
    (hd : dp.toNat + n.toNat ≤ W.size)
    (hdx : SegDigits W xp.toNat n.toNat) (hdy : SegDigits W yp.toNat (min k.toNat n.toNat))
    (hix : ∀ i j, i < j → j < n.toNat → dp.toNat + i ≠ xp.toNat + j)
    (hiy : ∀ i j, i < j → j < min k.toNat n.toNat → dp.toNat + i ≠ yp.toNat + j) :
    (addGen W xp yp k dp n).2.size = W.size ∧
    (∀ q, (q < dp.toNat ∨ dp.toNat + n.toNat ≤ q) → (addGen W xp yp k dp n).2[q]! = W[q]!) ∧
    SegDigits (addGen W xp yp k dp n).2 dp.toNat n.toNat ∧ (addGen W xp yp k dp n).1.toNat ≤ 1 ∧
    segVal (addGen W xp yp k dp n).2 dp.toNat n.toNat +
        (addGen W xp yp k dp n).1.toNat * base ^ n.toNat =
      segVal W xp.toNat n.toNat + segVal W yp.toNat (min k.toNat n.toNat) := by
  unfold addGen
  refine loop_induction (P := fun i (s : UInt64 × Array UInt64) => s.2.size = W.size ∧
      (∀ q, (q < dp.toNat ∨ dp.toNat + i ≤ q) → s.2[q]! = W[q]!) ∧
      SegDigits s.2 dp.toNat i ∧ s.1.toNat ≤ 1 ∧
      segVal s.2 dp.toNat i + s.1.toNat * base ^ i =
        segVal W xp.toNat i + segVal W yp.toNat (min k.toNat i))
    ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _), by simp, by simp [segVal]⟩ ?_
  intro i s hi ⟨hs, hfr, hdg, hc, hv⟩
  have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hxi : (xp + UInt64.ofNat i).toNat = xp.toNat + i := by rw [toNat_add_lt] <;> omega
  have hdi : (dp + UInt64.ofNat i).toNat = dp.toNat + i := by rw [toNat_add_lt] <;> omega
  have hX := read_kept hfr fun i' hi' => hix i' i hi' hi
  have hXd := hdx i hi
  rw [base_eq] at hXd
  have hc' : s.1.toNat ≤ 1 := hc
  -- the word of `y` read at this step
  obtain ⟨Y, hYt, hYv, hYlt⟩ : ∃ Y : ℕ,
      (if UInt64.ofNat i < k then s.2[(yp + UInt64.ofNat i).toNat]! else 0).toNat = Y ∧
      segVal W yp.toNat (min k.toNat (i + 1)) = segVal W yp.toNat (min k.toNat i) + Y * base ^ i ∧
      Y < 4294967296 := by
    by_cases hik : i < k.toNat
    · have hyi : (yp + UInt64.ofNat i).toNat = yp.toNat + i := by rw [toNat_add_lt] <;> omega
      have hY := read_kept hfr fun i' hi' => hiy i' i hi' (by omega)
      have hYd := hdy i (by omega)
      rw [base_eq] at hYd
      refine ⟨W[yp.toNat + i]!.toNat, ?_, ?_, hYd⟩
      · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hik), hyi, hY]
      · rw [show min k.toNat (i + 1) = min k.toNat i + 1 by omega, segVal_succ,
          show min k.toNat i = i by omega]
    · refine ⟨0, ?_, ?_, by norm_num⟩
      · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hik)]; rfl
      · rw [show min k.toNat (i + 1) = min k.toNat i by omega]; simp
  dsimp only
  rw [hxi, hdi]
  have ht : (s.2[xp.toNat + i]! + (if UInt64.ofNat i < k then
      s.2[(yp + UInt64.ofNat i).toNat]! else 0) + s.1).toNat =
      W[xp.toNat + i]!.toNat + Y + s.1.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hYt, hX]
    omega
  generalize (s.2[xp.toNat + i]! + (if UInt64.ofNat i < k then
      s.2[(yp + UInt64.ofNat i).toNat]! else 0) + s.1) = t at ht
  have hdin : dp.toNat + i < s.2.size := by omega
  have hget := fun q => get_set s.2 (dp.toNat + i) (t &&& 0xFFFFFFFF) q hdin
  refine ⟨by simp [hs], fun q hq => ?_, fun i' hi' => ?_, ?_, ?_⟩
  · rw [hget, if_neg (by omega)]; exact hfr q (by omega)
  · rw [hget]
    split
    · rw [and_mask]; exact Nat.mod_lt _ base_pos
    · exact hdg i' (by omega)
  · rw [shr32, ht, base_eq]; omega
  · have hcongr : segVal (s.2.set! (dp.toNat + i) (t &&& 0xFFFFFFFF)) dp.toNat i =
        segVal s.2 dp.toNat i :=
      segVal_congr fun i' hi' => by rw [hget, if_neg (by omega)]
    rw [segVal_succ, hcongr, hget, if_pos rfl, and_mask, shr32, segVal_succ, hYv, ht, pow_succ]
    have hdm := Nat.mod_add_div (W[xp.toNat + i]!.toNat + Y + s.1.toNat) base
    zify at hv hdm ⊢
    linear_combination hv + (base : ℤ) ^ i * hdm

/-! ## Subtraction in place -/

/-- `subGen` writes over the `n` words from `dp` the difference of the `n` words from `xp` and the
first `min k n` words from `yp`, plus `base ^ n` times the final borrow. -/
theorem subGen_spec (W : Array UInt64) (xp yp k dp n : UInt64) (hW : W.size < 2 ^ 64)
    (hx : xp.toNat + n.toNat ≤ W.size) (hy : yp.toNat + min k.toNat n.toNat ≤ W.size)
    (hd : dp.toNat + n.toNat ≤ W.size)
    (hdx : SegDigits W xp.toNat n.toNat) (hdy : SegDigits W yp.toNat (min k.toNat n.toNat))
    (hix : ∀ i j, i < j → j < n.toNat → dp.toNat + i ≠ xp.toNat + j)
    (hiy : ∀ i j, i < j → j < min k.toNat n.toNat → dp.toNat + i ≠ yp.toNat + j) :
    (subGen W xp yp k dp n).2.size = W.size ∧
    (∀ q, (q < dp.toNat ∨ dp.toNat + n.toNat ≤ q) → (subGen W xp yp k dp n).2[q]! = W[q]!) ∧
    SegDigits (subGen W xp yp k dp n).2 dp.toNat n.toNat ∧ (subGen W xp yp k dp n).1.toNat ≤ 1 ∧
    segVal (subGen W xp yp k dp n).2 dp.toNat n.toNat + segVal W yp.toNat (min k.toNat n.toNat) =
      segVal W xp.toNat n.toNat + (subGen W xp yp k dp n).1.toNat * base ^ n.toNat := by
  unfold subGen
  refine loop_induction (P := fun i (s : UInt64 × Array UInt64) => s.2.size = W.size ∧
      (∀ q, (q < dp.toNat ∨ dp.toNat + i ≤ q) → s.2[q]! = W[q]!) ∧
      SegDigits s.2 dp.toNat i ∧ s.1.toNat ≤ 1 ∧
      segVal s.2 dp.toNat i + segVal W yp.toNat (min k.toNat i) =
        segVal W xp.toNat i + s.1.toNat * base ^ i)
    ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _), by simp, by simp [segVal]⟩ ?_
  intro i s hi ⟨hs, hfr, hdg, hc, hv⟩
  have hii : (UInt64.ofNat i).toNat = i := toNat_ofNat_lt (by omega)
  have hxi : (xp + UInt64.ofNat i).toNat = xp.toNat + i := by rw [toNat_add_lt] <;> omega
  have hdi : (dp + UInt64.ofNat i).toNat = dp.toNat + i := by rw [toNat_add_lt] <;> omega
  have hX := read_kept hfr fun i' hi' => hix i' i hi' hi
  have hXd := hdx i hi
  rw [base_eq] at hXd
  have hc' : s.1.toNat ≤ 1 := hc
  obtain ⟨Y, hYt, hYv, hYlt⟩ : ∃ Y : ℕ,
      (if UInt64.ofNat i < k then s.2[(yp + UInt64.ofNat i).toNat]! else 0).toNat = Y ∧
      segVal W yp.toNat (min k.toNat (i + 1)) = segVal W yp.toNat (min k.toNat i) + Y * base ^ i ∧
      Y < 4294967296 := by
    by_cases hik : i < k.toNat
    · have hyi : (yp + UInt64.ofNat i).toNat = yp.toNat + i := by rw [toNat_add_lt] <;> omega
      have hY := read_kept hfr fun i' hi' => hiy i' i hi' (by omega)
      have hYd := hdy i (by omega)
      rw [base_eq] at hYd
      refine ⟨W[yp.toNat + i]!.toNat, ?_, ?_, hYd⟩
      · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hik), hyi, hY]
      · rw [show min k.toNat (i + 1) = min k.toNat i + 1 by omega, segVal_succ,
          show min k.toNat i = i by omega]
    · refine ⟨0, ?_, ?_, by norm_num⟩
      · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hii]; exact hik)]; rfl
      · rw [show min k.toNat (i + 1) = min k.toNat i by omega]; simp
  dsimp only
  rw [hxi, hdi]
  have ht : (s.2[xp.toNat + i]! + 4294967296 - (if UInt64.ofNat i < k then
      s.2[(yp + UInt64.ofNat i).toNat]! else 0) - s.1).toNat =
      W[xp.toNat + i]!.toNat + 4294967296 - Y - s.1.toNat := by
    have h1 : (s.2[xp.toNat + i]! + 4294967296).toNat = W[xp.toNat + i]!.toNat + 4294967296 := by
      rw [UInt64.toNat_add, hX]; simp only [UInt64.reduceToNat]; omega
    rw [UInt64.toNat_sub_of_le, UInt64.toNat_sub_of_le, h1, hYt]
    · rw [UInt64.le_iff_toNat_le, h1, hYt]; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le, h1, hYt]
      · omega
      · rw [UInt64.le_iff_toNat_le, h1, hYt]; omega
  generalize (s.2[xp.toNat + i]! + 4294967296 - (if UInt64.ofNat i < k then
      s.2[(yp + UInt64.ofNat i).toNat]! else 0) - s.1) = t at ht
  have hdin : dp.toNat + i < s.2.size := by omega
  have hget := fun q => get_set s.2 (dp.toNat + i) (t &&& 0xFFFFFFFF) q hdin
  have hq : t.toNat / base ≤ 1 := by rw [ht, base_eq]; omega
  have hb : ((1 : UInt64) - t >>> 32).toNat = 1 - t.toNat / base := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, shr32]; simpa using hq), shr32]
    rfl
  refine ⟨by simp [hs], fun q hq => ?_, fun i' hi' => ?_, ?_, ?_⟩
  · rw [hget, if_neg (by omega)]; exact hfr q (by omega)
  · rw [hget]
    split
    · rw [and_mask]; exact Nat.mod_lt _ base_pos
    · exact hdg i' (by omega)
  · rw [hb]; exact Nat.sub_le _ _
  · have hcongr : segVal (s.2.set! (dp.toNat + i) (t &&& 0xFFFFFFFF)) dp.toNat i =
        segVal s.2 dp.toNat i :=
      segVal_congr fun i' hi' => by rw [hget, if_neg (by omega)]
    rw [segVal_succ, hcongr, hget, if_pos rfl, and_mask, hb, segVal_succ, hYv, pow_succ]
    have hdm := Nat.mod_add_div t.toNat base
    have ht' : t.toNat + Y + s.1.toNat = W[xp.toNat + i]!.toNat + base := by
      rw [ht, base_eq]; omega
    obtain hq0 | hq1 : t.toNat / base = 0 ∨ t.toNat / base = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp hq
    · rw [hq0] at hdm ⊢
      zify at hv hdm ht' ⊢
      linear_combination hv + (base : ℤ) ^ i * hdm + (base : ℤ) ^ i * ht'
    · rw [hq1] at hdm ⊢
      zify at hv hdm ht' ⊢
      linear_combination hv + (base : ℤ) ^ i * hdm + (base : ℤ) ^ i * ht'

end Library.Numerics.Bignum
