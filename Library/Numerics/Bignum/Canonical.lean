module

public import Library.Numerics.Bignum.Spec
public import Library.Numerics.Bignum.Program
public import Library.Numerics.MultiPrecision.DivideProof

@[expose] public section

/-!
The canonical form of a natural.  `value u` is Mathlib's `Nat.ofDigits` in base `2^32` of the
limbs of `u` (`value_eq_ofDigits`), so `Nat.ofDigits_digits` gives `value (limbsOf n) = n`, and
`Nat.digits_ofDigits`, whose premises are the two conditions of `Canonical`, gives
`u = limbsOf (value u)` for a canonical `u` (`canonical_iff`).  An array of limbs therefore equals
`limbsOf n` exactly when it is canonical and has the value `n` (`eq_limbsOf`), which is how every
function's theorem is proved.  `natTrim_eq` states that `natTrim` gives the canonical form of the
value of any array of limbs.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision
open LeanExe.Dialect

theorem one_lt_base : 1 < base := by rw [base_eq]; decide

theorem base_lt_word : base < 2 ^ 64 := by rw [base_eq]; decide

theorem valL_eq_ofDigits (l : List UInt64) :
    Library.Numerics.Arithmetic.Uscale.UscaleTheorem.valL l =
      Nat.ofDigits base (l.map UInt64.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [Library.Numerics.Arithmetic.Uscale.UscaleTheorem.valL, List.map_cons,
      Nat.ofDigits_cons, ih, base]

/-- The value of an array of limbs is `Nat.ofDigits` of its limbs in base `2^32`. -/
theorem value_eq_ofDigits (u : Array UInt64) :
    value u = Nat.ofDigits base (u.toList.map UInt64.toNat) := by
  rw [value_eq_val, Library.Numerics.Arithmetic.Uscale.UscaleTheorem.val, valL_eq_ofDigits]

theorem toList_limbsOf (n : ℕ) : (limbsOf n).toList = (Nat.digits base n).map UInt64.ofNat := by
  simp [limbsOf]

theorem toNat_ofNat_digit {n d : ℕ} (h : d ∈ Nat.digits base n) : (UInt64.ofNat d).toNat = d :=
  UInt64.toNat_ofNat_of_lt' (lt_trans (Nat.digits_lt_base one_lt_base h) base_lt_word)

theorem map_toNat_limbsOf (n : ℕ) :
    (limbsOf n).toList.map UInt64.toNat = Nat.digits base n := by
  rw [toList_limbsOf, List.map_map]
  conv_rhs => rw [← List.map_id (Nat.digits base n)]
  exact List.map_congr_left fun d hd => toNat_ofNat_digit hd

theorem value_limbsOf (n : ℕ) : value (limbsOf n) = n := by
  rw [value_eq_ofDigits, map_toNat_limbsOf, Nat.ofDigits_digits]

theorem size_limbsOf (n : ℕ) : (limbsOf n).size = (Nat.digits base n).length := by
  simp [limbsOf]

theorem limbsOf_zero : limbsOf 0 = #[] := by simp [limbsOf]

theorem size_limbsOf_eq_zero (n : ℕ) : (limbsOf n).size = 0 ↔ n = 0 := by
  rw [size_limbsOf, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]

theorem canonical_limbsOf (n : ℕ) : Canonical (limbsOf n) := by
  have hl := map_toNat_limbsOf n
  refine ⟨fun i hi => ?_, fun h => ?_⟩
  · rw [getElem!_pos (limbsOf n) i hi]
    have hmem : (limbsOf n)[i].toNat ∈ Nat.digits base n := by
      rw [← hl]
      exact List.mem_map.mpr ⟨_, Array.getElem_mem_toList hi, rfl⟩
    exact Nat.digits_lt_base one_lt_base hmem
  · have hn : n ≠ 0 := fun h0 => by
      rw [h0, limbsOf_zero] at h
      exact absurd h (by simp)
    intro h0
    have hlast := Nat.getLast_digit_ne_zero base hn
    have hne : Nat.digits base n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
    have hget : ((limbsOf n).toList.map UInt64.toNat).getLast (by simpa [← hl] using hne) =
        (limbsOf n)[(limbsOf n).size - 1].toNat := by
      rw [List.getLast_map, List.getLast_eq_getElem]
      simp
    apply hlast
    have : (Nat.digits base n).getLast hne = (limbsOf n)[(limbsOf n).size - 1].toNat := by
      rw [← hget]
      congr 1
      exact hl.symm
    rw [this, h0]
    rfl

/-- A canonical array is the canonical form of its value. -/
theorem canonical_iff (u : Array UInt64) : Canonical u ↔ u = limbsOf (value u) := by
  constructor
  · intro ⟨hd, htop⟩
    set L := u.toList.map UInt64.toNat with hL
    have hlt : ∀ l ∈ L, l < base := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := hd i (by simpa using hi)
      rwa [getElem!_pos u i (by simpa using hi), ← Array.getElem_toList] at this
    have hlast : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
      intro h h0
      have hs : 0 < u.size := by
        rcases Nat.eq_zero_or_pos u.size with h' | h'
        · exact absurd (by simp [hL, Array.eq_empty_of_size_eq_zero h']) h
        · exact h'
      apply htop hs
      have : L.getLast h = u[u.size - 1].toNat := by
        simp only [hL, List.getLast_eq_getElem, List.getElem_map, Array.getElem_toList,
          List.length_map, Array.length_toList]
      rw [this] at h0
      exact UInt64.toNat_inj.mp (by rw [h0]; rfl)
    have hdig := Nat.digits_ofDigits base one_lt_base L hlt hlast
    apply Array.toList_inj.mp
    rw [toList_limbsOf, value_eq_ofDigits, ← hL, hdig, hL, List.map_map]
    conv_lhs => rw [← List.map_id u.toList]
    exact List.map_congr_left fun x _ => by simp
  · intro h
    rw [h]
    exact canonical_limbsOf _

/-- A canonical array with the value `n` is `limbsOf n`; `canonical_limbsOf` and `value_limbsOf`
give the converse. -/
theorem eq_limbsOf {u : Array UInt64} {n : ℕ} (hc : Canonical u) (hv : value u = n) :
    u = limbsOf n := by
  rw [← hv]
  exact (canonical_iff u).mp hc

theorem digits_of_canonical {u : Array UInt64} (h : Canonical u) : Digits u := h.1

/-- A canonical array is empty exactly when its value is 0. -/
theorem value_eq_zero_iff {u : Array UInt64} (hu : Canonical u) : value u = 0 ↔ u.size = 0 := by
  conv_rhs => rw [(canonical_iff u).mp hu]
  rw [size_limbsOf_eq_zero]

/-! ### Values of `digits` -/

theorem prefixValue_digits (N x : ℕ) {q : ℕ} (hq : q ≤ N) :
    prefixValue (digits N x) q = x % base ^ q := by
  induction q with
  | zero => simp [prefixValue_zero, Nat.mod_one]
  | succ q ih =>
    rw [prefixValue_succ, ih (by omega), digits_get (by omega),
      UInt64.toNat_ofNat_of_lt' (lt_trans (Nat.mod_lt _ base_pos) base_lt_word), Nat.mod_pow_succ]
    ring

theorem value_digits (N x : ℕ) : value (digits N x) = x % base ^ N := by
  unfold value
  rw [digits_size]
  exact prefixValue_digits N x le_rfl

theorem digits_digits (N x : ℕ) : Digits (digits N x) := by
  intro i hi
  rw [digits_size] at hi
  rw [digits_get hi, UInt64.toNat_ofNat_of_lt' (lt_trans (Nat.mod_lt _ base_pos) base_lt_word)]
  exact Nat.mod_lt _ base_pos

/-! ### Trimming -/

theorem size_toNat64 {u : Array UInt64} (h : u.size < 2 ^ 64) : u.size.toUInt64.toNat = u.size :=
  size_toNat h

theorem natTrim_size (w : Array UInt64) : (natTrim w).size = (significant w).toNat := by
  rw [natTrim, build_size]

theorem natTrim_get (w : Array UInt64) {i : ℕ} (hi : i < (significant w).toNat) :
    (natTrim w)[i]! = w[i]! := by
  rw [natTrim, build_get hi, UInt64.toNat_ofNat_of_lt' (by
    have := (significant w).toNat_lt; simp only [UInt64.size] at this ⊢; omega)]

/-- `natTrim` gives the canonical form of the value of any array of limbs. -/
theorem natTrim_eq {w : Array UInt64} (hw : Digits w) (hs : w.size < 2 ^ 64) :
    natTrim w = limbsOf (value w) := by
  obtain ⟨hts, hz, htop⟩ := significant_spec w hs
  apply eq_limbsOf
  · refine ⟨fun i hi => ?_, fun h => ?_⟩
    · rw [natTrim_size] at hi
      rw [natTrim_get w hi]
      exact digit_all hw i
    · rw [natTrim_size] at h
      have := htop h
      rw [← natTrim_get w (by omega), getElem!_pos (natTrim w) _ (by rw [natTrim_size]; omega)]
        at this
      simpa [natTrim_size] using this
  · unfold value
    rw [natTrim_size, prefixValue_congr fun p hp => natTrim_get w hp]
    exact (prefixValue_zero_tail hts fun i hi _ => hz i hi).symm

/-- `natTrim` of a canonical array is the array. -/
theorem natTrim_canonical {u : Array UInt64} (hu : Canonical u) (hs : u.size < 2 ^ 64) :
    natTrim u = u := by
  rw [natTrim_eq hu.1 hs, ← (canonical_iff u).mp hu]

/-- The canonical form of a number held in `N` digits. -/
theorem natTrim_digits {N x : ℕ} (hN : N < 2 ^ 64) (hx : x < base ^ N) :
    natTrim (digits N x) = limbsOf x := by
  rw [natTrim_eq (digits_digits N x) (by rw [digits_size]; exact hN), value_digits,
    Nat.mod_eq_of_lt hx]

/-! ### Integers -/

theorem toInt_ofInt (z : ℤ) : (BigInt.ofInt z).toInt = z := by
  unfold BigInt.toInt BigInt.ofInt
  simp only [value_limbsOf, decide_eq_true_eq]
  split <;> omega

theorem canonical_ofInt (z : ℤ) : (BigInt.ofInt z).Canonical := by
  unfold BigInt.Canonical
  rw [toInt_ofInt]

theorem ofInt_mag_canonical (z : ℤ) : Canonical (BigInt.ofInt z).mag := canonical_limbsOf _

/-- A canonical integer has a canonical magnitude and is negative only when the magnitude is not
empty. -/
theorem BigInt.canonical_iff (x : BigInt) :
    x.Canonical ↔ Bignum.Canonical x.mag ∧ (x.neg = true → x.mag.size ≠ 0) := by
  obtain ⟨neg, mag⟩ := x
  constructor
  · intro h
    have hc : Bignum.Canonical mag := by
      have := congrArg BigInt.mag h
      simp only [BigInt.ofInt] at this
      rw [this]
      exact canonical_limbsOf _
    refine ⟨hc, fun hn h0 => ?_⟩
    have hv : value mag = 0 := (value_eq_zero_iff hc).mpr h0
    have := congrArg BigInt.neg h
    simp only at hn
    simp only [BigInt.ofInt, BigInt.toInt, hn, hv] at this
    simp at this
  · intro ⟨hc, hn⟩
    unfold BigInt.Canonical BigInt.ofInt BigInt.toInt
    simp only [BigInt.mk.injEq]
    cases neg with
    | true =>
      have hpos : 0 < value mag := by
        rcases Nat.eq_zero_or_pos (value mag) with h | h
        · exact absurd ((value_eq_zero_iff hc).mp h) (hn rfl)
        · exact h
      refine ⟨by simp; omega, ?_⟩
      rw [ite_eq_left rfl, Int.natAbs_neg, Int.natAbs_natCast]
      exact (Bignum.canonical_iff mag).mp hc
    | false =>
      refine ⟨by simp, ?_⟩
      rw [ite_eq_right (by decide), Int.natAbs_natCast]
      exact (Bignum.canonical_iff mag).mp hc

theorem BigInt.eq_ofInt {x : BigInt} (h : x.Canonical) : x = .ofInt x.toInt := h

end Library.Numerics.Bignum
