import Library.Hashing.Sha2.Spec.Setup
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Common: `Word.fromBits` structural lemmas

`fromBits_foldl_init` (folding from a non-zero accumulator) and
`fromBits_append_same_width` (distribution over `++`).  Stated at
arbitrary `N` so SHA-512 (`N = 64`) reuses them unchanged. -/

namespace SHS.Equiv.FromBits

/-- `Word.fromBits` foldl with an arbitrary initial accumulator. -/
theorem fromBits_foldl_init {N : Nat} (x : BitVec N) (r : List Bool) :
    r.foldl (fun (acc : BitVec N) b => acc <<< 1 ||| (if b then 1 else 0)) x =
      (x <<< r.length) ||| SHS.Word.fromBits (n := N) r := by
  induction r using List.reverseRecOn generalizing x with
  | nil => simp [SHS.Word.fromBits]
  | append_singleton xs y ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
      List.length_nil]
    rw [ih]
    unfold SHS.Word.fromBits
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (0 : BitVec N)]
    rw [show xs.length + (0 + 1) = xs.length + 1 from by omega]
    rw [BitVec.shiftLeft_add x xs.length 1, BitVec.shiftLeft_or_distrib, BitVec.or_assoc]

/-- `Word.fromBits` of an append at the same width. -/
theorem fromBits_append_same_width {N : Nat} (l r : List Bool) :
    SHS.Word.fromBits (n := N) (l ++ r) =
      (SHS.Word.fromBits (n := N) l) <<< r.length ||| SHS.Word.fromBits (n := N) r := by
  show (l ++ r).foldl _ 0 = _
  rw [List.foldl_append, fromBits_foldl_init]; rfl

/-! ## Width-lift

`Word.fromBits` builds an MSB-first packed `BitVec`; as long as the bit
list is short enough to avoid overflow at the narrower width, lifting
to a wider width is a pure `setWidth`.  This lets per-width SHA-2 digest
emission lemmas (`fromBits_4bytes_BE_N` at `N = 256, 224, 512, …`) reduce
to one small-width ground proof plus a `setWidth` specialization. -/

/-- Pure-`Nat` mirror of `Word.fromBits`: foldl `2 * acc + b`.  Matches
`(Word.fromBits N bits).toNat` whenever the bit list fits at width `N`. -/
def natFromBits (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

private theorem natFromBits_foldl_init (init : Nat) (bits : List Bool) :
    bits.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) init =
      init * 2 ^ bits.length + natFromBits bits := by
  induction bits using List.reverseRecOn generalizing init with
  | nil => simp [natFromBits]
  | append_singleton xs y ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih init]
    unfold natFromBits
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih 0]
    simp [List.length_append, pow_succ]
    ring

/-- `natFromBits bits < 2 ^ bits.length`: each bit can only contribute
its positional value, so the packed integer is bounded by `2 ^ length`. -/
theorem natFromBits_lt (bits : List Bool) : natFromBits bits < 2 ^ bits.length := by
  induction bits using List.reverseRecOn with
  | nil => simp [natFromBits]
  | append_singleton xs y ih =>
    unfold natFromBits
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, natFromBits_foldl_init 0 xs]
    simp only [Nat.zero_mul, Nat.zero_add]
    have : (2 : Nat) ^ (xs ++ [y]).length = 2 ^ xs.length * 2 := by
      simp [List.length_append, pow_succ]
    rw [this]
    rcases y with _ | _
    · simp; nlinarith
    · simp; nlinarith

/-- `(Word.fromBits N bits).toNat = natFromBits bits` when `bits.length ≤ N`.
The key identity that turns a `setWidth` between two widths both
exceeding `bits.length` into a no-op on the packed value. -/
theorem fromBits_toNat_of_length_le {N : Nat} (bits : List Bool) (h : bits.length ≤ N) :
    (SHS.Word.fromBits (n := N) bits).toNat = natFromBits bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [SHS.Word.fromBits, natFromBits]
  | append_singleton xs y ih =>
    have hxs : xs.length ≤ N := by simp [List.length_append] at h; omega
    have hxs_lt : natFromBits xs < 2 ^ xs.length := natFromBits_lt xs
    show (SHS.Word.fromBits (n := N) (xs ++ [y])).toNat = _
    rw [fromBits_append_same_width]
    simp only [List.length_singleton]
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, ih hxs]
    -- `fromBits N [y] = 0 <<< 1 ||| (if y then 1 else 0) = if y then 1 else 0`.
    have hN_pos : 0 < N := by simp [List.length_append] at h; omega
    have hy : (SHS.Word.fromBits (n := N) [y]).toNat = (if y then 1 else 0) := by
      simp [SHS.Word.fromBits]
      split
      · rw [BitVec.toNat_one hN_pos]
      · simp
    rw [hy]
    -- The shift at width N doesn't overflow because `xs.length + 1 ≤ N`.
    have hxs_lt_N : xs.length + 1 ≤ N := by simp [List.length_append] at h; omega
    have hshift_lt : natFromBits xs <<< 1 < 2 ^ N := by
      rw [Nat.shiftLeft_eq, pow_one]
      calc natFromBits xs * 2
          < 2 ^ xs.length * 2 := (Nat.mul_lt_mul_right (by omega)).mpr hxs_lt
        _ = 2 ^ (xs.length + 1) := by rw [pow_succ]
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hxs_lt_N
    rw [Nat.mod_eq_of_lt hshift_lt]
    -- Goal: `natFromBits xs <<< 1 ||| (if y then 1 else 0) = natFromBits (xs ++ [y])`.
    have hy_lt : (if y = true then 1 else 0 : Nat) < 2 ^ 1 := by
      rcases y with _ | _ <;> simp
    rw [← Nat.shiftLeft_add_eq_or_of_lt hy_lt]
    -- RHS unfold via the foldl-init helper.
    show natFromBits xs <<< 1 + _ = _
    unfold natFromBits
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, natFromBits_foldl_init 0 xs]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.shiftLeft_eq, pow_one]
    omega

/-- `Word.fromBits` width-lift: between any two widths both `≥ bits.length`,
`setWidth` from the narrower form is exactly the wider form.  Consumed by
every SHA-2 digest-emission lemma: prove the ground identity once at a
small width (32 for SHA-256 family / 64 for SHA-512 family), then peel
off the target width via `setWidth_eq_lift`. -/
theorem fromBits_setWidth_eq {M N : Nat} (bits : List Bool)
    (hM : bits.length ≤ M) (hN : bits.length ≤ N) :
    (SHS.Word.fromBits (n := M) bits).setWidth N =
      SHS.Word.fromBits (n := N) bits := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, fromBits_toNat_of_length_le bits hM,
      fromBits_toNat_of_length_le bits hN]
  exact Nat.mod_eq_of_lt
    (lt_of_lt_of_le (natFromBits_lt bits) (Nat.pow_le_pow_right (by omega) hN))

/-! ## `leftmost` lift

`fromBits` packs bits MSB-first; the leftmost `N` bits of the wider
packing are exactly `fromBits` of the first `N` bits of the list.
Consumed by SHA-512/224 digest emission, where the spec's
`.leftmost 224` of a 256-bit packing crosses a word boundary. -/

private theorem natFromBits_split (l r : List Bool) :
    natFromBits (l ++ r) = natFromBits l * 2 ^ r.length + natFromBits r := by
  unfold natFromBits
  rw [List.foldl_append, natFromBits_foldl_init]
  rfl

/-- `leftmost N` of `fromBits M bits` (with `bits.length = M`, `N ≤ M`)
equals `fromBits N` of the first `N` bits.  The remaining bits become the
low part (LSB side) of the BitVec and are discarded by `leftmost`. -/
theorem fromBits_leftmost {M N : Nat} (bits : List Bool)
    (hLen : bits.length = M) (hN : N ≤ M) :
    (SHS.Word.fromBits (n := M) bits).leftmost N =
      SHS.Word.fromBits (n := N) (bits.take N) := by
  apply BitVec.eq_of_toNat_eq
  -- LHS reduces to `(natFromBits bits) >>> (M - N) % 2 ^ N`.
  rw [BitVec.leftmost, BitVec.extractLsb'_toNat,
      fromBits_toNat_of_length_le bits (by rw [hLen])]
  -- RHS to `natFromBits (bits.take N)`.
  have hTake_len : (bits.take N).length ≤ N := by
    rw [List.length_take]; omega
  rw [fromBits_toNat_of_length_le _ hTake_len]
  -- Split bits = take N ++ drop N, apply natFromBits_split, simplify shifts.
  have hSplit : bits = bits.take N ++ bits.drop N := (List.take_append_drop N bits).symm
  conv_lhs => rw [hSplit, natFromBits_split]
  have hDropLen : (bits.drop N).length = M - N := by
    rw [List.length_drop, hLen]
  rw [hDropLen]
  have hDropLt : natFromBits (bits.drop N) < 2 ^ (M - N) := by
    have := natFromBits_lt (bits.drop N)
    rwa [hDropLen] at this
  rw [Nat.shiftRight_eq_div_pow]
  have hAdd : (natFromBits (bits.take N) * 2 ^ (M - N) + natFromBits (bits.drop N))
      / 2 ^ (M - N) = natFromBits (bits.take N) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ (M - N))]
    rw [Nat.div_eq_of_lt hDropLt]
    ring
  rw [hAdd]
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_le (natFromBits_lt _) (Nat.pow_le_pow_right (by omega) hTake_len)

end SHS.Equiv.FromBits
