/-!
The word forms of Lean's `Int64` operations and their equations.  An `Int64` is the word
`x.toUInt64`, its two's-complement bits, and the reflector writes each `Int64` operation as an
expression over words.  `+`, `-`, `*`, `&&&`, `|||`, `^^^`, and `<<<` are the word operations, and
negation is `0 - a`.  `sar` shifts right arithmetically through the logical shift, between two
copies of the sign mask.  `div` and `rem` follow `BitVec.sdiv_eq` and `BitVec.srem_eq`: the
unsigned quotient or remainder of the magnitudes, with the sign of the result fixed afterwards, so
a zero divisor gives Lean's 0 and dividend through the unsigned operations, and `minValue / -1`
gives `minValue`.  The order comparisons add `M = 2 ^ 63` to both words, which maps
`[-2 ^ 63, 2 ^ 63)` onto `[0, 2 ^ 64)` in order.  The last section states the equations in the
forms that the reflector takes: a word term equal to the `Int64` term, and the `decide`, `if`,
`==`, and `!=` of a word comparison equal to those of the `Int64` comparison.
-/

namespace LeanExe.ProofKit.Signed64

/-- The word of the sign bit, `2 ^ 63`. -/
abbrev M : UInt64 := 0x8000000000000000

/-- The sign bit of a word, as `>>> 63` computes it. -/
theorem shr63 (w : UInt64) : w >>> 63 = if w.toBitVec.msb then 1 else 0 := by
  have hlt := w.toNat_lt
  have h : w.toBitVec.toNat = w.toNat := rfl
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight]
  split
  · rename_i hm
    have := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
    simp only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
    omega
  · rename_i hm
    have := BitVec.msb_eq_false_iff_two_mul_lt.mp (by simpa using hm)
    simp only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
    omega

/-- Lean's shift amount `b.smod 64` is the low 6 bits of `b`, as `b % 64` is. -/
theorem smod_toNat (b : BitVec 64) : (b.smod 64).toNat = b.toNat % 64 := by
  have hm : BitVec.msb (64 : BitVec 64) = false := by decide
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have hlt := b.isLt
  rw [BitVec.toNat_smod, hm]
  cases hb : b.msb
  · simp only [BitVec.umod_eq, BitVec.toNat_umod, h64]
  · have hge := BitVec.msb_eq_true_iff_two_mul_ge.mp hb
    simp only [BitVec.umod_eq, BitVec.toNat_eq, BitVec.toNat_umod, BitVec.toNat_neg,
      BitVec.toNat_sub, h64, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    split <;> omega

/-- Arithmetic shift right through the logical one, between two copies of the sign mask `s`, 0
or all ones. -/
@[inline] def sar (a k : UInt64) : UInt64 :=
  let s := (0 : UInt64) - (a >>> 63)
  ((a ^^^ s) >>> k) ^^^ s

theorem toBitVec_sar (x k : UInt64) :
    (sar x k).toBitVec = x.toBitVec.sshiftRight (k.toNat % 64) := by
  have hk : (k.toBitVec % 64).toNat = k.toNat % 64 := rfl
  unfold sar
  rw [shr63 x]
  cases hx : x.toBitVec.msb
  · rw [BitVec.sshiftRight_eq_of_msb_false hx]
    simp only [Bool.false_eq_true, ite_false, UInt64.sub_self, UInt64.xor_zero,
      UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', hk]
  · rw [BitVec.sshiftRight_eq_of_msb_true hx]
    have hs : ((0 : UInt64) - 1).toBitVec = BitVec.allOnes 64 := by decide
    simp only [ite_true, UInt64.toBitVec_xor, UInt64.toBitVec_shiftRight, hs,
      BitVec.xor_allOnes, BitVec.ushiftRight_eq', hk]

theorem sar_eq (a b : Int64) : (a >>> b).toUInt64 = sar a.toUInt64 b.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  rw [toBitVec_sar]
  show BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64) = _
  rw [BitVec.sshiftRight_eq', smod_toNat]
  rfl

theorem shl_eq (a b : Int64) : (a <<< b).toUInt64 = a.toUInt64 <<< b.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  show a.toBitVec <<< (b.toBitVec.smod 64) = a.toUInt64.toBitVec <<< (b.toUInt64.toBitVec % 64)
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq', smod_toNat]
  rfl

/-- `BitVec.sdiv_eq` on words: the unsigned quotient of the magnitudes, negated when the signs
differ. -/
@[inline] def div (a b : UInt64) : UInt64 :=
  let q := (if a >>> 63 == 0 then a else 0 - a) / (if b >>> 63 == 0 then b else 0 - b)
  if a >>> 63 == b >>> 63 then q else 0 - q

theorem toBitVec_div (x y : UInt64) : (div x y).toBitVec = x.toBitVec.sdiv y.toBitVec := by
  rw [BitVec.sdiv_eq]
  unfold div
  rw [shr63 x, shr63 y]
  cases hx : x.toBitVec.msb <;> cases hy : y.toBitVec.msb <;>
    simp [UInt64.toBitVec_div, BitVec.udiv_eq]

theorem div_eq (a b : Int64) : (a / b).toUInt64 = div a.toUInt64 b.toUInt64 :=
  UInt64.toBitVec_inj.mp (toBitVec_div a.toUInt64 b.toUInt64).symm

/-- `BitVec.srem_eq` on words: the unsigned remainder of the magnitudes, with the dividend's
sign. -/
@[inline] def rem (a b : UInt64) : UInt64 :=
  let r := (if a >>> 63 == 0 then a else 0 - a) % (if b >>> 63 == 0 then b else 0 - b)
  if a >>> 63 == 0 then r else 0 - r

theorem toBitVec_rem (x y : UInt64) : (rem x y).toBitVec = x.toBitVec.srem y.toBitVec := by
  rw [BitVec.srem_eq]
  unfold rem
  rw [shr63 x, shr63 y]
  cases hx : x.toBitVec.msb <;> cases hy : y.toBitVec.msb <;>
    simp [UInt64.toBitVec_mod]

theorem rem_eq (a b : Int64) : (a % b).toUInt64 = rem a.toUInt64 b.toUInt64 :=
  UInt64.toBitVec_inj.mp (toBitVec_rem a.toUInt64 b.toUInt64).symm

theorem neg_eq (a : Int64) : (-a).toUInt64 = 0 - a.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  simp

/-- The integer of an `Int64` from its word. -/
theorem toInt_cond (a : Int64) :
    a.toInt = if a.toUInt64.toNat < 2 ^ 63 then (a.toUInt64.toNat : Int)
      else (a.toUInt64.toNat : Int) - 2 ^ 64 := by
  show a.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  have h : a.toBitVec.toNat = a.toUInt64.toNat := rfl
  rw [h]
  split <;> split <;> omega

theorem lt_iff (a b : Int64) : a < b ↔ a.toUInt64 + M < b.toUInt64 + M := by
  rw [Int64.lt_iff_toInt_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add,
    toInt_cond, toInt_cond]
  have ha := a.toUInt64.toNat_lt
  have hb := b.toUInt64.toNat_lt
  have hM : M.toNat = 9223372036854775808 := rfl
  rw [hM]
  split <;> split <;> omega

theorem le_iff (a b : Int64) : a ≤ b ↔ a.toUInt64 + M ≤ b.toUInt64 + M := by
  rw [Int64.le_iff_toInt_le, UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_add,
    toInt_cond, toInt_cond]
  have ha := a.toUInt64.toNat_lt
  have hb := b.toUInt64.toNat_lt
  have hM : M.toNat = 9223372036854775808 := rfl
  rw [hM]
  split <;> split <;> omega

theorem eq_iff (a b : Int64) : a = b ↔ a.toUInt64 = b.toUInt64 :=
  ⟨congrArg Int64.toUInt64, fun h => by cases a; cases b; cases h; rfl⟩

/-! ## The reflector's forms

Each equation states a term over words on the left and the `Int64` term that the reflector
reflects through it on the right. -/

theorem add_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 + b.toUInt64) = a + b := rfl
theorem sub_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 - b.toUInt64) = a - b := rfl
theorem mul_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 * b.toUInt64) = a * b := rfl
theorem and_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 &&& b.toUInt64) = a &&& b := rfl
theorem or_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 ||| b.toUInt64) = a ||| b := rfl
theorem xor_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 ^^^ b.toUInt64) = a ^^^ b := rfl

theorem shl_word (a b : Int64) : Int64.ofUInt64 (a.toUInt64 <<< b.toUInt64) = a <<< b :=
  congrArg Int64.ofUInt64 (shl_eq a b).symm

theorem sar_word (a b : Int64) : Int64.ofUInt64 (sar a.toUInt64 b.toUInt64) = a >>> b :=
  congrArg Int64.ofUInt64 (sar_eq a b).symm

theorem div_word (a b : Int64) : Int64.ofUInt64 (div a.toUInt64 b.toUInt64) = a / b :=
  congrArg Int64.ofUInt64 (div_eq a b).symm

theorem rem_word (a b : Int64) : Int64.ofUInt64 (rem a.toUInt64 b.toUInt64) = a % b :=
  congrArg Int64.ofUInt64 (rem_eq a b).symm

theorem neg_word (a : Int64) : Int64.ofUInt64 (0 - a.toUInt64) = -a :=
  congrArg Int64.ofUInt64 (neg_eq a).symm

/-- The decision of a proposition through an equivalent one, for any instances. -/
theorem decide_iff {p q : Prop} [Decidable p] (h : p ↔ q) (inst : Decidable q) :
    decide p = @decide q inst :=
  (@decide_eq_decide p q _ inst).mpr h

/-- An `if` through an equivalent condition, for any instances. -/
theorem ite_iff {α : Type} {p q : Prop} [Decidable p] (h : p ↔ q) (inst : Decidable q)
    (x y : α) : (if p then x else y) = @ite α q inst x y := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

theorem beq_word (a b : Int64) : (a.toUInt64 == b.toUInt64) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_iff]

theorem bne_word (a b : Int64) : (a.toUInt64 != b.toUInt64) = (a != b) := by
  rw [bne, bne, beq_word]

end LeanExe.ProofKit.Signed64
