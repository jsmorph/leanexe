/-! Words as sets of states.  Bit `q` of a word, counted from the least significant, says whether
state `q` is in the set, so a word holds a set of states below 64.  The lemmas give the bits of
the operations that the matcher applies to its sets. -/

namespace Library.Regex.Bits

/-- Whether state `q` is in the set held by `s`. -/
def bit (s : UInt64) (q : Nat) : Bool := s.toNat.testBit q

theorem bit_or (a b : UInt64) (q : Nat) : bit (a ||| b) q = (bit a q || bit b q) := by
  simp [bit, UInt64.toNat_or, Nat.testBit_or]

theorem bit_and (a b : UInt64) (q : Nat) : bit (a &&& b) q = (bit a q && bit b q) := by
  simp [bit, UInt64.toNat_and, Nat.testBit_and]

theorem bit_zero (q : Nat) : bit 0 q = false := by
  simp [bit]

theorem bit_lt {s : UInt64} {q : Nat} (h : bit s q = true) : q < 64 := by
  rcases Nat.lt_or_ge q 64 with hq | hq
  · exact hq
  · have hlt : s.toNat < 2 ^ q :=
      Nat.lt_of_lt_of_le (UInt64.toNat_lt s) (Nat.pow_le_pow_right (by decide) hq)
    simp [bit, Nat.testBit_lt_two_pow hlt] at h

theorem bit_one_shiftLeft {p : UInt64} (hp : p.toNat < 64) (q : Nat) :
    bit ((1 : UInt64) <<< p) q = (q == p.toNat) := by
  have hm : p.toNat % 64 = p.toNat := Nat.mod_eq_of_lt hp
  simp only [bit, UInt64.toNat_shiftLeft, hm, UInt64.toNat_one, Nat.testBit_mod_two_pow,
    Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : q = p.toNat
  · subst h; simp [hp]
  · have : ¬ p.toNat = q := fun h' => h h'.symm
    simp [h, this]

/-- The test that the matcher writes for membership of state `q`. -/
theorem shiftRight_and_one {s q : UInt64} (hq : q.toNat < 64) :
    ((s >>> q) &&& 1 == 1) = bit s q.toNat := by
  have hm : q.toNat % 64 = q.toNat := Nat.mod_eq_of_lt hq
  have key : ((s >>> q) &&& 1).toNat = (s.toNat >>> q.toNat) % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hm, UInt64.toNat_one, Nat.and_one_is_mod]
  have hb : bit s q.toNat = ((s.toNat >>> q.toNat) % 2 != 0) := by
    simp only [bit, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (s.toNat >>> q.toNat) with h | h
  · have : (s >>> q) &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [key, h]; rfl)
    rw [this, hb, h]; decide
  · have : (s >>> q) &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [key, h]; rfl)
    rw [this, hb, h]; decide

/-- Two words with the same bits are equal. -/
theorem ext {a b : UInt64} (h : ∀ q, bit a q = bit b q) : a = b :=
  UInt64.toNat_inj.mp (Nat.eq_of_testBit_eq h)

#print axioms shiftRight_and_one
#print axioms bit_one_shiftLeft
#print axioms bit_lt

end Library.Regex.Bits
