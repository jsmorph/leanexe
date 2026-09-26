import Project.RunningSum.Digits

namespace Project.RunningSum

def digitWord (bytes : ByteArray) (i : Nat) : UInt64 :=
  if i < bytes.size then bytes[bytes.size - 1 - i]!.toUInt64 - 48 else 0

theorem digitWord_nat (bytes : ByteArray) (h : AsciiDigits bytes) (i : Nat) :
    (digitWord bytes i).toNat = digit bytes i := by
  unfold digitWord digit
  split_ifs with hi
  · have hbyte := h (bytes.size - 1 - i) (by omega)
    rw [UInt64.toNat_sub_of_le]
    · simp
    · exact UInt64.le_iff_toNat_le.mpr (by simpa using hbyte.1)
  · rfl

def digitStep (a b : ByteArray) (subtract : Bool) (state : ByteArray × UInt64)
    (i : Nat) : ByteArray × UInt64 :=
  let x := digitWord a i
  let y := digitWord b i
  let value := if subtract then 10 + x - y - state.2 else x + y + state.2
  (state.1.push (value % 10).toUInt8,
    if subtract then (if value < 10 then 1 else 0) else value / 10)

def digitPrefix (a b : ByteArray) (subtract : Bool) (n : Nat) : ByteArray × UInt64 :=
  (List.range n).foldl (digitStep a b subtract) (ByteArray.empty, 0)

@[simp] theorem digitPrefix_zero (a b : ByteArray) (subtract : Bool) :
    digitPrefix a b subtract 0 = (ByteArray.empty, 0) := rfl

theorem digitPrefix_succ (a b : ByteArray) (subtract : Bool) (n : Nat) :
    digitPrefix a b subtract (n + 1) = digitStep a b subtract
      (digitPrefix a b subtract n) n := by
  simp [digitPrefix, List.range_succ]

def PrefixInvariant (a b : ByteArray) (subtract : Bool) (n : Nat)
    (state : ByteArray × UInt64) : Prop :=
  state.1.size = n ∧ RawDigits state.1 ∧ state.2.toNat ≤ 1 ∧
  if subtract then
    rawValue state.1 + lowValue b n = lowValue a n + state.2.toNat * 10 ^ n
  else
    rawValue state.1 + state.2.toNat * 10 ^ n = lowValue a n + lowValue b n

theorem digitStep_invariant (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (subtract : Bool) (n : Nat) (state : ByteArray × UInt64)
    (h : PrefixInvariant a b subtract n state) :
    PrefixInvariant a b subtract (n + 1) (digitStep a b subtract state n) := by
  rcases h with ⟨hsize, hdigits, hcarry, hvalue⟩
  have hx := digitWord_nat a ha n
  have hy := digitWord_nat b hb n
  have hxl : (digitWord a n).toNat < 10 := by rw [hx]; exact digit_lt a ha n
  have hyl : (digitWord b n).toNat < 10 := by rw [hy]; exact digit_lt b hb n
  cases subtract with
  | false =>
    obtain ⟨hv, hd, hc, he⟩ := add_digit (digitWord a n) (digitWord b n) state.2 hxl hyl hcarry
    simp only [Bool.false_eq_true, ite_false] at hvalue
    refine ⟨by simp [digitStep, hsize], rawDigits_push _ _ hdigits hd, hc, ?_⟩
    simp only [digitStep, Bool.false_eq_true, ite_false, rawValue_push, hsize,
      lowValue, pow_succ]
    rw [hx, hy] at he
    have hew := congrArg (fun value : Nat => value * 10 ^ n) he
    nlinarith only [hvalue, hew]
  | true =>
    obtain ⟨hv, hd, hc, he⟩ := sub_digit (digitWord a n) (digitWord b n) state.2 hxl hyl hcarry
    simp only [ite_true] at hvalue
    refine ⟨by simp [digitStep, hsize], rawDigits_push _ _ hdigits hd, hc, ?_⟩
    simp only [digitStep, ite_true, rawValue_push, hsize, lowValue, pow_succ]
    rw [hx, hy] at he
    have hew := congrArg (fun value : Nat => value * 10 ^ n) he
    nlinarith only [hvalue, hew]

theorem digitPrefix_invariant (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (subtract : Bool) (n : Nat) :
    PrefixInvariant a b subtract n (digitPrefix a b subtract n) := by
  induction n with
  | zero =>
    refine ⟨rfl, ?_, by simp, ?_⟩
    · intro i hi
      simp at hi
    · cases subtract <;> rfl
  | succ n ih =>
    rw [digitPrefix_succ]
    exact digitStep_invariant a b ha hb subtract n _ ih

#print axioms digitPrefix_invariant

end Project.RunningSum
