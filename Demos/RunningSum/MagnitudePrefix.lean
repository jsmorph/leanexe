import Demos.RunningSum.Magnitude

namespace Demos.RunningSum.Magnitude

def digitWord (digits : Array UInt64) (i : Nat) : UInt64 :=
  if i < digits.size then digits[digits.size - 1 - i]! - 48 else 0

theorem digitWord_nat (digits : Array UInt64) (valid : DecimalDigits digits) (i : Nat) :
    (digitWord digits i).toNat = digit digits i := by
  unfold digitWord digit
  split_ifs with hi
  · have byte := valid (digits.size - 1 - i) (by omega)
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · exact UInt64.le_iff_toNat_le.mpr byte.1
  · rfl

def digitStep (a b : Array UInt64) (subtract : Bool) (state : Array UInt64 × UInt64)
    (i : Nat) : Array UInt64 × UInt64 :=
  let x := digitWord a i
  let y := digitWord b i
  let value := if subtract then 10 + x - y - state.2 else x + y + state.2
  (state.1.push (value % 10), if subtract then (if value < 10 then 1 else 0) else value / 10)

def digitPrefix (a b : Array UInt64) (subtract : Bool) : Nat → Array UInt64 × UInt64
  | 0 => (#[], 0)
  | n + 1 => digitStep a b subtract (digitPrefix a b subtract n) n

@[simp] theorem digitPrefix_size (a b : Array UInt64) (subtract : Bool) (n : Nat) :
    (digitPrefix a b subtract n).1.size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [digitPrefix, digitStep, Array.size_push, ih]

def PrefixInvariant (a b : Array UInt64) (subtract : Bool) (n : Nat)
    (state : Array UInt64 × UInt64) : Prop :=
  state.1.size = n ∧ RawDigits state.1 ∧ state.2.toNat ≤ 1 ∧
    if subtract then
      rawValue state.1 + lowValue b n = lowValue a n + state.2.toNat * 10 ^ n
    else
      rawValue state.1 + state.2.toNat * 10 ^ n = lowValue a n + lowValue b n

theorem digitStep_invariant (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (subtract : Bool) (n : Nat) (state : Array UInt64 × UInt64)
    (invariant : PrefixInvariant a b subtract n state) :
    PrefixInvariant a b subtract (n + 1) (digitStep a b subtract state n) := by
  rcases invariant with ⟨size, valid, carry, value⟩
  have hx := digitWord_nat a ha n
  have hy := digitWord_nat b hb n
  have hxl : (digitWord a n).toNat < 10 := by rw [hx]; exact digit_lt a ha n
  have hyl : (digitWord b n).toNat < 10 := by rw [hy]; exact digit_lt b hb n
  cases subtract with
  | false =>
      obtain ⟨_, hd, hc, he⟩ := add_digit (digitWord a n) (digitWord b n) state.2 hxl hyl carry
      simp only [Bool.false_eq_true, ite_false] at value
      refine ⟨by simp [digitStep, size], rawDigits_push _ _ valid hd, hc, ?_⟩
      simp only [digitStep, Bool.false_eq_true, ite_false, rawValue_push, size, lowValue, pow_succ]
      rw [hx, hy] at he
      have weighted := congrArg (fun value : Nat => value * 10 ^ n) he
      nlinarith only [value, weighted]
  | true =>
      obtain ⟨_, hd, hc, he⟩ := sub_digit (digitWord a n) (digitWord b n) state.2 hxl hyl carry
      simp only [ite_true] at value
      refine ⟨by simp [digitStep, size], rawDigits_push _ _ valid hd, hc, ?_⟩
      simp only [digitStep, ite_true, rawValue_push, size, lowValue, pow_succ]
      rw [hx, hy] at he
      have weighted := congrArg (fun value : Nat => value * 10 ^ n) he
      nlinarith only [value, weighted]

theorem digitPrefix_invariant (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (subtract : Bool) (n : Nat) :
    PrefixInvariant a b subtract n (digitPrefix a b subtract n) := by
  induction n with
  | zero =>
      refine ⟨rfl, ?_, by simp [digitPrefix], ?_⟩
      · intro i hi
        simp [digitPrefix] at hi
      · cases subtract <;> rfl
  | succ n ih => exact digitStep_invariant a b ha hb subtract n _ ih

theorem word_index (size i : Nat) (bound : size < UInt64.size) (index : i < size) :
    (size.toUInt64 - 1 - UInt64.ofNat i).toNat = size - 1 - i := by
  have sizeNat : size.toUInt64.toNat = size := UInt64.toNat_ofNat_of_lt' bound
  have indexNat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by omega)
  have one : (1 : UInt64) ≤ size.toUInt64 := UInt64.le_iff_toNat_le.mpr (by
    rw [sizeNat]
    change 1 ≤ size
    omega)
  have subNat : (size.toUInt64 - 1).toNat = size - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ one, sizeNat]
    rfl
  have less : UInt64.ofNat i ≤ size.toUInt64 - 1 := UInt64.le_iff_toNat_le.mpr (by
    rw [indexNat, subNat]
    omega)
  rw [UInt64.toNat_sub_of_le _ _ less, subNat, indexNat]

theorem digitWord_index (digits : Array UInt64) (bound : digits.size < UInt64.size)
    (i : Nat) (index : i < UInt64.size) :
    (if UInt64.ofNat i < digits.size.toUInt64 then
      digits[(digits.size.toUInt64 - 1 - UInt64.ofNat i).toNat]! - 48 else 0) = digitWord digits i := by
  have sizeNat : digits.size.toUInt64.toNat = digits.size := UInt64.toNat_ofNat_of_lt' bound
  have indexNat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' index
  simp only [UInt64.lt_iff_toNat_lt, sizeNat, indexNat, digitWord]
  split_ifs with hi
  · rw [word_index _ _ bound hi]
  · rfl

theorem digitPrefix_loop (a b : Array UInt64) (subtract : Bool) (count : UInt64)
    (ha : a.size < UInt64.size) (hb : b.size < UInt64.size) :
    (LeanExe.loop count (#[], (0 : UInt64)) fun i state =>
      let x := if i < a.size.toUInt64 then a[(a.size.toUInt64 - 1 - i).toNat]! - 48 else 0
      let y := if i < b.size.toUInt64 then b[(b.size.toUInt64 - 1 - i).toNat]! - 48 else 0
      let value := if subtract then 10 + x - y - state.2 else x + y + state.2
      (state.1.push (value % 10), if subtract then (if value < 10 then 1 else 0) else value / 10)) =
      digitPrefix a b subtract count.toNat := by
  refine LeanExe.Dialect.loop_induction (n := count)
    (fun n state => state = digitPrefix a b subtract n) rfl ?_
  intro n state hn same
  subst state
  rw [digitWord_index a ha n (lt_trans hn count.toNat_lt),
    digitWord_index b hb n (lt_trans hn count.toNat_lt)]
  rfl

end Demos.RunningSum.Magnitude
