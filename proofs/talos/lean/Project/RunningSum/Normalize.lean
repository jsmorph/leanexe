import Project.RunningSum.Prefix
import Init.Internal.Order.While

namespace Project.RunningSum

def rawPrefix (bytes : ByteArray) : Nat → Nat
  | 0 => 0
  | n + 1 => rawPrefix bytes n + bytes[n]!.toNat * 10 ^ n

theorem rawPrefix_eq (bytes : ByteArray) (n : Nat) (hn : n ≤ bytes.size) :
    rawPrefix bytes n = Nat.ofDigits 10 ((bytes.data.toList.take n).map UInt8.toNat) := by
  induction n with
  | zero => simp [rawPrefix]
  | succ n ih =>
    rw [rawPrefix, ih (by omega)]
    rw [List.take_succ_eq_append_getElem (by simpa using (show n < bytes.size by omega))]
    simp [List.map_append, Nat.ofDigits_append, Nat.ofDigits, Nat.min_eq_left (by omega : n ≤ bytes.size),
      getElem!_pos bytes n (by omega), ByteArray.getElem_eq_getElem_data, mul_comm]

theorem rawPrefix_size (bytes : ByteArray) : rawPrefix bytes bytes.size = rawValue bytes := by
  rw [rawPrefix_eq bytes bytes.size (by omega)]
  simp only [rawValue, List.map_take]
  rw [List.take_of_length_le (by simp)]

def trimSize (bytes : ByteArray) (initial : Nat) : Nat := Id.run do
  let mut size := initial
  while size > 0 && bytes[size - 1]! == 0 do
    size := size - 1
  return size

theorem trimSize_eq (bytes : ByteArray) (size : Nat) :
    trimSize bytes size =
      if size > 0 && bytes[size - 1]! == 0 then trimSize bytes (size - 1) else size := by
  unfold trimSize
  simp only [bind_pure, Id.run]
  conv_lhs => rw [show (forIn (m := Id) (Lean.Loop.mk) size _) = _ from Lean.Loop.forIn_eq_of_monadTail]
  split_ifs <;> rfl

theorem trimSize_spec (bytes : ByteArray) (size : Nat) :
    trimSize bytes size ≤ size ∧
    rawPrefix bytes (trimSize bytes size) = rawPrefix bytes size ∧
    (trimSize bytes size = 0 ∨ bytes[trimSize bytes size - 1]! ≠ 0) := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
    rw [trimSize_eq]
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨hle, hvalue, hlast⟩ := ih (size - 1) (by omega)
      refine ⟨by omega, ?_, hlast⟩
      rw [hvalue]
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
      have hb : bytes[n]! = 0 := by simpa using h.2
      simp [rawPrefix, hb]
    · refine ⟨by omega, rfl, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at h
      by_cases hs : size = 0
      · exact Or.inl hs
      · exact Or.inr (h (by omega))

def reverseAscii (bytes : ByteArray) (size : Nat) : ByteArray :=
  (List.range size).foldl (fun result i => result.push (bytes[size - 1 - i]! + 48)) ByteArray.empty

def finishDigits (bytes : ByteArray) : ByteArray := reverseAscii bytes (trimSize bytes bytes.size)

theorem finishDigits_eq (bytes : ByteArray) :
    (Id.run do
      let mut size := bytes.size
      while size > 0 && bytes[size - 1]! == 0 do
        size := size - 1
      let mut digits := ByteArray.empty
      for i in [:size] do
        digits := digits.push (bytes[size - 1 - i]! + 48)
      return digits) = finishDigits bytes := by
  simp only [finishDigits, reverseAscii, trimSize,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure, Id.run]
  rfl

theorem combineMagnitude_eq (a b : ByteArray) (subtract : Bool) :
    LeanExe.Examples.RunningSum.combineMagnitude a b subtract =
      let state := digitPrefix a b subtract (max a.size b.size)
      finishDigits (if !subtract && state.2 != 0 then state.1.push state.2.toUInt8 else state.1) := by
  conv_lhs =>
    simp only [LeanExe.Examples.RunningSum.combineMagnitude,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure, Id.run]
  let state := digitPrefix a b subtract (max a.size b.size)
  change (if !subtract && state.2 != 0 then finishDigits (state.1.push state.2.toUInt8)
    else finishDigits state.1) = finishDigits _
  exact (apply_ite finishDigits _ _ _).symm

#print axioms trimSize_spec
#print axioms combineMagnitude_eq

end Project.RunningSum
