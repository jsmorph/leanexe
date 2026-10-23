import Batteries.Data.ByteArray

/-! # Common: `ByteArray.get!` lemmas

`ByteArray.get!` distribution over `++`, `push`, and `appendZeros`.
The matching `getElem` lemmas exist in core / Batteries; we restate
at `get!` for proofs that operate on padded bytes by index. -/

namespace SHS.Equiv.ByteArray

/-- Append `n` zero bytes to a `ByteArray`. -/
def appendZeros (bs : ByteArray) (n : Nat) : ByteArray :=
  Nat.rec bs (motive := fun _ => ByteArray) (fun _ acc => acc.push 0) n

@[simp] theorem size_appendZeros (bs : ByteArray) (n : Nat) :
    (appendZeros bs n).size = bs.size + n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ((appendZeros bs k).push 0).size = bs.size + (k + 1)
    rw [ByteArray.size_push, ih]; omega

/-- `get!` agrees with `getElem` whenever the index is in range. -/
theorem get!_eq_getElem (a : ByteArray) (n : Nat) (h : n < a.size) :
    a.get! n = a[n]'h := by
  unfold ByteArray.get!
  simp
  rw [getElem!_pos]
  rfl

/-- Index into the left summand of a `ByteArray.append`. -/
theorem get!_append_left (a b : ByteArray) (n : Nat) (h : n < a.size) :
    (a ++ b).get! n = a.get! n := by
  rw [get!_eq_getElem _ _ h,
      get!_eq_getElem _ _ (by rw [ByteArray.size_append]; omega)]
  exact ByteArray.get_append_left h

/-- Index into the right summand of a `ByteArray.append`. -/
theorem get!_append_right (a b : ByteArray) (n : Nat)
    (hle : a.size ≤ n) (h : n - a.size < b.size) :
    (a ++ b).get! n = b.get! (n - a.size) := by
  rw [get!_eq_getElem _ _ (by rw [ByteArray.size_append]; omega),
      get!_eq_getElem _ _ h]
  exact ByteArray.get_append_right hle (by rw [ByteArray.size_append]; omega)

/-- Index below the size of `a` is unaffected by `push`. -/
theorem get!_push_lt (a : ByteArray) (b : UInt8) (n : Nat) (h : n < a.size) :
    (a.push b).get! n = a.get! n := by
  rw [get!_eq_getElem _ _ (by rw [ByteArray.size_push]; omega),
      get!_eq_getElem _ _ h]
  exact ByteArray.get_push_lt a b n h

/-- The newly pushed byte is found at the old size. -/
theorem get!_push_eq (a : ByteArray) (b : UInt8) :
    (a.push b).get! a.size = b := by
  rw [get!_eq_getElem _ _ (by rw [ByteArray.size_push]; omega)]
  exact ByteArray.get_push_eq a b

/-- Indexing inside the original prefix of `appendZeros` is unaffected. -/
theorem get!_appendZeros_lt (bs : ByteArray) (n i : Nat) (h : i < bs.size) :
    (appendZeros bs n).get! i = bs.get! i := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ((appendZeros bs k).push 0).get! i = bs.get! i
    have hsz : i < (appendZeros bs k).size := by
      rw [size_appendZeros]; omega
    rw [get!_push_lt _ _ _ hsz, ih]

/-- Indexing into the appended-zeros suffix returns `0`. -/
theorem get!_appendZeros_ge (bs : ByteArray) (n i : Nat)
    (h1 : bs.size ≤ i) (h2 : i < bs.size + n) :
    (appendZeros bs n).get! i = 0 := by
  induction n with
  | zero => omega
  | succ k ih =>
    show ((appendZeros bs k).push 0).get! i = 0
    by_cases hk : i < bs.size + k
    · have hsz : i < (appendZeros bs k).size := by
        rw [size_appendZeros]; omega
      rw [get!_push_lt _ _ _ hsz]
      exact ih hk
    · have heq : i = (appendZeros bs k).size := by
        rw [size_appendZeros]; omega
      rw [heq, get!_push_eq]

/-- The underlying `Array`'s list length equals the `ByteArray`'s size. -/
theorem data_toList_length (bs : ByteArray) :
    bs.data.toList.length = bs.size := by
  rw [Array.length_toList]
  rfl

/-- `bs.get! n`, for in-range `n`, equals the underlying list's `n`-th element. -/
theorem get!_eq_toList_getElem (bs : ByteArray) (n : Nat)
    (h : n < bs.size) :
    bs.get! n = bs.data.toList[n]'(by
      rw [data_toList_length bs]; exact h) := by
  rw [get!_eq_getElem _ _ h, ByteArray.getElem_eq_getElem_data]
  exact (Array.getElem_toList h).symm

end SHS.Equiv.ByteArray
