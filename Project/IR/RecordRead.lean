import Project.IR.Read
import Project.Pipeline.Implements

/-!
Reads of arrays of records.  An array of a flat type is stored as `flatWords`: each element's
components in order, one word each, so component `j` of element `i` is word `i · k + j` for
elements of `k` components.  The compiler reads that word only when `i < 2^29` and yields 0
otherwise, and it accepts a read only when every component of the element type's default is
0, which is what `xs[i]!` gives out of bounds.
-/

namespace Project.IR

open Project.Pipeline Project.ProofKit

theorem flatMap_getElem? {f : α → List β} {k j : Nat} (hk : ∀ x, (f x).length = k)
    (hj : j < k) : ∀ (xs : List α) (i : Nat),
    (xs.flatMap f)[i * k + j]? = xs[i]?.bind fun x => (f x)[j]?
  | [], _ => by simp
  | x :: xs, 0 => by
    simp [List.getElem?_append_left (show j < (f x).length by rw [hk]; exact hj)]
  | x :: xs, i + 1 => by
    have hi : (i + 1) * k + j = (f x).length + (i * k + j) := by rw [hk, Nat.succ_mul]; omega
    rw [List.flatMap_cons, hi, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      flatMap_getElem? hk hj xs i]
    rfl

theorem flatWords_size [Scalar α] {k : Nat} (hk : ∀ x : α, (Scalar.values x).length = k)
    (xs : Array α) : (flatWords xs).size = xs.size * k := by
  rw [flatWords, List.size_toArray, ← Array.length_toList]
  induction xs.toList with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, hk, ih, Nat.succ_mul, Nat.add_comm]

/-- Word `i · k + j` of an array of records, read when `i < 2^29` and 0 otherwise, is component
`j` of `xs[i]!`. -/
theorem flatWords_read [Scalar α] [Inhabited α] {k j : Nat}
    (hk : ∀ x : α, (Scalar.values x).length = k) (hj : j < k) (hkBound : k < 2 ^ 32)
    (hDefault : (Scalar.values (default : α)).map Value.word = List.replicate k 0)
    {xs : Array α} (hSize : (flatWords xs).size < 536870912) (i : UInt64) :
    (if i < 536870912 then (flatWords xs)[(i * UInt64.ofNat k + UInt64.ofNat j).toNat]!
      else 0) = ((Scalar.values xs[i.toNat]!).map Value.word)[j]! := by
  have hDefaultWord : ((Scalar.values (default : α)).map Value.word)[j]! = 0 := by
    rw [hDefault, getElem!_pos _ _ (by simpa using hj)]; simp
  rw [flatWords_size hk] at hSize
  split
  · rename_i hi
    have hiNat : i.toNat < 536870912 := by simpa [UInt64.lt_iff_toNat_lt] using hi
    have hProduct : i.toNat * k < 536870912 * 2 ^ 32 := Nat.mul_lt_mul'' hiNat hkBound
    have hPosition : (i * UInt64.ofNat k + UInt64.ofNat j).toNat = i.toNat * k + j := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show i.toNat * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hPosition, getElem!_def, flatWords, List.getElem?_toArray,
      flatMap_getElem? (by simp [hk]) hj, Array.getElem?_toList, getElem!_def xs]
    cases xs[i.toNat]? with
    | none => exact hDefaultWord.symm
    | some x => simp [getElem!_def]
  · rename_i hi
    have hOut : xs.size ≤ i.toNat := by
      have : xs.size ≤ xs.size * k := Nat.le_mul_of_pos_right _ (by omega)
      simp [UInt64.lt_iff_toNat_lt] at hi
      omega
    rw [getElem!_neg xs i.toNat (by omega)]
    exact hDefaultWord.symm

/-- An element of an array of a type of one component is the word at its position. -/
theorem flatWords_getElem!_one [Scalar α] [Inhabited α]
    (hk : ∀ x : α, (Scalar.values x).length = 1)
    (hDefault : (Scalar.values (default : α)).map Value.word = [0]) (xs : Array α) (n : Nat) :
    (flatWords xs)[n]! = ((Scalar.values xs[n]!).map Value.word)[0]! := by
  have h := flatMap_getElem? (f := fun x : α => (Scalar.values x).map Value.word) (k := 1)
    (j := 0) (by simp [hk]) (by decide) xs.toList n
  rw [Nat.mul_one, Nat.add_zero] at h
  rw [getElem!_def, flatWords, List.getElem?_toArray, h, Array.getElem?_toList, getElem!_def xs]
  cases xs[n]? with
  | none =>
    show (default : UInt64) = ((Scalar.values (default : α)).map Value.word)[0]!
    rw [hDefault]
    rfl
  | some x => simp [getElem!_def]

/-- The length word of an array of records of `k` components, divided by `k`, is the number of
elements. -/
theorem flatWords_count [Scalar α] {k : Nat} (hk : ∀ x : α, (Scalar.values x).length = k)
    (hkPos : 0 < k) (hkBound : k < 2 ^ 32) (xs : Array α) (hSize : (flatWords xs).size < 2 ^ 64) :
    UInt64.ofNat (flatWords xs).size / UInt64.ofNat k = xs.size.toUInt64 := by
  rw [flatWords_size hk] at hSize ⊢
  have hLe : xs.size ≤ xs.size * k := Nat.le_mul_of_pos_right _ hkPos
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_div, UInt64.toNat_ofNat', Nat.toUInt64_eq]
  rw [Nat.mod_eq_of_lt hSize, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mul_div_cancel _ hkPos,
    Nat.mod_eq_of_lt (by omega)]

/-- Below the guard, the compiled read of word `i · k + j` of an array of records laid out at
`ptr` gives component `j` of `xs[i.toNat]!`. -/
theorem Expr.readValue_record [Scalar α] [Inhabited α] {k j : Nat}
    (hk : ∀ x : α, (Scalar.values x).length = k) (hj : j < k) (hkBound : k < 2 ^ 32)
    (hDefault : (Scalar.values (default : α)).map Value.word = List.replicate k 0)
    {store : Wasm.Store Unit} {ptr : UInt64} {xs : Array α}
    (hArray : UInt64Array.At store ptr (flatWords xs)) {array : Nat} {i : UInt64}
    (hi : i < 536870912) {state : State} (hPtr : state.get array = some (.i64 ptr)) :
    Expr.readValue store.mem array (i * UInt64.ofNat k + UInt64.ofNat j) state =
      some (((Scalar.values xs[i.toNat]!).map Value.word)[j]!, state) := by
  have h := flatWords_read hk hj hkBound hDefault (xs := xs) (by have := hArray.1; omega) i
  simp only [hi, ite_true] at h
  rw [Expr.readValue_at hArray hPtr, h]

end Project.IR
