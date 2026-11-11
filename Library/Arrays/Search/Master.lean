import Library.Arrays.Search.Compiled
import Library.Arrays.Search.Proof
import LeanExe.Dialect.ArrayLemmas
import Verified.Master

namespace Library.Arrays.Search

open LeanExe.Dialect

theorem count_export :
    ({ name := "count", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem firstAbove_export :
    ({ name := "firstAbove", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem firstZero_export :
    ({ name := "firstZero", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `count xs key` is the number of elements of `xs` equal to `key`, as a word, for an array of
fewer than `2 ^ 64` elements. -/
theorem count_eq (xs : Array UInt64) (key : UInt64) (h : xs.size < 2 ^ 64) :
    count xs key = UInt64.ofNat (xs.toList.count key) := by
  have hn := size_toUInt64 xs h
  have hl := loop_induction (n := xs.size.toUInt64) (init := (0 : UInt64))
    (f := fun i acc => if xs[i.toNat]! == key then acc + 1 else acc)
    (fun m acc => acc = UInt64.ofNat ((xs.toList.take m).count key)) (by simp)
    fun m acc hm hacc => by
      rw [hn] at hm
      have hk : (UInt64.ofNat m).toNat = m := UInt64.toNat_ofNat_of_lt' (show m < 2 ^ 64 by omega)
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hm), List.count_append,
        hacc, hk, getElem!_pos xs m hm]
      by_cases he : xs[m] = key <;> simp [he]
  rw [hn, List.take_of_length_le (by simp)] at hl
  exact hl

/-- `firstAbove xs limit` is the index of the first element of `xs` above `limit` with `true`,
or `(0, false)` when no element is above `limit`, for an array of fewer than `2 ^ 64`
elements. -/
theorem firstAbove_eq (xs : Array UInt64) (limit : UInt64) (h : xs.size < 2 ^ 64) :
    firstAbove xs limit = match xs.toList.findIdx? (fun a => limit < a) with
      | some i => (UInt64.ofNat i, true)
      | none => (0, false) := by
  have hn := size_toUInt64 xs h
  have hl := loop_induction (n := xs.size.toUInt64) (init := ((0 : UInt64), false))
    (f := fun i (found, seen) =>
      if seen then (found, seen) else if limit < xs[i.toNat]! then (i, true) else (found, seen))
    (fun m s => s = match (xs.toList.take m).findIdx? (fun a => limit < a) with
      | some i => (UInt64.ofNat i, true)
      | none => (0, false)) (by simp)
    fun m s hm hs => by
      rw [hn] at hm
      have hk : (UInt64.ofNat m).toNat = m := UInt64.toNat_ofNat_of_lt' (show m < 2 ^ 64 by omega)
      have hlen : (xs.toList.take m).length = m := by simp; omega
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hm), List.findIdx?_append]
      cases ho : (xs.toList.take m).findIdx? (fun a => limit < a) with
      | some i => simp only [ho] at hs; subst hs; simp
      | none =>
        simp only [ho] at hs; subst hs
        rw [hk, getElem!_pos xs m hm, hlen]
        by_cases hlt : limit < xs[m] <;> simp [hlt]
  rw [hn, List.take_of_length_le (by simp)] at hl
  exact hl

/-- The export `count`, called on an array of words and a key, returns the number of elements
equal to the key. -/
theorem count_master :
    Verified.Master compiled.module compiled.tables "count" compiled.count.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64) y => y = UInt64.ofNat (x.1.toList.count x.2)) :=
  .of_trapFree (.ofA compiled.count.trapFree) nofun count_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => count_eq x.1 x.2 hxs.values.size_lt

#print axioms count_master

/-- The export `firstAbove`, called on an array of words and a limit, returns the index of the
first element above the limit with `true`, or `(0, false)` when no element is above it. -/
theorem firstAbove_master :
    Verified.Master compiled.module compiled.tables "firstAbove" compiled.firstAbove.bound
      (fun _ => True)
      (fun (x : Array UInt64 × UInt64) y => y = match x.1.toList.findIdx? (fun a => x.2 < a) with
        | some i => (UInt64.ofNat i, true)
        | none => (0, false)) :=
  .of_trapFree (.ofA compiled.firstAbove.trapFree) nofun firstAbove_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => firstAbove_eq x.1 x.2 hxs.values.size_lt

#print axioms firstAbove_master

/-- The export `firstZero`, called on an array `xs` of words and a count `c`, returns the least
`j < c` with `xs[j]! = 0`, or `c` when there is none, where a read past the end of the array
gives 0. -/
theorem firstZero_master :
    Verified.Master compiled.module compiled.tables "firstZero" compiled.firstZero.bound
      (fun _ => True)
      (fun (x : Array UInt64 × UInt64) y =>
        (y = x.2 ∧ ∀ j < x.2.toNat, x.1[j]! ≠ 0) ∨
          ∃ j < x.2.toNat, y = UInt64.ofNat j ∧ x.1[j]! = 0 ∧ ∀ i < j, x.1[i]! ≠ 0) :=
  .of_trapFree (.ofA compiled.firstZero.trapFree) nofun firstZero_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => firstZero_cases x.1 x.2

#print axioms firstZero_master

end Library.Arrays.Search
