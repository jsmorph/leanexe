import Library.Lists.Word.Compiled
import LeanExe.Dialect.Lemmas
import Verified.Master

namespace Library.Lists.Word

open LeanExe.Dialect LeanExe.Pipeline

theorem listSum_export :
    ({ name := "listSum", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem range_export :
    ({ name := "range", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sum_export :
    ({ name := "sum", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem reverse_export :
    ({ name := "reverse", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem increment_export :
    ({ name := "increment", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem foldl_add (xs : List UInt64) (a : UInt64) : xs.foldl (· + ·) a = a + xs.sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, UInt64.add_assoc]

/-- `listSum xs` is the sum of `xs` modulo `2 ^ 64`. -/
theorem listSum_eq (xs : List UInt64) : listSum xs = xs.sum := by
  rw [listSum, foldl_add, UInt64.zero_add]

/-- `range n` is the list of the words `0` to `n - 1` in ascending order. -/
theorem range_eq (n : UInt64) : range n = (List.range n.toNat).map UInt64.ofNat := by
  have hl := loop_induction (n := n) (init := ([] : List UInt64))
    (f := fun i xs => (n - 1 - i) :: xs)
    (fun m acc => acc = (List.range' (n.toNat - m) m).map UInt64.ofNat) (by simp)
    fun m acc hm hacc => by
      have hsub : n - 1 - UInt64.ofNat m = UInt64.ofNat (n.toNat - (m + 1)) := by
        rw [show n.toNat - (m + 1) = n.toNat - 1 - m by omega]
        conv_lhs => rw [← UInt64.ofNat_toNat (x := n)]
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl,
          ← UInt64.ofNat_sub (show 1 ≤ n.toNat by omega),
          ← UInt64.ofNat_sub (show m ≤ n.toNat - 1 by omega)]
      rw [hacc, hsub, List.range'_succ, show n.toNat - (m + 1) + 1 = n.toNat - m by omega,
        List.map_cons]
  rw [Nat.sub_self, ← List.range_eq_range'] at hl
  exact hl

/-- `sum xs acc` is `acc` plus the sum of `xs` modulo `2 ^ 64`. -/
theorem sum_eq (xs : List UInt64) (acc : UInt64) : sum xs acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp [sum]
  | cons x xs ih => simp [sum, ih, UInt64.add_assoc]

/-- `reverse xs acc` is the reverse of `xs` followed by `acc`. -/
theorem reverse_eq (xs acc : List UInt64) : reverse xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [reverse]
  | cons x xs ih => simp [reverse, ih]

/-- `increment xs` adds 1 to each element of `xs` modulo `2 ^ 64`. -/
theorem increment_eq (xs : List UInt64) : increment xs = xs.map (· + 1) := by
  induction xs with
  | nil => simp [increment]
  | cons x xs ih => simp [increment, ih]

/-- The frames condition of `increment` holds with `k` frames exactly when the list has fewer than
`k` elements. -/
theorem increment_fits : ∀ (k : Nat) (xs : List UInt64),
    compiled.increment.fits k { val := xs } = true ↔ xs.length < k
  | 0, xs => by simp [show compiled.increment.fits 0 { val := xs } = false from rfl]
  | k + 1, xs => by
    rw [compiled.increment.fits_eq]
    cases xs with
    | nil => simp
    | cons y ys => simp [increment_fits k ys]

/-- The export `listSum`, called on a list of words, returns its sum modulo `2 ^ 64`. -/
theorem listSum_master :
    Verified.Master compiled.module compiled.tables "listSum" compiled.listSum.bound
      (fun _ => True) (fun (xs : List UInt64) y => y = xs.sum) :=
  .of_trapFree (.ofA compiled.listSum.trapFree) nofun listSum_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs _ _ => listSum_eq xs

#print axioms listSum_master

/-- The export `range`, called on a word `n`, returns the list of the words `0` to `n - 1` in
ascending order. -/
theorem range_master :
    Verified.Master compiled.module compiled.tables "range" compiled.range.bound (fun _ => True)
      (fun (n : UInt64) ys => ys = (List.range n.toNat).map UInt64.ofNat) :=
  .of_trapFree (.ofA compiled.range.trapFree) nofun range_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ n _ _ => range_eq n

#print axioms range_master

/-- The export `sum`, called on a list of words and a word `acc`, returns `acc` plus the sum of
the list modulo `2 ^ 64`. -/
theorem sum_master :
    Verified.Master compiled.module compiled.tables "sum" compiled.sum.bound (fun _ => True)
      (fun (x : List UInt64 × UInt64) y => y = x.2 + x.1.sum) :=
  .of_trapFree (.ofA compiled.sum.trapFree) nofun sum_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => sum_eq x.1 x.2

#print axioms sum_master

/-- The export `reverse`, called on two lists of words that the caller moves, returns the reverse
of the first followed by the second. -/
theorem reverse_master :
    Verified.Master compiled.module compiled.tables "reverse" compiled.reverse.bound
      (fun _ => True)
      (fun (x : Moved (List UInt64) × Moved (List UInt64)) ys =>
        ys = x.1.val.reverse ++ x.2.val) :=
  .of_trapFree (.ofA compiled.reverse.trapFree) nofun reverse_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => reverse_eq x.1.val x.2.val

#print axioms reverse_master

/-- The export `increment`, called on a list of fewer than 1,000 words that the caller moves,
returns the list with 1 added to each element modulo `2 ^ 64`. -/
theorem increment_master :
    Verified.Master compiled.module compiled.tables "increment" (compiled.increment.bound 1000)
      (fun (xs : Moved (List UInt64)) => xs.val.length < 1000)
      (fun xs (ys : List UInt64) => ys = xs.val.map (· + 1)) :=
  .of_trapFree (.ofA compiled.increment.trapFree) nofun increment_export
    (fun xs _ _ hD h => ⟨(increment_fits 1000 xs.val).mpr hD, h⟩) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs _ _ => increment_eq xs.val

#print axioms increment_master

end Library.Lists.Word
