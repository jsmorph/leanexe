import Batteries.Data.List.Basic
import Mathlib.Data.List.Range

/-! # Common: `List.toChunks` lemmas

Facts about `List.toChunks` sufficient to expose a chunked list as a
`range`-driven `drop+take` slice.  Used to align the spec's bit-level
chunked parse with byte-aligned slicing.

## Why this file exists

The spec's preprocessing produces a `List Bool` (the bit message) and
parses it via `List.toChunks 32` into 32-bit words; the implementation
slices the same data byte-by-byte (`ByteArray.extract`) into 4-byte
groups.  Both produce the same per-chunk content, but the spec uses
`toChunks`'s built-in `Array`-accumulator definition while the
implementation uses pure `drop+take`.  `toChunks_eq_drop_take`
(below) bridges the two views, and `toChunks_go_spec` is the
case-split engine that unrolls `List.toChunks.go`'s
accumulator-threaded recursion into a purely positional
characterisation. -/

namespace SHS.Equiv.Chunks

/-- Spec for the inner `toChunks.go`: short-tail vs full-chunk dichotomy. -/
theorem toChunks_go_spec {α} (n : Nat) (hn : 0 < n) :
    ∀ (xs : List α) (acc₁ : Array α) (acc₂ : Array (List α)),
      acc₁.size ≤ n →
      List.toChunks.go n xs acc₁ acc₂ =
        if acc₁.size + xs.length < n then
          (acc₂.push (acc₁.toList ++ xs)).toList
        else
          acc₂.toList ++ ((acc₁.toList ++ xs.take (n - acc₁.size))
            :: (xs.drop (n - acc₁.size)).toChunks n) := by
  intro xs
  induction xs with
  | nil =>
    intro acc₁ acc₂ hSize
    show (acc₂.push acc₁.toList).toList = _
    simp only [List.length_nil, Nat.add_zero, List.take_nil, List.drop_nil,
      List.append_nil]
    by_cases h : acc₁.size < n
    · rw [if_pos h]
    · rw [if_neg h]
      have : acc₁.size = n := by omega
      simp [List.toChunks, Array.toList_push]
  | cons y ys ih =>
    intro acc₁ acc₂ hSize
    show (if (acc₁.size == n)
            then List.toChunks.go n ys ((Array.mkEmpty n).push y) (acc₂.push acc₁.toList)
            else List.toChunks.go n ys (acc₁.push y) acc₂) = _
    by_cases hAcc : acc₁.size = n
    · -- Branch A: `acc₁` is already full; `go` flushes it and starts a new chunk with `y`.
      rw [show (acc₁.size == n) = true from by simp [hAcc]]
      simp only [if_true]
      have hSize' : ((Array.mkEmpty n).push y).size ≤ n := by
        rw [Array.mkEmpty_eq, Array.size_push, Array.size_empty]; omega
      rw [ih _ _ hSize']
      simp only [Array.mkEmpty_eq, Array.size_push,
        Array.toList_push, List.nil_append]
      have hRhsCond : ¬ (acc₁.size + (y :: ys).length < n) := by
        rw [hAcc]; simp [List.length_cons]
      rw [if_neg hRhsCond]
      rw [hAcc, Nat.sub_self]
      simp only [List.take_zero, List.drop_zero, List.append_nil]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hToChunks : (y :: ys).toChunks (n' + 1) =
          List.toChunks.go (n' + 1) ys #[y] #[] := by rfl
      rw [hToChunks]
      have hSize2 : (#[y] : Array α).size ≤ n' + 1 := by
        simp
      rw [ih _ _ hSize2]
      simp only [Array.toList_push, List.nil_append,
        show (#[y] : Array α).size = 1 from rfl,
        show (#[] : Array α).size + 1 = 1 from rfl]
      by_cases h1 : 1 + ys.length < n' + 1
      · rw [if_pos h1, if_pos h1]
        simp [List.append_assoc]
      · rw [if_neg h1, if_neg h1]
        simp [List.append_assoc]
    · -- Branch B: `acc₁` not yet full; push `y` and recurse.
      simp only [show (acc₁.size == n) = false from by simp [hAcc]]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hSize' : (acc₁.push y).size ≤ n := by simp; omega
      rw [ih _ _ hSize']
      simp only [Array.size_push, Array.toList_push]
      by_cases hShort : acc₁.size + 1 + ys.length < n
      · rw [if_pos hShort]
        have hRhs : acc₁.size + (y :: ys).length < n := by
          simp [List.length_cons]; omega
        rw [if_pos hRhs]
        simp [List.append_assoc]
      · have hLhsCond : ¬ acc₁.size + 1 + ys.length < n := by omega
        rw [if_neg hLhsCond]
        have hRhsCond : ¬ acc₁.size + (y :: ys).length < n := by
          simp [List.length_cons]; omega
        rw [if_neg hRhsCond]
        -- Peel one element off the take/drop by shifting `n - acc₁.size` by 1.
        have hSub : n - acc₁.size = (n - acc₁.size - 1) + 1 := by omega
        have hSubEq : n - acc₁.size - 1 = n - (acc₁.size + 1) := by omega
        rw [hSub]
        simp only [List.take_succ_cons, List.drop_succ_cons]
        rw [hSubEq]
        simp [List.append_assoc]

/-- Single-step unfold of `List.toChunks` for length ≥ n. -/
theorem toChunks_cons_step {α} (n : Nat) (hn : 0 < n) (L : List α)
    (hLen : n ≤ L.length) :
    L.toChunks n = (L.take n) :: (L.drop n).toChunks n := by
  rcases L with _ | ⟨x, xs⟩
  · simp at hLen; omega
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show List.toChunks.go (n' + 1) xs #[x] #[] = _
    have hSize : (#[x] : Array α).size ≤ n' + 1 := by
      simp
    rw [toChunks_go_spec (n' + 1) (by omega) xs #[x] #[] hSize]
    simp only [Array.toList_push, List.nil_append,
      show (#[x] : Array α).size = 1 from rfl]
    have hLen' : ¬ 1 + xs.length < n' + 1 := by simp at hLen; omega
    rw [if_neg hLen']
    simp [List.take_succ_cons, List.drop_succ_cons]

/-- `toChunks` of an exact-multiple-length list: the chunks are the
`drop+take` slices. -/
theorem toChunks_eq_drop_take {α} (n : Nat) (hn : 0 < n) (L : List α)
    (k : Nat) (hLen : L.length = n * k) :
    L.toChunks n = (List.range k).map (fun i => (L.drop (i*n)).take n) := by
  induction k generalizing L with
  | zero =>
    have h0 : L.length = 0 := by simpa using hLen
    have : L = [] := List.length_eq_zero_iff.mp h0
    subst this
    rfl
  | succ k ih =>
    have hLen' : n ≤ L.length := by rw [hLen, Nat.mul_succ]; omega
    rw [toChunks_cons_step n hn L hLen']
    have hDrop : (L.drop n).length = n * k := by
      rw [List.length_drop, hLen, Nat.mul_succ]; omega
    rw [ih (L.drop n) hDrop]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    · simp
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [show (i + 1) * n = n + i * n from by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    rw [← List.drop_drop]

end SHS.Equiv.Chunks
