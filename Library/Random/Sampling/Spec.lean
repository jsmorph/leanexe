import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! The specification of a shuffle of words that draws its randomness from an array of words.  A
function `f` shuffles when four properties hold.  First, `f us xs` is Knuth's Algorithm P on `xs`
with the words of `us`, `algorithmP`: for `j` from `n - 1` down to 1 it exchanges the words at `j`
and at `⌊(j + 1)·u / 2^64⌋`, where `u = us[n - 1 - j]` is read as the fraction `U = u / 2^64` of
step P3, so that the steps take the words in order, and a missing word is 0.  The second and fourth
properties state the guarantees that the request asks for, and the third extends the distribution
to inputs with repeated words.  For arrays of fewer than `2^32` words the other three follow from
the first, and their proofs check the index arithmetic of `algorithmP`.  Second, `f us xs` is a
permutation of `xs` for every word array `us`.  Third, the positions that `f` moves do not depend
on the words of `xs`: `f us xs` is `f us (iota n)`, the shuffle of the positions `0, …, n - 1`,
with each position replaced by the word of `xs` there.  Fourth, for an array `xs` of `n` distinct
words and each permutation `ys` of `xs`, the number of word arrays `us` of `n - 1` words with
`f us xs = ys` lies between `fewest n` and `most n`, the products of `⌊2^64 / (j + 1)⌋` and of
`⌈2^64 / (j + 1)⌉` over `j` from 1 to `n - 1`.  When the words of `us` are independent and
uniform, each of the `(2^64)^(n - 1)` arrays has the same probability, so each permutation of
distinct words has a probability within a relative error of about `n(n - 1) / 2^65` of `1 / n!`,
and the third property carries the distribution to inputs with repeated words.  Algorithm P reads
only the first `n - 1` words, so further words do not change the distribution.  The first and
fourth properties concern arrays of fewer than `2^32` words, which includes every array in a
32-bit WebAssembly memory, and the second and third arrays of fewer than `2^64` words. -/

namespace Library.Random.Sampling

/-- `∏ ⌊2^64 / (j + 1)⌋` over `j` from 1 to `n - 1`. -/
def fewest (n : Nat) : Nat :=
  ∏ j ∈ Finset.Ico 1 n, 2 ^ 64 / (j + 1)

/-- `∏ ⌈2^64 / (j + 1)⌉` over `j` from 1 to `n - 1`. -/
def most (n : Nat) : Nat :=
  ∏ j ∈ Finset.Ico 1 n, (2 ^ 64 + j) / (j + 1)

/-- Knuth's Algorithm P with indices from 0 on an array of `n` words, for `j` from `m` down to 1:
the exchange of the words at `j` and at `⌊(j + 1)·us[n - 1 - j] / 2^64⌋`.  The recursion on `j + 1`
performs the exchange at position `j + 1` with the word `us[n - 2 - j]` and the multiplier `j + 2`,
the number of positions to choose from. -/
def algorithmP (us : Array UInt64) (n : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, a => a
  | j + 1, a =>
    algorithmP us n j (a.swapIfInBounds (us[n - 2 - j]!.toNat * (j + 1 + 1) / 2 ^ 64) (j + 1))

/-- The positions `0, …, n - 1` as words. -/
def iota (n : Nat) : Array UInt64 :=
  Array.ofFn fun i : Fin n => UInt64.ofNat i

/-- The word arrays of length `xs.size - 1` for which `f` shuffles `xs` into `ys`. -/
def arraysTo (f : Array UInt64 → Array UInt64 → Array UInt64) (xs ys : Array UInt64) :
    Finset (Fin (xs.size - 1) → UInt64) :=
  Finset.univ.filter fun w => f (Array.ofFn w) xs = ys

/-- `f` shuffles: it computes Algorithm P, its results are permutations, the positions it moves
do not depend on the words, and for fewer than `2^32` distinct words every permutation comes from
between `fewest n` and `most n` word arrays of `n - 1` words. -/
structure Shuffles (f : Array UInt64 → Array UInt64 → Array UInt64) : Prop where
  method : ∀ us xs : Array UInt64, xs.size < 2 ^ 32 →
    f us xs = algorithmP us xs.size (xs.size - 1) xs
  perm : ∀ us xs : Array UInt64, xs.size < 2 ^ 64 → (f us xs).toList.Perm xs.toList
  positions : ∀ us xs : Array UInt64, xs.size < 2 ^ 64 →
    f us xs = (f us (iota xs.size)).map fun p => xs[p.toNat]!
  count : ∀ xs ys : Array UInt64, xs.size < 2 ^ 32 → xs.toList.Nodup →
    ys.toList.Perm xs.toList →
      fewest xs.size ≤ (arraysTo f xs ys).card ∧ (arraysTo f xs ys).card ≤ most xs.size

end Library.Random.Sampling
