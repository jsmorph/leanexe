import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorial.Basic

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

/-! ### Selection sampling

The specification of selection sampling, which chooses `k = min n N` of the `N` words of `xs` and
keeps their order.  A function `f` samples when four properties hold.  First, `f us xs n` is Knuth's
Algorithm S, `algorithmS`: with `m` records chosen, it chooses record `t` when
`(N - t)·us[t] < (k - m)·2^64`, that is, exactly when the test `(N - t)U ≥ n - m` of step S3 fails,
with `U = us[t] / 2^64`.  Knuth assumes `0 < n ≤ N`, and `algorithmS` extends his algorithm to
`n = 0`, which chooses nothing, and to `n > N`, which chooses every word.  A missing word is 0,
which chooses the record while fewer than `k` are chosen.  Second, the result is a sublist of `xs`
of `k` words.  Third, the positions that `f` chooses do not depend on the words of `xs`.  Fourth,
for `n ≤ N` and each list of `n` positions in increasing order, the number of word arrays of `N`
words for which `f` chooses those positions lies between `n!(N - n)! ∏ ⌊2^64 / M⌋` and
`n!(N - n)! ∏ ⌈2^64 / M⌉`, the products over `M` from 1 to `N`.  For independent uniform words, each
of the `N! / (n!(N - n)!)` subsets therefore has a probability within a relative error of about
`N(N - 1) / 2^65` of `1 / C(N, n)`.  Algorithm S reads only the first `N` words, so further words do
not change the distribution.  The properties concern arrays of fewer than `2^32` words. -/

/-- The records, from record `t` on, that Algorithm S chooses when `m` of `k` are already chosen
from `N` records. -/
def selectFrom (us : Array UInt64) (N k : Nat) : Nat → Nat → List UInt64 → List UInt64
  | _, _, [] => []
  | t, m, x :: rest =>
    if us[t]!.toNat * (N - t) < (k - m) * 2 ^ 64 then x :: selectFrom us N k (t + 1) (m + 1) rest
    else selectFrom us N k (t + 1) m rest

/-- Knuth's Algorithm S: the `min n N` words of `xs` that it chooses, in order. -/
def algorithmS (us xs : Array UInt64) (n : Nat) : Array UInt64 :=
  (selectFrom us xs.size (min n xs.size) 0 0 xs.toList).toArray

/-- `n!(N - n)! ∏ ⌊2^64 / M⌋` over `M` from 1 to `N`. -/
def fewestS (N n : Nat) : Nat :=
  n.factorial * (N - n).factorial * ∏ M ∈ Finset.Ico 1 (N + 1), 2 ^ 64 / M

/-- `n!(N - n)! ∏ ⌈2^64 / M⌉` over `M` from 1 to `N`. -/
def mostS (N n : Nat) : Nat :=
  n.factorial * (N - n).factorial * ∏ M ∈ Finset.Ico 1 (N + 1), (2 ^ 64 + M - 1) / M

/-- The word arrays of length `xs.size` for which `f` chooses `ys` from `xs`. -/
def samplesTo (f : Array UInt64 → Array UInt64 → UInt64 → Array UInt64) (xs : Array UInt64)
    (n : UInt64) (ys : Array UInt64) : Finset (Fin xs.size → UInt64) :=
  Finset.univ.filter fun w => f (Array.ofFn w) xs n = ys

/-- `f` samples: it computes Algorithm S, its result is a sublist of `min n N` words, the positions
it chooses do not depend on the words, and for `n ≤ N < 2^32` every subset of `n` positions comes
from between `fewestS N n` and `mostS N n` word arrays of `N` words. -/
structure Samples (f : Array UInt64 → Array UInt64 → UInt64 → Array UInt64) : Prop where
  method : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    f us xs n = algorithmS us xs n.toNat
  sublist : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    (f us xs n).toList.Sublist xs.toList ∧ (f us xs n).size = min n.toNat xs.size
  positions : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    f us xs n = (f us (iota xs.size) n).map fun p => xs[p.toNat]!
  count : ∀ (N : Nat) (n : UInt64) (ps : List UInt64), N < 2 ^ 32 → n.toNat ≤ N →
    ps.Sublist (iota N).toList → ps.length = n.toNat →
      fewestS N n.toNat ≤ (samplesTo f (iota N) n ps.toArray).card ∧
        (samplesTo f (iota N) n ps.toArray).card ≤ mostS N n.toNat

/-! ### Reservoir sampling

The specification of reservoir sampling, which keeps `k = min n N` of the `N` words of `xs` as
candidates.  A function `f` keeps a reservoir when four properties hold.  First, `f us xs n` is
Algorithm R with the candidates in an array, `algorithmR`: the first `k` words are the candidates,
and record `t ≥ k` replaces candidate `⌊(t + 1)·us[t - k] / 2^64⌋` when that is below `k`.  Vitter
assumes `n ≤ N`, and `algorithmR` keeps every word when `n > N`.  A missing word is 0, which puts
the record into candidate 0 when `k > 0`.  Second, the result holds `k` of the words of `xs`, as a
sub-multiset.  Third, the positions that `f` keeps do not depend on the words of `xs`.  Fourth, for
`n ≤ N` and each set of `n` positions, given as a list in increasing order, the number of word
arrays of `N - n` words for which `f` keeps those positions, in any order, lies between
`(N - n)! ∏ ⌊2^64 / (t + 1)⌋` and `(N - n)! ∏ ⌈2^64 / (t + 1)⌉`, the products over `t` from `n` to
`N - 1`.  For independent uniform words, each set therefore has a probability within a relative
error of about `(N(N - 1) - n(n - 1)) / 2^65` of `1 / C(N, n)`.  Algorithm R reads only the first
`N - k` words, so further words do not change the distribution.  The order of the candidates depends
on the words, so the property counts sets.  The properties concern arrays of fewer than `2^32`
words. -/

/-- Algorithm R on the records from `t` on, with the candidates `r`, of which there are `k`. -/
def reservoirFrom (us : Array UInt64) (k : Nat) : Nat → List UInt64 → List UInt64 → List UInt64
  | _, r, [] => r
  | t, r, x :: rest =>
    reservoirFrom us k (t + 1) (r.set (us[t - k]!.toNat * (t + 1) / 2 ^ 64) x) rest

/-- Algorithm R with the candidates in an array: the `min n N` candidates at the end. -/
def algorithmR (us xs : Array UInt64) (n : Nat) : Array UInt64 :=
  (reservoirFrom us (min n xs.size) (min n xs.size) (xs.toList.take (min n xs.size))
    (xs.toList.drop (min n xs.size))).toArray

/-- `(N - n)! ∏ ⌊2^64 / (t + 1)⌋` over `t` from `n` to `N - 1`. -/
def fewestR (N n : Nat) : Nat :=
  (N - n).factorial * ∏ t ∈ Finset.Ico n N, 2 ^ 64 / (t + 1)

/-- `(N - n)! ∏ ⌈2^64 / (t + 1)⌉` over `t` from `n` to `N - 1`. -/
def mostR (N n : Nat) : Nat :=
  (N - n).factorial * ∏ t ∈ Finset.Ico n N, (2 ^ 64 + t) / (t + 1)

/-- The word arrays of length `xs.size - min n xs.size` for which `f` keeps the words of `ys`, in
any order. -/
def keepsTo (f : Array UInt64 → Array UInt64 → UInt64 → Array UInt64) (xs : Array UInt64)
    (n : UInt64) (ys : List UInt64) : Finset (Fin (xs.size - min n.toNat xs.size) → UInt64) :=
  Finset.univ.filter fun w => (f (Array.ofFn w) xs n).toList.Perm ys

/-- `f` keeps a reservoir: it computes Algorithm R, it keeps `min n N` of the words, the positions
it keeps do not depend on the words, and for `n ≤ N < 2^32` every set of `n` positions comes from
between `fewestR N n` and `mostR N n` word arrays of `N - n` words. -/
structure Reservoirs (f : Array UInt64 → Array UInt64 → UInt64 → Array UInt64) : Prop where
  method : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    f us xs n = algorithmR us xs n.toNat
  contents : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    (f us xs n).toList.Subperm xs.toList ∧ (f us xs n).size = min n.toNat xs.size
  positions : ∀ us xs : Array UInt64, ∀ n : UInt64, xs.size < 2 ^ 32 →
    f us xs n = (f us (iota xs.size) n).map fun p => xs[p.toNat]!
  count : ∀ (N : Nat) (n : UInt64) (ps : List UInt64), N < 2 ^ 32 → n.toNat ≤ N →
    ps.Sublist (iota N).toList → ps.length = n.toNat →
      fewestR N n.toNat ≤ (keepsTo f (iota N) n ps).card ∧
        (keepsTo f (iota N) n ps).card ≤ mostR N n.toNat

end Library.Random.Sampling
