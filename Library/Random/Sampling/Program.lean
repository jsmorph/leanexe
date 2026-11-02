import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import Library.Sorting.Heapsort.Program

/-! Random shuffling, Algorithm P of TAOCP §3.4.2, on an array of words, in place, with indices
from 0.  The random numbers are words `u` of an array that the caller supplies, read as fractions
`U = u / 2^64` in `[0, 1)`.  For `j` from `n - 1` down to 1, step P3 exchanges the word at `j` with
the word at `k = ⌊(j + 1)U⌋`, a position from 0 to `j`.  The steps read the words in order, as
Knuth's steps generate their numbers: the step for `j` takes `U` from `us[n - 1 - j]`, so a shuffle
of `n` words reads the `n - 1` words `us[0, n - 1)`. -/

namespace Library.Random.Sampling

open Library.Sorting.Heapsort (swap)

/-- `⌊u·m / 2^64⌋` for `m < 2^32`, the index of step P3 with `U = u / 2^64`: the high half of `u`
times `m`, plus the high half of the low half of `u` times `m`, shifted right by 32 bits.  When
`m < 2^32` neither the products nor their sum reaches `2^64`. -/
def scale (u m : UInt64) : UInt64 :=
  ((u >>> 32) * m + (((u &&& 0xFFFFFFFF) * m) >>> 32)) >>> 32

/-- Algorithm P with `n = xs.size`: arrays of 0 and 1 elements return unchanged, and otherwise
step `t` of the loop sets `j = n - 1 - t` and exchanges the words at `j` and at
`scale us[t] (j + 1)`.  A missing word of `us` reads as 0, which selects position 0. -/
def shuffle (us xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  if n ≤ 1 then xs
  else LeanExe.loop (n - 1) xs fun t acc =>
    swap (scale us[t.toNat]! (n - t)) (n - 1 - t) acc

/-- Selection sampling, Algorithm S of TAOCP §3.4.2: the `k = min n N` words of `xs` that it
chooses, in order.  For record `t`, with `m` records chosen, step S3 chooses the record when
`(N - t)U < k - m` with `U = us[t] / 2^64`, which is `scale us[t] (N - t) < k - m`.  The state is
`m` and an array of `k` words: each step writes the record at position `m` and then advances `m`
when it chooses the record, so a record that is not chosen is overwritten by the next one, and a
write at `m = k` is out of range and changes nothing.  The loop reads all `N` words, where Knuth
stops at the `k`-th choice: after it `k - m = 0` and no word chooses. -/
def sample (us xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  let N := xs.size.toUInt64
  let k := if n ≤ N then n else N
  (LeanExe.loop N ((0 : UInt64), LeanExe.build k fun _ => 0) fun t s =>
    (s.1 + (if scale us[t.toNat]! (N - t) < k - s.1 then 1 else 0),
      s.2.set! s.1.toNat xs[t.toNat]!)).2

/-- Reservoir sampling, Algorithm R of TAOCP §3.4.2, with the candidates in an array, as Vitter
states it: the first `k = min n N` words are the candidates, and for each later record `t` the
index `M = ⌊(t + 1)U⌋`, with `U = us[t - k] / 2^64`, is a position from 0 to `t`.  When `M < k`,
the record replaces candidate `M`, and a write at `M ≥ k` is out of range and changes nothing,
which is the test of step R3.  The loop reads the `N - k` words `us[0, N - k)` in order. -/
def reservoir (us xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  let N := xs.size.toUInt64
  let k := if n ≤ N then n else N
  LeanExe.loop (N - k) (LeanExe.build k fun i => xs[i.toNat]!) fun t r =>
    r.set! (scale us[t.toNat]! (k + t + 1)).toNat xs[(k + t).toNat]!

end Library.Random.Sampling
