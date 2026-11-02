import LeanExe.Dialect.Loop
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

end Library.Random.Sampling
