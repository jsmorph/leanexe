import Library.Sorting.Shellsort.Spec
import TestSupport.Modules.Quicksort
import Library.Random.SplitMix64.Program

/-! The inputs of the verified compiler's cases of Shellsort. -/

namespace Library.Sorting.Shellsort

open TestSupport.Host

/-- The arrays of the verified compiler's cases: the inputs of quicksort, `quicksortInputs`, which
include those of straight insertion and heapsort, and arrays whose lengths bound the increments.
An array of `N` words starts with the increment 4 from `N = 14`, 13 from 41, 40 from 122, 121 from
365, 364 from 1,094, 1,093 from 3,281, and 3,280 from 9,842, so the arrays of these lengths and of
the lengths one below them take each first increment and the one below it.  Each such length up to
3,281 has an array in decreasing order, an array of distinct arbitrary words, and an array that
draws each word from eleven arbitrary words, four to six of them at or above `2^63`, by the
SplitMix64 output of its position.  The lengths 9,841 and 9,842 have an array in decreasing order
and an array that draws every eighth word in the same way and its other words below 100, since an
argument of the host program holds at most 128 KiB.  In these arrays every pass with an increment
above 1 compares equal words and compares words with the high bit set. -/
def shellsortInputs : List (List UInt64) :=
  let draw := fun (k : Nat) => (Library.Random.SplitMix64.splitMix (UInt64.ofNat k)).2.toNat
  let down := fun (n : Nat) => (List.range n).map fun k => UInt64.ofNat (n - k)
  let arbitrary := fun (n : Nat) => (List.range n).map fun k => rw (k + 7 * n)
  let repeated := fun (n : Nat) => (List.range n).map fun k => rw (draw k % 11 + 3 * n)
  let mixed := fun (n : Nat) => (List.range n).map fun k =>
    if k % 8 = 0 then rw (draw k % 11 + 3 * n) else UInt64.ofNat (draw k % 100)
  let bounds := [13, 14, 40, 41, 121, 122, 364, 365, 1093, 1094, 3280, 3281]
  Library.Sorting.Quicksort.quicksortInputs ++
    bounds.flatMap (fun n => [down n, arbitrary n, repeated n]) ++
    [9841, 9842].flatMap fun n => [down n, mixed n]

end Library.Sorting.Shellsort
