import Library.Sorting.Heapsort.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of heapsort. -/

namespace Library.Sorting.Heapsort

open TestSupport.Host

/-- The arrays of the verified compiler's cases: the empty array, `[5]`, two elements in both
orders, eight elements sorted and reversed, `[7, 7, 7, 7, 7]`, `[3, 1, 3, 1, 3, 1, 2]`, an array of
the words 0, `2^63 - 1`, `2^63`, and `2^64 - 1`, the array `[2^64 - 1, 2^64 - 2, 1, 0]`, and
arbitrary words of every length from 1 to 40.  The long arrays are 100
arbitrary words, 255 words of 7 values, 256 words in decreasing order, 1,000 words of about 300
values, 300 words in increasing order, 300 copies of one word, and 300 words that are 0 or
`2^64 - 1`. -/
def sortInputs : List (List UInt64) :=
  let half : UInt64 := 9223372036854775808
  let chosen : List (List UInt64) :=
    [[], [5], [1, 2], [2, 1], [1, 2, 3, 4, 5, 6, 7, 8], [8, 7, 6, 5, 4, 3, 2, 1], [7, 7, 7, 7, 7],
      [0, maxU, half, half - 1, 0, maxU], [maxU, maxU - 1, 1, 0], [3, 1, 3, 1, 3, 1, 2]]
  let arbitrary := (List.range 40).map fun i => (List.range (i + 1)).map fun k => rw (41 * i + k)
  let long : List (List UInt64) :=
    [(List.range 100).map fun k => rw (k + 5000),
      (List.range 255).map fun k => rw k % 7,
      (List.range 256).map fun k => UInt64.ofNat (256 - k),
      (List.range 1000).map fun k => rw (k + 9000) % 1000,
      (List.range 300).map fun k => UInt64.ofNat (3 * k + 1),
      List.replicate 300 (rw 77),
      (List.range 300).map fun k => if rw (k + 300) % 3 = 0 then 0 else maxU]
  chosen ++ arbitrary ++ long

end Library.Sorting.Heapsort
