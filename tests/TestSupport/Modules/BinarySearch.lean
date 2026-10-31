import Library.Arrays.BinarySearch.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of binary search: sorted arrays with keys below,
at, between, and above their elements. -/

namespace Library.Arrays.BinarySearch

open TestSupport.Host

/-- The words of `xs` in nondecreasing order. -/
def sortWords (xs : List UInt64) : List UInt64 := xs.mergeSort fun a b => a ≤ b

/-- The arguments of the verified compiler's cases.  Each short sorted array is searched for 0,
`2^64 - 1`, each element, and each element plus and minus one.  The short arrays have 0 to 34
elements, among them repeated elements, the words 0 and `2^64 - 1`, and the words `2^63 - 1` and
`2^63` on either side of the sign bit.  Each long array, of 200 to 1,000 elements and with long runs
of equal words in some, is searched for 0, `2^64 - 1`, and every 37th element and its neighbors. -/
def searchInputs : List (List UInt64 × UInt64) :=
  let half : UInt64 := 9223372036854775808
  let short : List (List UInt64) :=
    [[], [0], [5], [maxU], [3, 9], [half - 1, half], [half, half, half + 1], [1, 2, 3],
      [2, 2, 2, 3, 3, 7], [0, 0, maxU, maxU], [7, 7, 7, 7, 7]] ++
      (List.range 12).map fun i => sortWords ((List.range (3 * i + 1)).map fun k => rw (31 * i + k))
  let long : List (List UInt64) :=
    [List.replicate 100 7 ++ List.replicate 100 9,
      List.replicate 300 half ++ List.replicate 1 maxU,
      [0] ++ List.replicate 498 5 ++ [maxU],
      sortWords ((List.range 1000).map fun k => rw (7 * k + 3)),
      sortWords ((List.range 777).map fun k => rw (k % 50))]
  let around (xs : List UInt64) (x : UInt64) : List (List UInt64 × UInt64) :=
    [x - 1, x, x + 1].map fun key => (xs, key)
  (short.flatMap fun xs => ([0, maxU] ++ xs.flatMap fun x => [x - 1, x, x + 1]).map fun key =>
    (xs, key)) ++
    long.flatMap fun xs =>
      [(xs, 0), (xs, maxU)] ++ ((List.range xs.length).filter (· % 37 = 0)).flatMap fun k =>
        around xs (xs.getD k 0)

end Library.Arrays.BinarySearch
