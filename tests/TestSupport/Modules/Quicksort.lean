import Library.Sorting.Quicksort.Spec
import TestSupport.Modules.StraightInsertion

/-! The inputs of the verified compiler's cases of quicksort. -/

namespace Library.Sorting.Quicksort

open TestSupport.Host

/-- The arrays of the verified compiler's cases: the inputs of straight insertion,
`insertionInputs`, which include those of heapsort, and arrays that drive the partitions of steps Q2
to Q7.  Arrays of 10 words, the shortest that the steps partition, and of 11 words, the shortest
whose partition leaves a part that they partition again, appear in increasing and decreasing order.
A first word above every other word runs the scan of step Q3 to the end of the subfile, where
Knuth's sentinel would stop it, and a first word below every other word runs the scan of step Q4
down to the first word, at lengths 10, 21, and 500.  The long arrays it adds are 2,000 arbitrary
words, 2,000 words of 3 values, 2,000 words in organ-pipe order, increasing and then decreasing,
2,000 words in increasing and in decreasing order, which partition into an empty part and the rest
at every stage, 3,000 copies of one word, and 10,000 words below 100,000, whose array takes more
than one 64 KiB page of memory and whose decimal form stays within Linux's limit of 128 KiB on one
command-line argument of the host. -/
def quicksortInputs : List (List UInt64) :=
  let up := fun (n : Nat) => (List.range n).map UInt64.ofNat
  let down := fun (n : Nat) => (List.range n).map fun k => UInt64.ofNat (n - k)
  let high := fun (n : Nat) => maxU :: (List.range (n - 1)).map fun k => rw k / 2
  let low := fun (n : Nat) => 0 :: (List.range (n - 1)).map fun k => rw k / 2 + 1
  let chosen : List (List UInt64) :=
    [up 10, down 10, up 11, down 11] ++ [10, 21, 500].flatMap fun n => [high n, low n]
  let long : List (List UInt64) :=
    [(List.range 2000).map (fun k => rw (k + 20000)),
      (List.range 2000).map (fun k => rw (k + 30000) % 3),
      up 1000 ++ down 1000, up 2000, down 2000, List.replicate 3000 (rw 5),
      (List.range 10000).map fun k => rw (k + 40000) % 100000]
  Library.Sorting.StraightInsertion.insertionInputs ++ chosen ++ long

end Library.Sorting.Quicksort
