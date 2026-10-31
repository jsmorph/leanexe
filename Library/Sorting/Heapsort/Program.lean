import LeanExe.Dialect.Loop

/-! Heapsort, Algorithm H of TAOCP §5.2.3, on an array of words, in place.  Node `i` of the heap
`xs[0, n)` has the children `2i + 1` and `2i + 2`, and the heap order puts every node at or above its
children.  `siftDown` moves the word at a node down until it is at least both children.  `heapify`
sifts the nodes `n / 2 - 1` down to 0, which makes the whole array a heap, and `heapsort` then
swaps the root, the largest word, with the last word of the heap, shrinks the heap by one, and
sifts the new root down, until one word remains.  A node `i` has a child exactly when `i < n / 2`,
so the program tests that before it computes `2i + 1`, which therefore does not wrap. -/

namespace Library.Sorting.Heapsort

/-- The array with the words at `i` and `j` exchanged.  The array comes last, so that a caller can
read it in the other arguments before the call takes it. -/
def swap (i j : UInt64) (xs : Array UInt64) : Array UInt64 :=
  let x := xs[i.toNat]!
  let y := xs[j.toNat]!
  (xs.set! i.toNat y).set! j.toNat x

/-- Steps H3 to H8: the word at node `i` moves down the heap `xs[0, n)`, exchanged with its larger
child while that child holds a larger word.  Each branch names the child it moves to, `2i + 2` when
that child exists and holds a larger word than `2i + 1`, and `2i + 1` otherwise, so that the new
index reads no array.  The index comes before the array, so that the array is used last and changes
in place. -/
def siftDown (i n : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if i < n / 2 then
    if i + i + 2 < n ∧ xs[(i + i + 1).toNat]! < xs[(i + i + 2).toNat]! then
      if xs[i.toNat]! < xs[(i + i + 2).toNat]! then siftDown (i + i + 2) n (swap i (i + i + 2) xs)
      else xs
    else
      if xs[i.toNat]! < xs[(i + i + 1).toNat]! then siftDown (i + i + 1) n (swap i (i + i + 1) xs)
      else xs
  else xs
termination_by (n - i).toNat
decreasing_by
  all_goals
    have h : i < n / 2 := by assumption
    have := UInt64.toNat_lt n
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt64.reduceToNat] at h
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega

/-- Steps H1 and H2: sift the nodes `n / 2 - 1` down to 0, which makes `xs[0, n)` a heap. -/
def heapify (n : UInt64) (xs : Array UInt64) : Array UInt64 :=
  LeanExe.loop (n / 2) xs fun k acc => siftDown (n / 2 - 1 - k) n acc

/-- The array in nondecreasing order: for `e` from `n - 1` down to 1, exchange the root with the
word at `e` and sift the new root down the heap `xs[0, e)`.  The size is read once, before
`heapify` takes the array, so that no later step reads the array that the loop changes. -/
def heapsort (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  if n ≤ 1 then xs
  else
    LeanExe.loop (n - 1) (heapify n xs) fun k acc => siftDown 0 (n - 1 - k) (swap 0 (n - 1 - k) acc)

end Library.Sorting.Heapsort
