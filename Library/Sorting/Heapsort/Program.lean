import LeanExe.Dialect.Loop

/-! Heapsort, Algorithm H of TAOCP §5.2.3, on an array of words, in place.  Indices start at 0, so
node `i` of the heap `xs[0, n)` has the children `2i + 1` and `2i + 2`, where Knuth's node `j` has
`2j` and `2j + 1`.  The heap order puts every node at or above its children.  `siftDown`, Knuth's
siftup of steps H3 to H8, moves the word at a node down until it is at least both children.
`heapify` performs the first phase of step H2: it sifts the nodes `n / 2 - 1` down to 0, which
makes the whole array a heap.  `heapsort` performs the second phase: it swaps the root, the largest
word, with the last word of the heap, shrinks the heap by one, and sifts the new root down, until
one word remains.  Knuth runs both phases in one loop and assumes at least two records, and
`heapsort` returns arrays of 0 and 1 elements unchanged.  A node `i` has a child if and only if
`i < n / 2`, and the program tests that before it computes `2i + 1`, so `2i + 1` does not wrap. -/

namespace Library.Sorting.Heapsort

/-- The array with the words at `i` and `j` exchanged.  The array comes last, so that a caller can
read it in the other arguments before the call takes it. -/
def swap (i j : UInt64) (xs : Array UInt64) : Array UInt64 :=
  let x := xs[i.toNat]!
  let y := xs[j.toNat]!
  (xs.set! i.toNat y).set! j.toNat x

/-- Steps H3 to H8: the word at node `i` moves down the heap `xs[0, n)`, exchanged with its larger
child while that child holds a larger word.  When the subtrees of the children of `i` are heaps,
the result is a heap from `i` down.  Knuth's steps H6 and H7 move the larger child up into the
vacant node and step H8 stores the word once, and the program exchanges the word with the child at
each level.  Each branch names the child it moves to, `2i + 2` when that child exists and holds a
larger word than `2i + 1`, and `2i + 1` otherwise, so that the new index reads no array: the
compiler copies an array that one argument of a tail call reads while a later argument consumes
it.  The index comes before the array, so that the call uses the array last and the compiler
updates it in place. -/
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

/-- Algorithm H with `n = xs.size`: arrays of 0 and 1 elements return unchanged.  Otherwise
`heapify` builds the heap, and for `e` from `n - 1` down to 1 the loop performs the second phase of
step H2: it exchanges the root with the word at `e` and sifts the new root down the heap
`xs[0, e)`.  The program reads the size once, before `heapify` takes the array, because a later
read of `xs` would make the compiler copy the array. -/
def heapsort (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  if n ≤ 1 then xs
  else
    LeanExe.loop (n - 1) (heapify n xs) fun k acc => siftDown 0 (n - 1 - k) (swap 0 (n - 1 - k) acc)

end Library.Sorting.Heapsort
