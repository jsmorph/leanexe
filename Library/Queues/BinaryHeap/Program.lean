import Library.Sorting.Heapsort.Program

/-! A priority queue as a binary heap, TAOCP §5.2.3.  The heap is the prefix `h[0, n)` of an array,
with the largest word at the root and every node at or above its children, as in heapsort.  An
insertion writes the value at position `n`, or appends it when the array is full, and moves it up
while its parent holds a smaller word.  A removal outputs the root, moves the last word of the heap
to the root, and moves that word down with heapsort's `siftDown`.  The loop's state holds the
outputs, the heap's size, and the array, in that order, so that each step reads the array before it
changes it. -/

namespace Library.Queues.BinaryHeap

open Library.Sorting.Heapsort

/-- The word at node `i` moves up the heap, exchanged with its parent while the parent holds a
smaller word.  The parent of node `i` is `(i - 1) / 2`. -/
def siftUp (i : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if 0 < i ∧ xs[((i - 1) / 2).toNat]! < xs[i.toNat]! then siftUp ((i - 1) / 2) (swap ((i - 1) / 2) i xs)
  else xs
termination_by i.toNat
decreasing_by
  have h : 0 < i ∧ xs[((i - 1) / 2).toNat]! < xs[i.toNat]! := by assumption
  have := UInt64.lt_iff_toNat_lt.mp h.1
  simp only [UInt64.toNat_div, UInt64.toNat_sub, UInt64.reduceToNat] at *
  omega

/-- One operation on the state: the outputs, the heap's size, and the array.  Each component
chooses its own new value, so that the loop's body ends in one tuple; the compiler unfolds `step`
into the loop, whose state it owns, so that the arrays change in place. -/
@[inline] def step (op v : UInt64) (s : Array UInt64 × UInt64 × Array UInt64) :
    Array UInt64 × UInt64 × Array UInt64 :=
  (if 0 < op ∧ 0 < s.2.1 then s.1.push s.2.2[(0 : UInt64).toNat]! else s.1,
    if op = 0 then s.2.1 + 1 else if 0 < s.2.1 then s.2.1 - 1 else s.2.1,
    if op = 0 then
      siftUp s.2.1
        (if s.2.1 < s.2.2.size.toUInt64 then s.2.2.set! s.2.1.toNat v else s.2.2.push v)
    else if 0 < s.2.1 then
      siftDown 0 (s.2.1 - 1) (s.2.2.set! (0 : UInt64).toNat s.2.2[(s.2.1 - 1).toNat]!)
    else s.2.2)

/-- The words that the removals output, in order. -/
def heapQueue (xs : Array UInt64) : Array UInt64 :=
  (LeanExe.loop (xs.size.toUInt64 / 2) ((#[] : Array UInt64), (0 : UInt64), (#[] : Array UInt64))
    fun i s => step xs[(i + i).toNat]! xs[(i + i + 1).toNat]! s).1

end Library.Queues.BinaryHeap
