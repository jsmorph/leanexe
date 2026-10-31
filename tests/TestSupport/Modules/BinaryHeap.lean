import Library.Queues.BinaryHeap.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the binary heap. -/

namespace Library.Queues.BinaryHeap

open TestSupport.Host

/-- The input words of the operations `ops`, each a code and a value. -/
def program (ops : List (UInt64 × UInt64)) : List UInt64 :=
  ops.flatMap fun (op, v) => [op, v]

/-- Insertions of the values `vs`. -/
def inserts (vs : List UInt64) : List (UInt64 × UInt64) := vs.map fun v => (0, v)

/-- `k` removals, with code 1 and value 0. -/
def removes (k : Nat) : List (UInt64 × UInt64) := List.replicate k (1, 0)

/-- `count` arbitrary operations.  About one in three removes, with an arbitrary multiple of 3 as
its code, or 1 in place of 0, and an arbitrary word as its value.  The others insert an arbitrary
value below `range`, or an arbitrary word when `range` is 0. -/
def arbitrary (count seed range : Nat) : List (UInt64 × UInt64) :=
  (List.range count).map fun i =>
    let c := rw (seed + i)
    let w := rw (seed + count + i)
    if c % 3 = 0 then (if c = 0 then 1 else c, w)
    else (0, if range = 0 then w else w % UInt64.ofNat range)

/-- The verified compiler's cases run these inputs: the empty input, one word without a partner, a
removal from the empty queue, one insertion and one removal, five insertions with a repeated word
and seven removals, the words 0, `2^63`, and `2^64 - 1` inserted and removed, removals with the
codes 2, `2^32`, `2^63`, and `2^64 - 1`, an insertion after the queue has emptied, and two
insertions and a removal followed by the word 1 without a partner, which would remove the remaining
word if the program read it as an operation.  The heap reuses the array's positions when it shrinks
and grows again: ten insertions, five removals, ten insertions, and fifteen removals.  Insertions in
increasing order move each new word to the root, and insertions in decreasing order move none.  The
long inputs insert 100 and 300 arbitrary words and remove them all, run 1,000 arbitrary operations
whose inserted values lie below 10, and run 2,000 arbitrary operations of arbitrary words. -/
def heapInputs : List (List UInt64) :=
  let half : UInt64 := 9223372036854775808
  let chosen : List (List UInt64) :=
    [[], [5], program [(1, 0)], program [(0, 7), (1, 0)],
      program (inserts [5, 3, 8, 1, 8] ++ removes 7),
      program (inserts [0, maxU, half, 0, maxU] ++ removes 6),
      program (inserts [4, 9, 2, 6, 1] ++ [(2, 0), (4294967296, 5), (half, 0), (maxU, 0), (2, 0)]),
      program [(0, 5), (1, 0), (1, 0), (0, 8), (0, 3), (1, 0), (1, 0)],
      program [(0, 3), (0, 9), (1, 0)] ++ [1],
      program (inserts ((List.range 10).map fun k => rw (k + 100)) ++ removes 5 ++
        inserts ((List.range 10).map fun k => rw (k + 200)) ++ removes 15),
      program (inserts ((List.range 40).map fun k => UInt64.ofNat k) ++ removes 40),
      program (inserts ((List.range 40).map fun k => UInt64.ofNat (40 - k)) ++ removes 40)]
  let long : List (List UInt64) :=
    [program (inserts ((List.range 100).map fun k => rw (k + 1000)) ++ removes 100),
      program (inserts ((List.range 300).map fun k => rw (k + 3000)) ++ removes 300),
      program (arbitrary 1000 5000 10),
      program (arbitrary 2000 9000 0)]
  chosen ++ long

end Library.Queues.BinaryHeap
