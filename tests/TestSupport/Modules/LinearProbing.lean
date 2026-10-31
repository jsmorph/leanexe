import Library.HashTables.LinearProbing.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the hash table. -/

namespace Library.HashTables.LinearProbing

open TestSupport.Host

/-- The input words of a table of `m` slots and the operations `ops`, each a code and a key. -/
def program (m : UInt64) (ops : List (UInt64 × UInt64)) : List UInt64 :=
  m :: ops.flatMap fun (op, k) => [op, k]

/-- Insertions, lookups, and deletions of the keys `ks`. -/
def inserts (ks : List UInt64) : List (UInt64 × UInt64) := ks.map fun k => (0, k)
def lookups (ks : List UInt64) : List (UInt64 × UInt64) := ks.map fun k => (1, k)
def deletes (ks : List UInt64) : List (UInt64 × UInt64) := ks.map fun k => (2, k)

/-- `count` arbitrary operations, from the high bits of arbitrary words.  The code of operation
`i` is 0, 1, or an arbitrary word at least 2, by a residue modulo 3, and its key is a number below
`range`, or, when `range` is 0, one of 700 arbitrary words. -/
def arbitrary (count seed range : Nat) : List (UInt64 × UInt64) :=
  (List.range count).map fun i =>
    let c := rw (seed + i)
    let w := (rw (seed + count + i)) >>> 32
    (if (c >>> 32) % 3 = 0 then 0 else if (c >>> 32) % 3 = 1 then 1 else c ||| 2,
      if range = 0 then rw (seed + 2 * count + (w % 700).toNat) else w % UInt64.ofNat range)

/-- The verified compiler's cases run these inputs: the empty input, a slot count without
operations, a slot count and one word without a partner, tables of 0 and 1 slots, which hold no key,
and a table of 2 slots, which holds one key.  In a table of 8 slots, the keys 3, 11, 19, and 27
share the home slot 3.  Deleting 11 and then 3 moves the keys after them back, and deleting 27, the
last key of its cluster, moves none.  The keys 7, 15, 8, 23, and 9 fill slots 7, 0, 1, 2, and 3, a
cluster that wraps from the last slot to the first, and deletions of 7, 8, and 23 move keys back
along the cluster, the last moving 7 past 9, which stays at its home slot.  The keys 6, 14, 0, and
22 fill slots 6, 7, 0, and 1, and deleting 6 moves 14, leaves 0, whose home slot follows the empty
slot across the wrap, and moves 22 across the wrap.  The keys 3 and 11 of home slot 3 and the keys 5
and 13 of home slot 5 form one cluster, and the deletion of 3 moves 11 and leaves 5 and 13 in place.
A table of 8 slots filled with the keys 1 to 7 refuses an eighth key, searches for the absent key 9
through every occupied slot, and after a deletion accepts the eighth key.  A table of 7 slots holds
the keys 2, 9, 16, and 23 of home slot 2 and the key 3 of home slot 3 in one cluster, and the
deletions of 9 and 2 move the keys after them, 3 among them.  The other short inputs repeat
insertions and deletions of one key, delete absent keys, use the deletion codes 2, 3, `2^63`, and
`2^64 - 1` and the keys 0 and `2^64 - 1`, and end with a word without a partner.  The long inputs
run 2,000 arbitrary operations on keys below 40 in a table of 16 slots, 3,000 operations on keys
below 500 in a table of 101 slots, and 3,000 operations on 700 arbitrary words in a table of 1,024
slots. -/
def probeInputs : List (List UInt64) :=
  let half : UInt64 := 9223372036854775808
  let chosen : List (List UInt64) :=
    [[], [5], [8, 0], program 0 (inserts [7] ++ lookups [7] ++ deletes [7]),
      program 1 (inserts [7] ++ lookups [7] ++ deletes [7]),
      program 2 (inserts [7, 9] ++ lookups [7, 9] ++ deletes [9, 7] ++ inserts [9] ++ lookups [9]),
      program 8 (inserts [3, 11, 19, 27] ++ lookups [3, 11, 19, 27] ++ deletes [11] ++
        lookups [3, 11, 19, 27] ++ deletes [3] ++ lookups [19, 27] ++ deletes [27] ++
        lookups [19] ++ inserts [3] ++ lookups [3, 19]),
      program 8 (inserts [7, 15, 8, 23, 9] ++ lookups [7, 15, 8, 23, 9] ++ deletes [7] ++
        lookups [15, 8, 23, 9] ++ inserts [7] ++ deletes [8] ++ lookups [7, 15, 23, 9] ++
        deletes [23] ++ lookups [7, 15, 9]),
      program 8 (inserts [6, 14, 0, 22] ++ deletes [6] ++ lookups [6, 14, 0, 22]),
      program 8 (inserts [3, 11, 5, 13] ++ deletes [3] ++ lookups [3, 11, 5, 13]),
      program 8 (inserts [1, 2, 3, 4, 5, 6, 7, 8] ++ lookups [8, 9] ++ deletes [4] ++
        inserts [8] ++ lookups [1, 2, 3, 4, 5, 6, 7, 8]),
      program 7 (inserts [2, 9, 16, 23, 3] ++ deletes [9] ++ lookups [2, 9, 16, 23, 3] ++
        deletes [2] ++ lookups [16, 23, 3]),
      program 8 (inserts [5, 5] ++ deletes [5, 5] ++ inserts [5] ++ lookups [5] ++ deletes [6]),
      program 8 (inserts [1, 9, 17] ++ [(3, 9), (half, 1), (maxU, 17), (2, 1)] ++
        lookups [1, 9, 17]),
      program 4 (inserts [0, maxU, 4] ++ lookups [0, maxU, 4, 8] ++ deletes [0] ++ lookups [maxU, 4]),
      program 8 (inserts [3, 4]) ++ [1]]
  let long : List (List UInt64) :=
    [program 16 (arbitrary 2000 7000 40), program 101 (arbitrary 3000 11000 500),
      program 1024 (arbitrary 3000 21000 0)]
  chosen ++ long

end Library.HashTables.LinearProbing
