import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! A hash table with linear probing, Algorithms L and R of TAOCP §6.4.  The input holds the slot
count `m = xs[0]` and then the operations as pairs `xs[2e + 1], xs[2e + 2]` of a code and a key:
code 0 inserts, code 1 looks up, and any other code deletes.  The table of `m` slots is an array `t`
of `2m` words: slot `s` is occupied when `t[2s] ≠ 0`, and then `t[2s + 1]` is its key.  Every word,
0 among them, is a possible key, so the occupancy takes a word of its own, and one array holds both
words of every slot so that a deletion, which moves keys, returns one array.  The home slot of key
`k` is `k % m`, and a search inspects the slots `k % m`, `k % m + 1`, and so on, with slot 0 after
slot `m - 1`, until it finds the key or an empty slot.  Knuth's searches move down the table, and
these move up, so the conditions of Algorithm R appear in mirror image.  The loop's state holds the
outputs, the number of keys, and the table. -/

namespace Library.HashTables.LinearProbing

/-- The slot after slot `s` of a table of `m` slots. -/
def next (m s : UInt64) : UInt64 := if s + 1 < m then s + 1 else 0

/-- The first slot, from slot `s` on and within `fuel` slots, that is empty or holds the key `k`,
or the slot `fuel` steps after `s` when every slot on the way holds another key. -/
def probe (m k s fuel : UInt64) (t : Array UInt64) : UInt64 :=
  if 0 < fuel ∧ 0 < t[(s + s).toNat]! then
    if t[(s + s + 1).toNat]! = k then s else probe m k (next m s) (fuel - 1) t
  else s
termination_by fuel.toNat
decreasing_by
  rename_i h _
  have := UInt64.lt_iff_toNat_lt.mp h.1
  simp only [UInt64.toNat_sub, UInt64.reduceToNat] at *
  omega

/-- The key of slot `i` moves to the empty slot `j`, and slot `i` becomes empty. -/
def move (j i : UInt64) (t : Array UInt64) : Array UInt64 :=
  ((t.set! (j + j + 1).toNat t[(i + i + 1).toNat]!).set! (j + j).toNat 1).set! (i + i).toNat 0

/-- The number of steps from slot `a` to slot `b` of a table of `m` slots. -/
def gap (m a b : UInt64) : UInt64 := (b + m - a) % m

/-- Algorithm R, within `fuel` slots: slot `j` is empty, and slot `i` is the next slot to inspect.
The search for the key of an occupied slot `i` starts at its home slot `r` and passes slot `j`
unless `r` lies in the slots after `j` up to `i`, that is, unless `r` is fewer slots before `i` than
`j` is.  A key whose search passes slot `j` moves to slot `j` with `move`, and slot `i` becomes the
empty slot.  The scan stops at an empty slot or after `fuel` slots.  `step` empties the deleted
key's slot before it calls `close`. -/
def close (m j i fuel : UInt64) (t : Array UInt64) : Array UInt64 :=
  if 0 < fuel ∧ 0 < t[(i + i).toNat]! then
    if gap m (t[(i + i + 1).toNat]! % m) i < gap m j i then
      close m j (next m i) (fuel - 1) t
    else close m i (next m i) (fuel - 1) (move j i t)
  else t
termination_by fuel.toNat
decreasing_by
  all_goals
    rename_i h _
    have := UInt64.lt_iff_toNat_lt.mp h.1
    simp only [UInt64.toNat_sub, UInt64.reduceToNat] at *
    omega

/-- The slot that holds the key `k`, or the empty slot where its search ends. -/
def slot (m k : UInt64) (t : Array UInt64) : UInt64 := probe m k (k % m) m t

/-- One operation, with the code `op` and the key `k`, on the state of the outputs, the number of
keys `n`, and the table.  Slot `i` is the slot where the search for `k` ends, and it holds `k`
exactly when it is occupied.  Code 0 outputs 0 when slot `i` is occupied or `m ≤ n + 1`, since a
table of `m` slots holds at most `m - 1` keys, and otherwise writes `k` into slot `i`, increases
`n`, and outputs 1.  Code 1 outputs 1 when slot `i` is occupied and 0 otherwise.  Any other code,
when slot `i` is occupied, empties it, decreases `n`, runs `close` from the next slot, and outputs
1, and otherwise outputs 0.  Each component chooses its own new value, so that the loop's body ends
in one tuple. -/
@[inline] def step (m op k : UInt64) (s : Array UInt64 × UInt64 × Array UInt64) :
    Array UInt64 × UInt64 × Array UInt64 :=
  let i := slot m k s.2.2
  (s.1.push
      (if op = 0 then (if 0 < s.2.2[(i + i).toNat]! ∨ m ≤ s.2.1 + 1 then 0 else 1)
      else if 0 < s.2.2[(i + i).toNat]! then 1 else 0),
    if op = 0 then (if 0 < s.2.2[(i + i).toNat]! ∨ m ≤ s.2.1 + 1 then s.2.1 else s.2.1 + 1)
    else if op = 1 then s.2.1
    else if 0 < s.2.2[(i + i).toNat]! then s.2.1 - 1 else s.2.1,
    if op = 0 then
      (if 0 < s.2.2[(i + i).toNat]! ∨ m ≤ s.2.1 + 1 then s.2.2
      else (s.2.2.set! (i + i).toNat 1).set! (i + i + 1).toNat k)
    else if op = 1 then s.2.2
    else if 0 < s.2.2[(i + i).toNat]! then close m i (next m i) m (s.2.2.set! (i + i).toNat 0)
    else s.2.2)

/-- The outputs of the operations, one word for each, from a table of `2m` zero words for the slot
count `m = xs[0]`, or the empty array for the empty input. -/
def hashTable (xs : Array UInt64) : Array UInt64 :=
  if xs.size.toUInt64 = 0 then #[]
  else
    (LeanExe.loop ((xs.size.toUInt64 - 1) / 2)
      ((#[] : Array UInt64), (0 : UInt64),
        LeanExe.build (xs[(0 : UInt64).toNat]! + xs[(0 : UInt64).toNat]!) fun _ => (0 : UInt64))
      fun e s => step xs[(0 : UInt64).toNat]! xs[(e + e + 1).toNat]! xs[(e + e + 2).toNat]! s).1

end Library.HashTables.LinearProbing
