import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import Library.Sorting.Heapsort.Program

/-! The least walk lengths from one vertex by Dijkstra's algorithm with a binary heap. -/

namespace Library.Graphs.Dijkstra

open Library.Sorting.Heapsort (swap)

/-- The word `2^64 - 1`, the result for a vertex that no walk reaches or whose least walk has
length `2^64 - 1` or more. -/
def INF : UInt64 := 0xffffffffffffffff

/-- `a + b`, or `INF` when the sum is `INF` or more. -/
def addSat (a b : UInt64) : UInt64 := if a < INF - b then a + b else INF

/-- The entry at `i` moves up the heap of keys `hk` and vertices `hv` while its key is below its
parent's. -/
def siftUp (i : UInt64) (hk hv : Array UInt64) : Array UInt64 × Array UInt64 :=
  if 0 < i ∧ hk[i.toNat]! < hk[((i - 1) / 2).toNat]! then
    siftUp ((i - 1) / 2) (swap ((i - 1) / 2) i hk) (swap ((i - 1) / 2) i hv)
  else (hk, hv)
termination_by i.toNat
decreasing_by
  have h : 0 < i ∧ hk[i.toNat]! < hk[((i - 1) / 2).toNat]! := by assumption
  have := UInt64.lt_iff_toNat_lt.mp h.1
  simp only [UInt64.toNat_div, UInt64.toNat_sub, UInt64.reduceToNat] at *
  omega

/-- The entry at `i` moves down the heap of `n` entries, exchanged with its child of smaller key
while that child's key is below its own.  Each branch names the child it moves to, `2i + 2` when
that child exists and has a smaller key than `2i + 1`, and `2i + 1` otherwise. -/
def siftDown (i n : UInt64) (hk hv : Array UInt64) : Array UInt64 × Array UInt64 :=
  if i < n / 2 then
    if i + i + 2 < n ∧ hk[(i + i + 2).toNat]! < hk[(i + i + 1).toNat]! then
      if hk[(i + i + 2).toNat]! < hk[i.toNat]! then
        siftDown (i + i + 2) n (swap i (i + i + 2) hk) (swap i (i + i + 2) hv)
      else (hk, hv)
    else
      if hk[(i + i + 1).toNat]! < hk[i.toNat]! then
        siftDown (i + i + 1) n (swap i (i + i + 1) hk) (swap i (i + i + 1) hv)
      else (hk, hv)
  else (hk, hv)
termination_by (n - i).toNat
decreasing_by
  all_goals
    have h : i < n / 2 := by assumption
    have := UInt64.toNat_lt n
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt64.reduceToNat] at h
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega

/-- The arcs out of `u`: each arc to a vertex `v` below `n` that shortens the tentative length of
`v` sets it and adds the entry of `v` to the heap of `h` entries.  The arrays are separate
parameters, so that the loop owns them and updates them in place. -/
def relax (n u : UInt64) (first heads lens dist hk hv : Array UInt64) (h : UInt64) :
    Array UInt64 × Array UInt64 × Array UInt64 × UInt64 :=
  let a := first[u.toNat]!
  let b := first[(u + 1).toNat]!
  LeanExe.loop (if a ≤ b then b - a else 0) (dist, hk, hv, h) fun t s =>
    let v := heads[(a + t).toNat]!
    let nd := addSat s.1[u.toNat]! lens[(a + t).toNat]!
    if v < n ∧ nd < s.1[v.toNat]! then
      let hu := siftUp s.2.2.2 (s.2.1.set! s.2.2.2.toNat nd) (s.2.2.1.set! s.2.2.2.toNat v)
      (s.1.set! v.toNat nd, hu.1, hu.2, s.2.2.2 + 1)
    else s

/-- The least walk lengths from `s`, with `INF` for a vertex that no walk reaches or whose least
walk has length `INF` or more, and `n` words of `INF` for a source of `n` or more.  The source is
done first, and each of the `m` steps of the loop, when the heap is not empty, removes the entry
with the least key and, when its vertex is not yet done, marks it done and relaxes its arcs. -/
def dijkstra (n s : UInt64) (first heads lens : Array UInt64) : Array UInt64 :=
  let m := first[n.toNat]!
  if s < n then
    let st0 := relax n s first heads lens ((LeanExe.build n fun _ => INF).set! s.toNat 0)
      (LeanExe.build m fun _ => 0) (LeanExe.build m fun _ => 0) 0
    (LeanExe.loop m (st0.1, st0.2.1, st0.2.2.1, st0.2.2.2,
        (LeanExe.build n fun _ => false).set! s.toNat true) fun _ q =>
      if 0 < q.2.2.2.1 then
        let u := q.2.2.1[(0 : UInt64).toNat]!
        let h := q.2.2.2.1 - 1
        let heap := siftDown 0 h (q.2.1.set! (0 : UInt64).toNat q.2.1[h.toNat]!)
          (q.2.2.1.set! (0 : UInt64).toNat q.2.2.1[h.toNat]!)
        if q.2.2.2.2[u.toNat]! then (q.1, heap.1, heap.2, h, q.2.2.2.2)
        else
          let r := relax n u first heads lens q.1 heap.1 heap.2 h
          (r.1, r.2.1, r.2.2.1, r.2.2.2, q.2.2.2.2.set! u.toNat true)
      else q).1
  else LeanExe.build n fun _ => INF

end Library.Graphs.Dijkstra
