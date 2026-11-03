import TestSupport.Host
import Library.Random.SplitMix64.Program

/-! The inputs of the verified compiler's cases of shortest paths, and `shortest`, which computes
their expected results by the algorithm of Bellman and Ford, apart from the program. -/

namespace Library.Graphs.Dijkstra

open TestSupport.Host

/-- The arcs `(u, v, w)` of the forward star with `n` vertices: for each `u` below `n`, the
positions `k` from `first[u]` to `first[u + 1] - 1` that lie below the lengths of `heads` and
`lens` and whose head `heads[k]` is below `n`. -/
def caseArcs (n : Nat) (first heads lens : Array UInt64) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun u =>
    ((List.range first[u + 1]!.toNat).drop first[u]!.toNat).filterMap fun k =>
      if k < heads.size ∧ k < lens.size ∧ heads[k]!.toNat < n then
        some (u, heads[k]!.toNat, lens[k]!.toNat)
      else none

/-- One round of Bellman and Ford: each arc in turn whose tail has a length sets the length of its
head to the tail's length plus its own, as natural numbers, when the head has no length or a
greater one. -/
def bfRound (as : List (Nat × Nat × Nat)) (d : Array (Option Nat)) : Array (Option Nat) :=
  as.foldl (fun d (u, v, w) =>
    match d[u]!, d[v]! with
    | some a, some b => if a + w < b then d.set! v (some (a + w)) else d
    | some a, none => d.set! v (some (a + w))
    | none, _ => d) d

/-- Rounds until one changes nothing, at most `fuel` of them. -/
def bfRounds (as : List (Nat × Nat × Nat)) : Nat → Array (Option Nat) → Array (Option Nat)
  | 0, d => d
  | fuel + 1, d =>
    let d' := bfRound as d
    if d' == d then d else bfRounds as fuel d'

/-- The least walk length from `s` to each vertex below `n`, or `2^64 - 1` when no walk reaches it
or its least length is `2^64 - 1` or more.  The lengths are natural numbers, so some least walk
visits no vertex twice, `n` rounds find every least length, and one more changes nothing. -/
def shortest (n s : UInt64) (first heads lens : List UInt64) : List UInt64 :=
  let N := n.toNat
  let as := caseArcs N first.toArray heads.toArray lens.toArray
  let d := bfRounds as (N + 1) ((Array.replicate N none).set! s.toNat (some 0))
  d.toList.map fun
    | some x => if x < 2 ^ 64 - 1 then UInt64.ofNat x else maxU
    | none => maxU

/-- The forward star of `n` vertices with the arcs `as`, each a tail, a head, and a length, with
the arcs of each tail in the order of `as` and without the arcs whose tail is `n` or more. -/
def star (n : Nat) (as : List (Nat × UInt64 × UInt64)) :
    List UInt64 × List UInt64 × List UInt64 :=
  let out := (as.foldl (fun (g : Array (List (UInt64 × UInt64))) (u, v, w) =>
    g.modify u ((v, w) :: ·)) (Array.replicate n [])).toList.map List.reverse
  ((out.scanl (fun k l => k + l.length) 0).map UInt64.ofNat, out.flatMap (·.map (·.1)),
    out.flatMap (·.map (·.2)))

/-- The inputs `(n, s, first, heads, lens)` of the cases, each in the form that `WellFormed`
states.  Small graphs cover no vertex, one vertex, sources of `n`, `2^32`, `2^32 + 1`, and
`2^64 - 1`, of which a program that reads the source in 32 bits places `2^32` at 0 and `2^32 + 1`
at 1, and sources of `n` or more whose words of `first` give a range of arcs, which a program
without the test `s < n` relaxes.  They cover a path, vertices that no walk reaches, parallel arcs
in decreasing length, which add a vertex to the heap three times, and in increasing length, a
shorter walk found after a longer one, loops, and arcs of length 0.  Heads of `n`, `2^32 + 1`,
`2^32 + 2`, `2^33 + 3`, `2^63`, and `2^64 - 1` name no vertex, and a program that reads heads in 32
bits places `2^32 + 1`, `2^32 + 2`, `2^33 + 3`, and `2^63` in the graph.  Lengths of `2^32`,
`2^63`, `2^64 - 2`, and `2^64 - 1` give sums that a program with 32-bit or signed lengths gets
wrong, sums of `2^64 - 2`, which is a length, and of `2^64 - 1` and `2^64`, which are not, and a
vertex whose least walk avoids a walk that saturates.  Arrays whose `first[0]` is above 0, whose
`heads` and `lens` hold words past `first[n]`, or whose vertices have no arcs although `heads` is
not empty, cover the forward star's bounds, and two graphs from the reviews detect a `siftUp` with
the parent `i / 2` and a `siftDown` whose guard is `i < (h - 1) / 2`.  Random graphs drawn with
SplitMix64 have 10 to 1,000 vertices, 15 to 5,000 arcs, lengths below 10, 1,000, 1,000,000, and
`2^62`, and several sources, and two graphs of 100 and 200 vertices give the source an arc to
every other vertex with a length of 64 bits, so that keys on both sides of `2^63` share the heap.
A grid of 40 by 40 vertices with arcs in both directions, a complete graph of 40 vertices, and a
vertex with 100 arcs to one head in decreasing length, which fills the heap, cover long runs. -/
def dijkstraInputs : List (UInt64 × UInt64 × List UInt64 × List UInt64 × List UInt64) :=
  let case (n : Nat) (s : UInt64) (as : List (Nat × UInt64 × UInt64)) :=
    let (first, heads, lens) := star n as
    (UInt64.ofNat n, s, first, heads, lens)
  let big : UInt64 := 9223372036854775808
  let draw (seed t : Nat) : UInt64 :=
    (Library.Random.SplitMix64.splitMix (UInt64.ofNat (100003 * seed + t))).2
  let random (n m seed wmax : Nat) : List (Nat × UInt64 × UInt64) :=
    (List.range m).map fun t =>
      ((draw seed (3 * t)).toNat % n, UInt64.ofNat ((draw seed (3 * t + 1)).toNat % n),
        UInt64.ofNat ((draw seed (3 * t + 2)).toNat % wmax))
  let random64 (n m seed : Nat) : List (Nat × UInt64 × UInt64) :=
    (List.range m).map fun t =>
      ((draw seed (3 * t)).toNat % n, UInt64.ofNat ((draw seed (3 * t + 1)).toNat % n),
        draw seed (3 * t + 2))
  let spread (n seed : Nat) : List (Nat × UInt64 × UInt64) :=
    (List.range (n - 1)).map fun v => (0, UInt64.ofNat (v + 1), draw seed v)
  let side := 40
  let grid := (List.range (side * side)).flatMap fun i =>
    let near := (if i % side + 1 < side then [i + 1] else []) ++
      (if i + side < side * side then [i + side] else []) ++
      (if 0 < i % side then [i - 1] else []) ++ (if side ≤ i then [i - side] else [])
    near.map fun j =>
      (i, UInt64.ofNat j, UInt64.ofNat ((draw 7 (4 * i + j % 4)).toNat % 100 + 1))
  let complete := (List.range 40).flatMap fun i => (List.range 40).filterMap fun j =>
    if i = j then none
    else some (i, UInt64.ofNat j, UInt64.ofNat ((draw 11 (40 * i + j)).toNat % 100))
  let lazy : List (Nat × UInt64 × UInt64) :=
    [(0, 3, 100), (0, 1, 1), (1, 3, 50), (0, 2, 2), (2, 3, 10)]
  [case 0 0 [], case 1 0 [], case 1 0 [(0, 0, 5)], case 3 3 [(0, 1, 1)],
    case 3 maxU [(0, 1, 1)], case 3 4294967296 [(0, 1, 1)], case 3 4294967297 [(1, 2, 1)],
    (1, 1, [0, 0, 1], [0], [5]), (1, maxU, [1, 1], [0], [5]),
    case 4 0 [(0, 1, 5), (1, 2, 7), (2, 3, 1)], case 4 0 [(1, 2, 3), (2, 3, 4)],
    case 4 1 [(1, 2, 3), (2, 3, 4)], case 4 0 lazy, case 4 2 lazy,
    case 2 0 [(0, 1, 5), (0, 1, 4), (0, 1, 3)], case 2 0 [(0, 1, 3), (0, 1, 4), (0, 1, 5)],
    case 3 0 [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 2, 0), (2, 2, 7)],
    case 3 0 [(0, 3, 1), (0, 4294967297, 1), (0, big, 1), (0, maxU, 1), (0, 2, 9)],
    case 4 0 [(0, 1, 3), (1, 4294967298, 1), (1, 3, 8), (0, 8589934595, 2)],
    case 3 0 [(0, 1, big), (1, 2, big)], case 3 0 [(0, 1, maxU)], case 3 0 [(0, 1, maxU - 1)],
    case 3 0 [(0, 1, big), (1, 2, big - 2)], case 3 0 [(0, 1, big), (1, 2, big - 1)],
    case 3 0 [(0, 1, maxU - 1), (1, 2, 1)], case 3 0 [(0, 1, maxU - 1), (1, 2, 0)],
    case 3 0 [(0, 1, maxU - 5), (1, 2, 10), (0, 2, maxU - 3)],
    case 3 0 [(0, 1, 4294967296), (1, 2, 4294967296)], case 3 0 [(0, 1, big), (0, 2, 1), (2, 1, 5)],
    (2, 0, [2, 3, 3], [1, 1, 1, 1], [1, 1, 7, 9]), (2, 0, [0, 1, 1], [1, 0, 0], [4]),
    (3, 1, [0, 0, 0, 0], [1, 2], [5, 6]),
    (3, 0, [1, 3, 4, 4], [2, 1, 2, 2, 0, 7], [0, 4, 6, 1, 5, 5]),
    case 11 0 [(0, 2, 2), (0, 1, 0), (0, 3, 1), (0, 4, 4), (0, 5, 3), (1, 6, 4), (1, 7, 0),
      (1, 8, 4), (2, 5, 0), (5, 10, 0), (7, 9, 4)],
    case 5 0 [(0, 1, 0), (0, 2, 0), (0, 3, 1), (2, 3, 0), (3, 4, 0)],
    case 10 0 (random 10 30 1 10), case 10 3 (random 10 30 1 10), case 10 0 (random 10 15 2 10),
    case 20 0 (random 20 400 8 1000), case 100 0 (random 100 500 3 1000),
    case 100 17 (random 100 500 3 1000), case 100 0 (random 100 300 4 (2 ^ 62)),
    case 100 0 (spread 100 10 ++ random64 100 300 5),
    case 200 0 (spread 200 12 ++ random64 200 1000 9),
    case 1000 0 (random 1000 5000 6 1000000), case 1000 999 (random 1000 3000 7 1000000),
    case (side * side) 0 grid, case (side * side) 820 grid, case 40 0 complete,
    case 40 39 complete, case 2 0 ((List.range 100).map fun w => (0, 1, UInt64.ofNat (200 - w)))]

end Library.Graphs.Dijkstra
