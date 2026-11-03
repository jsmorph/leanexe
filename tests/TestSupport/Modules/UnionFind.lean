import Library.Graphs.UnionFind.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of equivalence classes, and `leastLabels`, which
computes their expected results by a search of the graph of the pairs, apart from the program. -/

namespace Library.Graphs.UnionFind

open TestSupport.Host

/-- A depth-first search from the element `r` that labels with `r` every unlabeled element it
reaches, where `n` marks an unlabeled element and `adj` lists the neighbors of each element.  The
count `fuel` bounds the steps, and a count above the number of pushes suffices. -/
def visit (n r : Nat) (adj : Array (List Nat)) : Nat → Array Nat → List Nat → Array Nat
  | 0, lab, _ => lab
  | _ + 1, lab, [] => lab
  | fuel + 1, lab, x :: stack =>
    let fresh := adj[x]!.filter fun y => lab[y]! == n
    visit n r adj fuel (fresh.foldl (fun l y => l.set! y r) lab) (fresh ++ stack)

/-- The least element of the class of each element below `n`: the pairs whose elements are both
below `n` are edges in both directions, and a search from each unlabeled element in increasing
order labels its component with it. -/
def leastLabels (n : Nat) (js ks : List UInt64) : List UInt64 :=
  let pairs := (js.zip ks).filter fun (a, b) => a.toNat < n && b.toNat < n
  let adj := pairs.foldl (fun (g : Array (List Nat)) (a, b) =>
    (g.modify a.toNat (b.toNat :: ·)).modify b.toNat (a.toNat :: ·)) (Array.replicate n [])
  let fuel := n + 2 * pairs.length + 1
  let lab := (List.range n).foldl (fun (lab : Array Nat) i =>
    if lab[i]! == n then visit n i adj fuel (lab.set! i i) [i] else lab) (Array.replicate n n)
  lab.toList.map UInt64.ofNat

/-- The inputs `(n, js, ks)` of the cases.  Every list of at most two pairs over the elements 0 to
4 with `n = 4`, so that the element 4 lies outside, covers repeated pairs, pairs of an element with
itself, and pairs in both orders.  Small cases cover `n = 0` and `n = 1`, arrays of different
lengths, whose extra words belong to no pair, and a pair that unites two classes of several
elements each.  The element `2^32`, which a program that reads elements in 32 bits places at 0,
`2^63` and `2^64 - 1`, which a program that reads elements as signed numbers places below `n`,
and 1,000, which lies between `n` and `2^32`, each appear beside an element other than 0.  Random
pairs from the high bits of `rw` over 110 and 1,100 values with `n = 100` and `n = 1,000`, some of
them out of range, form several classes, with arrays of equal and of different lengths.  For
10,000 elements, the pairs `(i, i + 1)` in increasing order make one tree whose path from 0
passes every element, and a final pair `(0, 0)` searches that path from both elements.  The same
pairs with their elements exchanged make a tree of depth 1, and pairs with 0 in both orders make
one class. -/
def classInputs : List (Nat × List UInt64 × List UInt64) :=
  let elems : List UInt64 := [0, 1, 2, 3, 4]
  let pairs := elems.flatMap fun a => elems.map fun b => (a, b)
  let one := (4, [], []) :: pairs.map fun (a, b) => (4, [a], [b])
  let two := pairs.flatMap fun (a, b) => pairs.map fun (c, d) => (4, [a, c], [b, d])
  let draw (n seed t : Nat) : UInt64 := UInt64.ofNat ((rw (seed + t)).toNat / 2 ^ 40 % (n + n / 10))
  let random (n m extra seed : Nat) : Nat × List UInt64 × List UInt64 :=
    (n, (List.range m).map fun t => draw n (100003 * seed) (2 * t),
      (List.range (m + extra)).map fun t => draw n (100003 * seed) (2 * t + 1))
  let big := 10000
  let up := (List.range (big - 1)).map UInt64.ofNat
  let next := (List.range (big - 1)).map fun i => UInt64.ofNat (i + 1)
  let zeros := (List.range (big - 1)).map fun _ => (0 : UInt64)
  [(0, [], []), (0, [0], [0]), (1, [], []), (1, [0], [0]), (1, [0, 0], [0]), (3, [0, 1, 2], [1]),
    (3, [2], [0, 1, 2]), (3, [0, 3], [3, 1]), (3, [maxU], [0]), (3, [0], [maxU]),
    (5, [0, 1, 4294967296], [1, 4294967296, 3]), (5, [4294967296, 2], [0, 4294967296]),
    (3, [maxU], [1]), (3, [1], [maxU]), (3, [9223372036854775808], [1]), (5, [1000, 2], [1, 1000]),
    (8, [0, 1, 4, 5, 2], [1, 2, 5, 6, 6]), (8, [7, 6, 5, 3], [6, 5, 4, 0])] ++
    one ++ two ++
    [random 100 50 0 1, random 100 70 3 2, random 100 99 0 3, random 1000 600 7 4,
      random 1000 2000 0 5, (big, up ++ [0], next ++ [0]), (big, next, up), (big, zeros, next),
      (big, next, zeros)]

end Library.Graphs.UnionFind
