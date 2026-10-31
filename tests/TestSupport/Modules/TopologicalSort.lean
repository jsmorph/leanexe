import Library.Graphs.TopologicalSort.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of topological sorting. -/

namespace Library.Graphs.TopologicalSort

open TestSupport.Host

/-- An input of `n` vertices and the given relations. -/
def graph (n : Nat) (rels : List (Nat × Nat)) : List UInt64 :=
  UInt64.ofNat n :: rels.flatMap fun (j, k) => [UInt64.ofNat j, UInt64.ofNat k]

/-- A vertex below `n` from the high bits of an arbitrary word, which vary more than its low bits. -/
def vertexOf (n i : Nat) : Nat := ((rw i) >>> 29).toNat % n

/-- `count` arbitrary relations among `n` vertices.  With `forward` each relation goes from the
smaller vertex to the larger, so the relations admit an order; otherwise each keeps its arbitrary
direction. -/
def arbitrary (n count seed : Nat) (forward : Bool) : List (Nat × Nat) :=
  (List.range count).filterMap fun i =>
    let a := vertexOf n (seed + 2 * i)
    let b := vertexOf n (seed + 2 * i + 1)
    if forward then (if a = b then none else some (min a b, max a b)) else some (a, b)

/-- The inputs of the verified compiler's cases.  Valid inputs: no vertices, vertices without
relations, 1,000 vertices without relations, chains in both directions, nine vertices with ten
relations, a diamond, repeated relations, a relation of a vertex to itself alone and among other
relations, a relation of vertex 0 to itself as the only vertex, cycles of two and three vertices, a
cycle with a repeated relation, a cycle reachable from an acyclic part, a chain of 40 vertices
closed into a cycle, arbitrary relations among 20 and 40 vertices from the smaller vertex to the
larger, 400 such relations among 40 vertices, arbitrary relations in arbitrary directions among 20
vertices, which contain a cycle, and two such sets among 40 vertices, which admit an order.  Invalid
inputs, on which the module must still compute the Lean function: the empty array, an even number
of words, a vertex at or above the count, and a relation with the count 0. -/
def topoInputs : List (List UInt64) :=
  [graph 0 [], graph 1 [], graph 5 [], graph 1000 [], graph 4 [(0, 1), (1, 2), (2, 3)],
    graph 4 [(3, 2), (2, 1), (1, 0)],
    graph 9 [(0, 2), (7, 5), (3, 7), (7, 4), (3, 8), (8, 6), (5, 8), (4, 6), (1, 3), (2, 8)],
    graph 4 [(0, 1), (0, 2), (1, 3), (2, 3)], graph 3 [(0, 1), (0, 1), (1, 2), (0, 1)],
    graph 3 [(1, 1)], graph 4 [(0, 1), (2, 2), (1, 3)], graph 1 [(0, 0)],
    graph 2 [(0, 1), (1, 0)], graph 3 [(0, 1), (1, 2), (2, 0)],
    graph 2 [(0, 1), (0, 1), (1, 0)],
    graph 6 [(0, 1), (1, 2), (3, 4), (4, 5), (5, 3), (2, 3)],
    graph 40 (((List.range 39).map fun i => (i, i + 1)) ++ [(39, 0)]),
    graph 20 (arbitrary 20 30 100 true), graph 40 (arbitrary 40 80 300 true),
    graph 40 (arbitrary 40 400 700 true),
    graph 20 (arbitrary 20 30 200 false), graph 40 (arbitrary 40 25 400 false),
    graph 40 (arbitrary 40 60 500 false),
    [], [2, 0, 1, 1], [2, 0, 5], [0, 0, 0]]

end Library.Graphs.TopologicalSort
