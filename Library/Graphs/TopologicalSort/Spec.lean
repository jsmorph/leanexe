/-! The specification of topological sorting.  The input `xs` holds the vertex count `n = xs[0]`
and then pairs `xs[2e + 1], xs[2e + 2]`, the relation `e`, which states that its first vertex comes
before its second.  An order is a topological order when it lists every vertex below `n` exactly
once and puts the first vertex of every relation before the second.  Many inputs have several
topological orders, so the specification is a property of the result and not a function: on a
well-formed input, the result is a topological order, or it is the empty array and no topological
order exists.  When `n = 0`, the empty array is the only topological order.  A relation of a vertex
to itself, or any cycle of relations, admits no topological order, and a repeated relation means
the same as one copy.  The specification puts no bound on `n`, so the input `[2^64 - 1]` is well
formed and its only orders hold `2^64 - 1` words.  The specification says nothing about inputs that
are not well formed. -/

namespace Library.Graphs.TopologicalSort

/-- The vertex count `n`. -/
def vertexCount (xs : Array UInt64) : Nat := xs[0]!.toNat

/-- The number of relations: the whole pairs after the count. -/
def relationCount (xs : Array UInt64) : Nat := (xs.size - 1) / 2

/-- The first vertex of relation `e`. -/
def source (xs : Array UInt64) (e : Nat) : Nat := xs[2 * e + 1]!.toNat

/-- The second vertex of relation `e`. -/
def target (xs : Array UInt64) (e : Nat) : Nat := xs[2 * e + 2]!.toNat

/-- A well-formed input: the count and whole pairs, every vertex of which is below the count. -/
def Valid (xs : Array UInt64) : Prop :=
  0 < xs.size ∧ xs.size % 2 = 1 ∧
    ∀ e, e < relationCount xs → source xs e < vertexCount xs ∧ target xs e < vertexCount xs

/-- `order` lists every vertex below `n` exactly once, and puts the first vertex of every relation
before its second. -/
def IsTopologicalOrder (xs order : Array UInt64) : Prop :=
  order.size = vertexCount xs ∧
    (∀ p, p < order.size → order[p]!.toNat < vertexCount xs) ∧
    (∀ p q, p < q → q < order.size → order[p]! ≠ order[q]!) ∧
    (∀ e, e < relationCount xs → ∀ p q, p < order.size → q < order.size →
      order[p]!.toNat = source xs e → order[q]!.toNat = target xs e → p < q)

end Library.Graphs.TopologicalSort
