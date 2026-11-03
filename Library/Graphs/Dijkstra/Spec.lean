/-! The specification of the least walk lengths from one vertex.  The graph is in forward-star form:
the arcs out of a vertex `u` below `n` are the positions `k` with `first[u] ≤ k < first[u + 1]` that
lie below the sizes of `heads` and `lens`, each from `u` to `heads[k]` with the length `lens[k]`,
and an arc whose head is `n` or more is no arc.  `Walk n first heads lens s v L` states that a walk
from `s` to `v` of total length `L` exists, with lengths as natural numbers, and a walk starts only
at a vertex below `n`.  `Distances` states that the result holds `n` words and that word `v` is the
least length of a walk from `s` to `v` when that length is below `2^64 - 1`, and `2^64 - 1` when no
walk reaches `v` or every walk has length `2^64 - 1` or more, which determines the result, as
`distances_unique` of the proof states.  `WellFormed` states the request's form of the graph:
`first` holds at least `n + 1` words, the first `n + 1` in nondecreasing order, and `first[n]` is at
most the size of `heads` and of `lens`.  The specification names the result and not the method, and
the program text shows Dijkstra's algorithm. -/

namespace Library.Graphs.Dijkstra

/-- An arc from `u` to `v` of length `w`. -/
def Arc (n : Nat) (first heads lens : Array UInt64) (u v w : Nat) : Prop :=
  u < n ∧ v < n ∧ ∃ k, first[u]!.toNat ≤ k ∧ k < first[u + 1]!.toNat ∧ k < heads.size ∧
    k < lens.size ∧ heads[k]!.toNat = v ∧ lens[k]!.toNat = w

/-- A walk from `s` to `v` of total length `L`. -/
inductive Walk (n : Nat) (first heads lens : Array UInt64) (s : Nat) : Nat → Nat → Prop
  | start : s < n → Walk n first heads lens s s 0
  | step {u v w L : Nat} : Walk n first heads lens s u L → Arc n first heads lens u v w →
      Walk n first heads lens s v (L + w)

/-- `r` holds `n` words, and word `v` is the least length of a walk from `s` to `v` when that length
is below `2^64 - 1`, and `2^64 - 1` when every walk from `s` to `v`, if any, has length `2^64 - 1`
or more. -/
def Distances (n s : Nat) (first heads lens r : Array UInt64) : Prop :=
  r.size = n ∧ ∀ v < n,
    (r[v]!.toNat < 2 ^ 64 - 1 → Walk n first heads lens s v r[v]!.toNat ∧
      ∀ L, Walk n first heads lens s v L → r[v]!.toNat ≤ L) ∧
    (r[v]!.toNat = 2 ^ 64 - 1 → ∀ L, Walk n first heads lens s v L → 2 ^ 64 - 1 ≤ L)

/-- The forward star of the request. -/
def WellFormed (n : Nat) (first heads lens : Array UInt64) : Prop :=
  n < first.size ∧ (∀ u < n, first[u]! ≤ first[u + 1]!) ∧ first[n]!.toNat ≤ heads.size ∧
    first[n]!.toNat ≤ lens.size

end Library.Graphs.Dijkstra
