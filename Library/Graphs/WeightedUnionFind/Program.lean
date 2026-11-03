import Library.Graphs.UnionFind.Program

/-! Equivalence classes by the trees of Algorithm E of TAOCP §2.3.3 with path compression and union
by size, as Tarjan analyzed them in 1975.  `root` is the step of Algorithm E that follows the links
to a root, `compress` gives every element on the path from `j` the root as parent, `unite` makes the
root whose recorded size is smaller a child of the other root, and `forest` takes the pairs in
order.  `classes` labels each element with the least element of its class, as the module of
Algorithm E does. -/

namespace Library.Graphs.WeightedUnionFind

open Library.Graphs.UnionFind (root)

/-- Path compression: when `r` is the root of `j`, every element on the path from `j` to `r` gets
the parent `r`, as far as the count `fuel` of steps reaches, and `unite` passes the count `n`, which
covers every path of a forest of `n` elements.  `compress_spec` states only that each element keeps
its parent or gets its root. -/
def compress (parent : Array UInt64) (j r fuel : UInt64) : Array UInt64 :=
  if 0 < fuel then
    if j = r then parent
    else
      let next := parent[j.toNat]!
      compress (parent.set! j.toNat r) next r (fuel - 1)
  else parent
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel := by assumption
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- The pair `j ≡ k`: when both are elements, both paths are compressed, and when the roots differ,
the root whose recorded size is smaller becomes a child of the other root, whose recorded size grows
by the smaller one.  With equal sizes, the root of `k` becomes a child of the root of `j`.  The
recorded size at each root is the number of elements of its tree, a fact that no theorem states. -/
def unite (n j k : UInt64) (parent size : Array UInt64) : Array UInt64 × Array UInt64 :=
  if j < n ∧ k < n then
    let rj := root parent j n
    let rk := root parent k n
    let p := compress (compress parent j rj n) k rk n
    if rj = rk then (p, size)
    else
      let sj := size[rj.toNat]!
      let sk := size[rk.toNat]!
      if sj < sk then (p.set! rj.toNat rk, size.set! rk.toNat (sk + sj))
      else (p.set! rk.toNat rj, size.set! rj.toNat (sj + sk))
  else (parent, size)

/-- Every element starts as a root of a tree of size 1, and the pairs `js[t] ≡ ks[t]` for `t` below
the length of the shorter array are united in order. -/
def forest (n : UInt64) (js ks : Array UInt64) : Array UInt64 :=
  let a := js.size.toUInt64
  let b := ks.size.toUInt64
  let m := if a ≤ b then a else b
  (LeanExe.loop m (LeanExe.build n fun i => i, LeanExe.build n fun _ => 1) fun t st =>
    unite n js[t.toNat]! ks[t.toNat]! st.1 st.2).1

/-- The least element of the class of each element below `n`. -/
def classes (n : UInt64) (js ks : Array UInt64) : Array UInt64 :=
  let parent := forest n js ks
  (LeanExe.loop n (LeanExe.build n fun _ => n, LeanExe.build n fun _ => 0) fun i s =>
    let r := root parent i n
    let least := if s.1[r.toNat]! = n then i else s.1[r.toNat]!
    (s.1.set! r.toNat least, s.2.set! i.toNat least)).2

end Library.Graphs.WeightedUnionFind
