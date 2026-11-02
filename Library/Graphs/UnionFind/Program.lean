import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! Equivalence classes by Knuth's Algorithm E of TAOCP §2.3.3, with elements from 0 and a root
marked as its own parent, where Knuth marks a root with the parent 0.  `root` is step E3, `merge`
steps E3 and E4 for one pair, and `forest` steps E1 and E2, which start every element as a root
and take the pairs in order.  `classes` then labels each element with the least element of its
class: it visits the elements in increasing order and records, at each root, the first element
that reaches it. -/

namespace Library.Graphs.UnionFind

/-- Step E3: the root of the tree that holds `j`, reached by the links of `parent`.  The count
`fuel` bounds the steps so that the function is total, and a call with `fuel = n` on a forest of
`n` elements never exhausts it. -/
def root (parent : Array UInt64) (j fuel : UInt64) : UInt64 :=
  if 0 < fuel then (if parent[j.toNat]! = j then j else root parent parent[j.toNat]! (fuel - 1))
  else j
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel := by assumption
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- Steps E3 and E4 for the pair `j ≡ k`: when both are elements and their roots differ, the
root of `j` becomes a child of the root of `k`. -/
def merge (n j k : UInt64) (parent : Array UInt64) : Array UInt64 :=
  if j < n then
    if k < n then
      let rj := root parent j n
      let rk := root parent k n
      if rj = rk then parent else parent.set! rj.toNat rk
    else parent
  else parent

/-- Steps E1 and E2: every element starts as a root, and the pairs `js[t] ≡ ks[t]` for `t` below
the length of the shorter array are merged in order. -/
def forest (n : UInt64) (js ks : Array UInt64) : Array UInt64 :=
  let a := js.size.toUInt64
  let b := ks.size.toUInt64
  let m := if a ≤ b then a else b
  LeanExe.loop m (LeanExe.build n fun i => i) fun t parent =>
    merge n js[t.toNat]! ks[t.toNat]! parent

/-- The least element of the class of each element below `n`. -/
def classes (n : UInt64) (js ks : Array UInt64) : Array UInt64 :=
  let parent := forest n js ks
  (LeanExe.loop n (LeanExe.build n fun _ => n, LeanExe.build n fun _ => 0) fun i s =>
    let r := root parent i n
    let least := if s.1[r.toNat]! = n then i else s.1[r.toNat]!
    (s.1.set! r.toNat least, s.2.set! i.toNat least)).2

end Library.Graphs.UnionFind
