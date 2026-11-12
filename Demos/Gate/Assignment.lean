import LeanExe.Dialect.Loop

/-!
The check of an optimal assignment.  `check c perm u v` reads an `n × n` matrix of `Int64` costs
`c` in row-major order, in which the value `2⁶³ - 1` forbids a pair, a proposed assignment `perm`
that gives row `i` the column `perm[i]`, and a dual certificate `u`, `v`.  It accepts when the
certificate's values lie in `(-2⁶², 2⁶²)`, the assignment is a permutation of `{0, …, n - 1}`
through allowed pairs with `u[i] + v[perm[i]] = c[i·n + perm[i]]` for every row, and
`u[i] + v[j] ≤ c[i·n + j]` for every allowed pair.  By weak duality the assignment then has the
least total cost of any permutation through allowed pairs.  Three passes check the conditions and
stop at the first failure, which the result's status, row, and column name.  The limit of 16,384
on `n` keeps the costs below the `2²⁹` words of the largest array that the verified compiler's
code admits.
-/

namespace Demos.Gate.Assignment

/-- The status and the position of the first failure: status 0 for an accepted assignment, 1 for
a size outside the range, 2 for a dual value outside `(-2⁶², 2⁶²)`, 3 for an assignment that is
not a permutation through allowed pairs, 4 for a violated dual inequality, and 5 for a row whose
pair is not tight. -/
structure Check where
  status : UInt64
  row : UInt64
  col : UInt64
  deriving Inhabited

/-- The cost that forbids a pair, `2⁶³ - 1`. -/
abbrev forbidden : Int64 := 9223372036854775807

/-- Whether `-2⁶² < w < 2⁶²`. -/
def inRange (w : Int64) : Bool := -4611686018427387904 < w && w < 4611686018427387904

/-- Pass 1: the values of `u` and `v` lie in `(-2⁶², 2⁶²)`. -/
def ranges (u v : Array Int64) (n : UInt64) : Check :=
  LeanExe.loop n ⟨0, 0, 0⟩ fun i r =>
    if r.status == 0 then
      if inRange u[i.toNat]! && inRange v[i.toNat]! then r else ⟨2, i, 0⟩
    else r

/-- Pass 2: each row's column lies below `n`, its pair is allowed, and its pair is tight. -/
def rows (c : Array Int64) (perm : Array UInt64) (u v : Array Int64) (n : UInt64) (r : Check) :
    Check :=
  LeanExe.loop n r fun i r =>
    if r.status == 0 then
      let j := perm[i.toNat]!
      if j < n then
        let w := c[(i * n + j).toNat]!
        if w != forbidden then
          if u[i.toNat]! + v[j.toNat]! == w then r else ⟨5, i, j⟩
        else ⟨3, i, j⟩
      else ⟨3, i, j⟩
    else r

/-- Pass 3, over `t = i·n + j`: rows `i < j` have different columns, and `u[i] + v[j] ≤ c[t]`.
The test needs no exception for a forbidden pair, since `u[i] + v[j] < 2⁶³ - 1` for values in
range. -/
def pairs (c : Array Int64) (perm : Array UInt64) (u v : Array Int64) (n : UInt64) (r : Check) :
    Check :=
  LeanExe.loop (n * n) r fun t r =>
    if r.status == 0 then
      let i := t / n
      let j := t % n
      if i < j && perm[i.toNat]! == perm[j.toNat]! then ⟨3, j, perm[j.toNat]!⟩
      else
        if c[t.toNat]! < u[i.toNat]! + v[j.toNat]! then ⟨4, i, j⟩ else r
    else r

/-- The check of the assignment `perm` against the costs `c` and the certificate `u`, `v`. -/
def check (c : Array Int64) (perm : Array UInt64) (u v : Array Int64) : Check :=
  let n := perm.size.toUInt64
  if 1 ≤ n ∧ n ≤ 16384 ∧ c.size.toUInt64 = n * n ∧ u.size.toUInt64 = n ∧ v.size.toUInt64 = n then
    pairs c perm u v n (rows c perm u v n (ranges u v n))
  else ⟨1, 0, 0⟩

end Demos.Gate.Assignment
