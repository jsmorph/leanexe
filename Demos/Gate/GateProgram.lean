import Library.Numerics.Interval.Functions
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-!
The gate.  `gate nu s g` checks an innovation `nu` of `d` values and a covariance `s` of `d·d`
values in row-major order, eliminates the covariance and the innovation symmetrically in interval
arithmetic, and returns an interval of the squared Mahalanobis distance `ν' S⁻¹ ν` with its
verdict against the threshold `g`.  Each step requires a pivot interval above zero, which shows
the covariance positive definite, adds `r_k² / p_k` to the distance, and subtracts multiples of
row `k` from the later rows, with the new matrix and right-hand side built as new arrays.
-/

namespace Demos.Gate

open Library.Numerics.Bounds Library.Numerics.Interval

/-- The state of the elimination: a status, the matrix `a` of `d·d` intervals in row-major order,
the right-hand side `r` of `d` intervals, and the sum of `r_k² / p_k` over the steps so far.
Status 1 marks a pivot that is rejected or not shown above zero. -/
structure Elim where
  status : UInt64
  a : Array Interval
  r : Array Interval
  acc : Interval
  deriving Inhabited

/-- The result of the gate: status 0 with the interval `[lo, hi]` of the squared Mahalanobis
distance and the verdict, status 1 for a rejected input, and status 2 for a covariance that the
elimination does not show positive definite or an interval operation that rejects. -/
structure Gate where
  status : UInt64
  lo : Float
  hi : Float
  verdict : UInt64
  deriving Inhabited

/-- Whether the first `n` values of `xs` are finite. -/
def allFinite (xs : Array Float) (n : UInt64) : Bool :=
  LeanExe.loop n true fun t ok => ok && finite xs[t.toNat]!

/-- Whether `s[i·d + j]` and `s[j·d + i]` are each at most the other, for all `i, j < d`. -/
def symmetric (s : Array Float) (d : UInt64) : Bool :=
  LeanExe.loop (d * d) true fun t ok =>
    let u := s[t.toNat]!
    let w := s[(t % d * d + t / d).toNat]!
    ok && u ≤ w && w ≤ u

/-- Step `k` of the elimination: with the pivot `p = a[k·d + k]` accepted and above zero, it
subtracts `(a[i·d + k] / p) · a[j·d + k]` from `a[i·d + j]` and `(a[i·d + k] / p) · r[k]` from
`r[i]` for `i, j > k`, and adds `r[k]² / p` to the sum. -/
def elimStep (d k : UInt64) (e : Elim) : Elim :=
  if e.status == 0 then
    let p := e.a[(k * d + k).toNat]!
    if p.status == 0 && 0.0 < p.lo then
      ⟨0,
        LeanExe.build (d * d) fun t =>
          if k < t / d && k < t % d then
            sub e.a[t.toNat]! (mul (div e.a[(t / d * d + k).toNat]! p) e.a[(t % d * d + k).toNat]!)
          else e.a[t.toNat]!,
        LeanExe.build d fun i =>
          if k < i then sub e.r[i.toNat]! (mul (div e.a[(i * d + k).toNat]! p) e.r[k.toNat]!)
          else e.r[i.toNat]!,
        add e.acc (div (sq e.r[k.toNat]!) p)⟩
    else ⟨1, e.a, e.r, e.acc⟩
  else e

/-- `d` steps of elimination from the points of `s` and `nu`. -/
def eliminate (s nu : Array Float) (d : UInt64) : Elim :=
  LeanExe.loop d
    ⟨0, LeanExe.build (d * d) fun t => point s[t.toNat]!, LeanExe.build d fun i => point nu[i.toNat]!,
      point 0.0⟩
    fun k e => elimStep d k e

/-- The gate for the innovation `nu` of `d` values, the covariance `s` of `d·d` values in
row-major order, and the threshold `g`: an interval of the squared Mahalanobis distance and its
verdict against `g`, 1 when the interval lies at or below `g`, 2 when it lies above `g`, and 0
otherwise. -/
def gate (nu s : Array Float) (g : Float) : Gate :=
  let d := nu.size.toUInt64
  if 1 ≤ d ∧ d ≤ 64 ∧ s.size.toUInt64 = d * d then
    if finite g && 0.0 ≤ g && allFinite nu d && allFinite s (d * d) && symmetric s d then
      let e := eliminate s nu d
      if e.status == 0 && e.acc.status == 0 then
        let q := clamp e.acc 0.0 e.acc.hi
        if q.status == 0 then
          let v : UInt64 := if q.hi ≤ g then 1 else if g < q.lo then 2 else 0
          ⟨0, q.lo, q.hi, v⟩
        else ⟨2, 0.0, 0.0, 0⟩
      else ⟨2, 0.0, 0.0, 0⟩
    else ⟨1, 0.0, 0.0, 0⟩
  else ⟨1, 0.0, 0.0, 0⟩

end Demos.Gate
