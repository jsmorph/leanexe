import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! The primes below a word `N` by the sieve of Eratosthenes.  `marks` holds a flag for each number
below `N`, and `sieveFrom` sets the flags of the multiples `p·p`, `p·p + p`, … below `N` of each
`p` from 2 with `p·p < N` whose flag is unset, which leaves unset exactly the flags of 0, 1, and
the primes.  `countUnmarked` counts the unset flags from 2, and `primes` builds an array of that
size and fills it with those numbers in increasing order. -/

namespace Library.Numerics.Arithmetic.Sieve

/-- The flags of `p·p`, `p·p + p`, … below `N` set, for `p·p < N` as numbers: then `p·p` fits in a
word, and the last multiple, `p·p + ((N - 1 - p·p) / p)·p`, is below `N`, so no index wraps. -/
def crossOff (p N : UInt64) (marks : Array Bool) : Array Bool :=
  LeanExe.loop ((N - 1 - p * p) / p + 1) marks fun k acc => acc.set! (p * p + k * p).toNat true

/-- The sieve from `p`: while `p < N` and `p·p < N`, tested as `p ≤ (N - 1) / p`, which forms no
product, the flags of the multiples of `p` from `p·p` below `N` are set when the flag of `p` is
unset.  `N - 1` wraps for `N = 0`, where the test `p < N` fails. -/
def sieveFrom (p N : UInt64) (marks : Array Bool) : Array Bool :=
  if p < N ∧ p ≤ (N - 1) / p then
    if marks[p.toNat]! then sieveFrom (p + 1) N marks
    else sieveFrom (p + 1) N (crossOff p N marks)
  else marks
termination_by N.toNat - p.toNat
decreasing_by
  all_goals
    have h : p < N ∧ p ≤ (N - 1) / p := by assumption
    have h1 := UInt64.lt_iff_toNat_lt.mp h.1
    have e : (p + 1).toNat = p.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]
      have := UInt64.toNat_lt N
      omega
    rw [e]
    omega

/-- The number of unset flags from 2 below `N`. -/
def countUnmarked (N : UInt64) (marks : Array Bool) : UInt64 :=
  LeanExe.loop N 0 fun k c => if 2 ≤ k ∧ marks[k.toNat]! = false then c + 1 else c

/-- The primes below `N`: the sieve's flags, then an array of `countUnmarked` words filled with the
numbers from 2 whose flags are unset, each at the count of those before it. -/
def primes (N : UInt64) : Array UInt64 :=
  let marks := sieveFrom 2 N (LeanExe.build N fun _ => false)
  let count := countUnmarked N marks
  (LeanExe.loop N (LeanExe.build count fun _ => (0 : UInt64), (0 : UInt64)) fun k st =>
    if 2 ≤ k ∧ marks[k.toNat]! = false then (st.1.set! st.2.toNat k, st.2 + 1) else st).1

end Library.Numerics.Arithmetic.Sieve
