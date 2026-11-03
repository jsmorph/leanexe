import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! The occurrences of a pattern in a text by the algorithm of Knuth, Morris, and Pratt, on byte
strings held eight bytes to a word.  `failure` computes, for each prefix `pat[0, q + 1)` of the
pattern, the length `pi[q]` of its longest proper prefix that is also its suffix.  The scan keeps
the length `q` of the longest prefix of the pattern shorter than `m` that ends at the current byte
of the text, and after a mismatch `fall` replaces `q` by `pi[q - 1]` until the next byte extends it
or `q` is 0.  When `q` reaches `m`, the pattern ends at the current byte, and the scan continues
from `pi[m - 1]`.  `count` counts the occurrences, and `occurrences` builds an array of that size
and fills it in a second scan. -/

namespace Library.Strings.Kmp

/-- Byte `i` of words packed eight to a word in little-endian order, as a word. -/
def byte (ws : Array UInt64) (i : UInt64) : UInt64 :=
  (ws[(i / 8).toNat]! >>> (8 * (i % 8))) &&& 255

/-- The fall-back from the matched length `k` before the byte `c`: while `0 < k` and byte `k` of the
pattern differs from `c`, `k` becomes `pi[k - 1]`.  The count `fuel` bounds the steps. -/
def fall (pat pi : Array UInt64) (c k fuel : UInt64) : UInt64 :=
  if 0 < fuel ∧ 0 < k ∧ byte pat k ≠ c then fall pat pi c pi[(k - 1).toNat]! (fuel - 1) else k
termination_by fuel.toNat
decreasing_by
  have h : 0 < fuel ∧ 0 < k ∧ byte pat k ≠ c := by assumption
  have h0 := UInt64.lt_iff_toNat_lt.mp h.1
  simp only [UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt fuel
  omega

/-- The matched length after the byte `c`, from the matched length `k`. -/
def step (pat pi : Array UInt64) (m c k : UInt64) : UInt64 :=
  let j := fall pat pi c k m
  if byte pat j = c then j + 1 else j

/-- The failure function: `pi[q]` is the length of the longest proper prefix of `pat[0, q + 1)`
that is also its suffix, for `q` below `m`. -/
def failure (pat : Array UInt64) (m : UInt64) : Array UInt64 :=
  let pi0 := LeanExe.build m fun _ => 0
  if m ≤ 1 then pi0
  else
    (LeanExe.loop (m - 1) (pi0, (0 : UInt64)) fun t st =>
      let q := t + 1
      let k := step pat st.1 m (byte pat q) st.2
      (st.1.set! q.toNat k, k)).1

/-- The number of occurrences of a nonempty pattern. -/
def count (pat pi txt : Array UInt64) (m n : UInt64) : UInt64 :=
  (LeanExe.loop n ((0 : UInt64), (0 : UInt64)) fun i st =>
    let q := step pat pi m (byte txt i) st.1
    if q = m then (pi[(m - 1).toNat]!, st.2 + 1) else (q, st.2)).2

/-- The positions of the occurrences in increasing order.  The empty pattern occurs at every
position from 0 to `n`, which takes one block of `n + 1` words when `n + 1` is a word, and a block
of `n` words extended by `n` when `n` is `2^64 - 1`, an array that no memory holds. -/
def occurrences (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64) :
    Array UInt64 :=
  if m = 0 then
    if n < 0xffffffffffffffff then LeanExe.build (n + 1) fun i => i
    else (LeanExe.build n fun i => i).push n
  else
    let pi := failure pat m
    let c := count pat pi txt m n
    (LeanExe.loop n (LeanExe.build c fun _ => (0 : UInt64), (0 : UInt64), (0 : UInt64))
      fun i st =>
        let q := step pat pi m (byte txt i) st.2.1
        if q = m then (st.1.set! st.2.2.toNat (i + 1 - m), pi[(m - 1).toNat]!, st.2.2 + 1)
        else (st.1, q, st.2.2)).1

end Library.Strings.Kmp
