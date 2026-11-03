import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! Least-significant-digit radix sort of an array of words, TAOCP §5.2.5, with eight passes of
distribution counting, Algorithm D of TAOCP §5.2, one for each byte from the least significant.
Each pass moves the words from one array to the other, so the eighth pass moves them into the array
that held the input, which by the compiler's ownership rules occupies the input's block, a fact that
no theorem states. -/

namespace Library.Sorting.RadixSort

/-- The byte of `x` at bit `s`. -/
def digit (s x : UInt64) : UInt64 := (x >>> s) &&& 255

/-- Steps D1 to D4 for the byte at bit `s`: for an array of 256 counts, `count[v]` becomes the
number of words of `src` whose byte is at most `v`. -/
def countDigits (s : UInt64) (src count : Array UInt64) : Array UInt64 :=
  let n := src.size.toUInt64
  let zeroed := LeanExe.loop 256 count fun v c => c.set! v.toNat 0
  let counted := LeanExe.loop n zeroed fun j c =>
    let d := digit s src[j.toNat]!
    c.set! d.toNat (c[d.toNat]! + 1)
  LeanExe.loop 255 counted fun v c => c.set! (v + 1).toNat (c[(v + 1).toNat]! + c[v.toNat]!)

/-- Steps D5 and D6: for `j` from `n - 1` down to 0, the word `src[j]` goes to position
`count[d] - 1` of `dst`, where `d` is its byte, and `count[d]` decreases. -/
def distribute (s : UInt64) (src dst count : Array UInt64) : Array UInt64 × Array UInt64 :=
  let n := src.size.toUInt64
  LeanExe.loop n (dst, count) fun k st =>
    let x := src[(n - 1 - k).toNat]!
    let d := digit s x
    let i := st.2[d.toNat]! - 1
    (st.1.set! i.toNat x, st.2.set! d.toNat i)

/-- The passes from the byte at bit `s`: each distributes `src` into `dst`, and the next pass
distributes the result back into `src`. -/
def passes (s : UInt64) (src dst count : Array UInt64) : Array UInt64 :=
  if s < 64 then
    let (out, count') := distribute s src dst (countDigits s src count)
    passes (s + 8) out src count'
  else src
termination_by 64 - s.toNat
decreasing_by
  have h : s < 64 := by assumption
  have h1 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat] at h1
  have e : (s + 8).toNat = s.toNat + 8 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]
    omega
  rw [e]
  omega

/-- The eight passes, with a second array of the size of `xs` and an array of 256 counts. -/
def radixSort (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  passes 0 xs (LeanExe.build n fun _ => 0) (LeanExe.build 256 fun _ => 0)

end Library.Sorting.RadixSort
