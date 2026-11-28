module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build
public import LeanExe.Dialect.RepeatWhile
public import Library.Numerics.Bignum.Second.Program

@[expose] public section

/-!
The third iteration of the library: Burnikel and Ziegler's recursive division, in the form of
Brent and Zimmermann's Algorithms 1.8 (RecursiveDivRem) and 1.9 (UnbalancedDivision), and the
conversion to decimal text by their Algorithm 1.26 (FastIntegerOutput), with powers of `10^9`
computed by squaring.

Every number of a division lives in one workspace, an array that each helper takes as an owned
parameter and returns, so that each update writes in place, as the second iteration's product
does.  Positions and lengths are words; a segment is the run of limbs of the workspace from a
position, least significant first.

* `baseDiv` is Brent and Zimmermann's Algorithm 1.6 (BasecaseDivRem) with Knuth's quotient
  selection: the top step subtracts the divisor once when the top limbs allow it, and then the
  first iteration's Algorithm D, with the trial digit of step D3 (`trialAt`), the
  multiply-and-subtract of step D4 (`mulSubSeg`), and the add-back of step D6, computes one
  quotient limb at a time, all in place.
* `rdiv` is Algorithm 1.8: below the threshold `T` it calls `baseDiv`, and above it divides the
  top part by the top half of the divisor, subtracts the product of that quotient by the low part
  of the divisor (`mulAcc`, Karatsuba's product in chunks, and `subFix`, which also adds the
  divisor back at most four times), and repeats with the low part.  Its quotient has `m` limbs and
  a top word of 0 or 1, since a dividend of `n + m` limbs and a normalized divisor of `n` limbs have
  a quotient below `2 β^m`.
* `udiv` is Algorithm 1.9: a dividend of `n + M` limbs is divided `n` limbs of quotient at a time,
  and the last part of fewer than `n` quotient limbs by `tdiv`, which divides the top `2 m` limbs
  by the top `m` limbs of the divisor and subtracts the rest of the product, as the steps 3 to 5 of
  Algorithm 1.8 do.
* `divSeg` normalizes the divisor and the dividend into the workspace by the factor `2^s` that
  sets the divisor's top bit, divides by `udiv`, and divides the remainder back by `2^s`.

`natDivModBZWith t T D u v` uses the first iteration's Algorithm D, in the second iteration's form
with carries by shift and mask, when the divisor or the quotient has fewer than `max D 2` limbs,
and `divSeg` otherwise.  The printer `natToTextDCWith` writes chunks of nine digits: the powers
`P_i = 10^(9·2^i)` by squaring (`powInit`), then `toChunks`, which divides a number below `P_i²`
by `P_i` with `divSeg` and converts the quotient and the remainder at level `i - 1`, down to
level `L`, where `leafChunks` divides by `10^9` repeatedly, the first iteration's quadratic
printer in place.  The text is built from the chunks as the first iteration's `intToText` builds
it.  Below `P` limbs the printer is the first iteration's `intToText`.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision (tooBig)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

/-! ## Algorithm D in place -/

/-- Step D3 for the window of `n + 1` limbs at `wp` and the divisor of `n ≥ 2` limbs at `bp`:
MultiPrecision's `trial` with offsets. -/
def trialAt (W : Array UInt64) (wp bp n : UInt64) : UInt64 :=
  let x2 := W[(wp + n).toNat]!
  let x1 := W[(wp + n - 1).toNat]!
  let x0 := W[(wp + n - 2).toNat]!
  let v1 := W[(bp + n - 1).toNat]!
  let v0 := W[(bp + n - 2).toNat]!
  let q0 := (x2 * 4294967296 + x1) / v1
  let r0 := (x2 * 4294967296 + x1) % v1
  let c0 := tooBig q0 r0 x0 v0
  let q1 := if c0 then q0 - 1 else q0
  let r1 := if c0 then r0 + v1 else r0
  if c0 ∧ r1 < 4294967296 ∧ tooBig q1 r1 x0 v0 then q1 - 1 else q1

/-- Step D4: subtracts `q` times the `n` limbs at `bp` from the `n + 1` limbs at `wp`, and returns
the final borrow. -/
def mulSubSeg (W : Array UInt64) (wp bp n q : UInt64) : UInt64 × Array UInt64 :=
  let s := LeanExe.loop (n + 1) ((0 : UInt64), (0 : UInt64), W) fun i x =>
    let p := q * (if i < n then x.2.2[(bp + i).toNat]! else 0) + x.1
    let r := x.2.2[(wp + i).toNat]! + 4294967296 - (p &&& 0xFFFFFFFF) - x.2.1
    (p >>> 32, (1 : UInt64) - (r >>> 32), x.2.2.set! (wp + i).toNat (r &&& 0xFFFFFFFF))
  (s.2.1, s.2.2)

/-- Brent and Zimmermann's Algorithm 1.6 with Knuth's steps D3, D4, and D6: the `n + m` limbs at
`ap` divided by the normalized `n ≥ 2` limbs at `bp`.  The `m` quotient limbs go to `qp` and the
top quotient word, 0 or 1, is returned; the remainder replaces the low `n` limbs at `ap`. -/
def baseDiv (W : Array UInt64) (ap bp qp n m : UInt64) : UInt64 × Array UInt64 :=
  let s := subGen W (ap + m) bp n (ap + m) n
  let W := if s.1 == 1 then (addGen s.2 (ap + m) bp n (ap + m) n).2 else s.2
  ((1 : UInt64) - s.1, LeanExe.loop m W fun e W =>
    let j := m - 1 - e
    let qh := trialAt W (ap + j) bp n
    let ms := mulSubSeg W (ap + j) bp n qh
    if ms.1 == 1 then
      (addGen ms.2 (ap + j) bp n (ap + j) (n + 1)).2.set! (qp + j).toNat (qh - 1)
    else ms.2.set! (qp + j).toNat qh)

/-! ## Algorithm 1.8 -/

/-- Chunk `j` of `mulAcc`: the product of the quotient `Q`, the `ql` limbs at `qc` plus `c β^ql`, by
the `len = min ql (k - j ql)` limbs at `bp + j ql`, copied and padded to `ql` limbs at `qc + ql`,
by Karatsuba's product to the `2 ql + 1` limbs at `qc + 2 ql`, with scratch from `qc + 4 ql + 1`,
and added to the accumulator at `ac + j ql`. -/
def mulChunk (t : UInt64) (W : Array UInt64) (bp k ql c ac qc j : UInt64) : Array UInt64 :=
  let len := if k - j * ql < ql then k - j * ql else ql
  let W := (addGen W (bp + j * ql) (bp + j * ql) 0 (qc + ql) len).2
  let W := LeanExe.loop (ql - len) W fun i W => W.set! (qc + ql + len + i).toNat 0
  let W := kara t W qc (qc + ql) (qc + 2 * ql) (qc + 4 * ql + 1) ql
  let W := W.set! (qc + 4 * ql).toNat 0
  let W := if c == 1 then (addGen W (qc + 3 * ql) (qc + ql) len (qc + 3 * ql) (ql + 1)).2 else W
  (addGen W (ac + j * ql) (qc + 2 * ql) (2 * ql + 1) (ac + j * ql) (2 * ql + 1)).2

/-- The product of the quotient `Q`, the `ql` limbs at `qp` plus `c β^ql`, by the `k ≥ 1` limbs
at `bp`, written to the `nc·ql + ql + 1` limbs at `sp + 1`, where `nc = ⌈k / ql⌉`: Karatsuba's
products of `Q` by chunks of `ql` limbs, each added at its offset.  Every other word that it
writes lies above them, in the copies of `Q` and of a chunk, the chunk's product, and its
scratch, `10 ql + 1` limbs. -/
def mulAcc (t : UInt64) (W : Array UInt64) (bp k qp ql c sp : UInt64) : Array UInt64 :=
  let nc := (k + ql - 1) / ql
  let qc := sp + 1 + nc * ql + ql + 1
  let W := LeanExe.loop (nc * ql + ql + 1) W fun i W => W.set! (sp + 1 + i).toNat 0
  LeanExe.loop nc (addGen W qp qp 0 qc ql).2 fun j W => mulChunk t W bp k ql c (sp + 1) qc j

/-- Steps 4 and 5, or 7 and 8, of Algorithm 1.8: subtracts the first `al` limbs at `sp + 1`, the
product of `mulAcc`, from the `n + 1` limbs at `rp`, and while the difference is negative, at most
four times, adds the `n` limbs of the divisor at `bp` and decreases the quotient, the `ql` limbs
at `qp` and the top word `c`, which it returns. -/
def subFix (W : Array UInt64) (rp bp n qp ql c sp al : UInt64) : UInt64 × Array UInt64 :=
  let s := subGen W rp (sp + 1) al rp (n + 1)
  let r := LeanExe.repeatWhile 4 (s.1, c, s.2.set! sp.toNat 1) (fun st => st.1 == 1) fun st =>
    let a := addGen st.2.2 rp bp n rp (n + 1)
    let d := subGen a.2 qp sp 1 qp ql
    ((1 : UInt64) - a.1, st.2.1 - d.1, d.2)
  (r.2.1, r.2.2)

/-- Steps 4 and 5 of Algorithm 1.8, or 7 and 8: the product of the quotient by the `k` limbs at
`bp` by `mulAcc`, subtracted from the `n + 1` limbs at `rp` with the corrections of `subFix`. -/
def halfStep (t : UInt64) (W : Array UInt64) (rp bp n k qp ql c sp : UInt64) :
    UInt64 × Array UInt64 :=
  subFix (mulAcc t W bp k qp ql c sp) rp bp n qp ql c sp ((k + ql - 1) / ql * ql + ql + 1)

/-- Steps 7 to 9 of Algorithm 1.8: the low half's correction, and the quotient `Q1 β^k + Q0`, with
`Q1`'s top word `c1` and `Q0`'s `c0`, for `k = ⌊m / 2⌋`. -/
def lowHalf (t : UInt64) (W : Array UInt64) (ap bp n qp sp m c1 c0 : UInt64) :
    UInt64 × Array UInt64 :=
  let r := halfStep t W ap bp n (m / 2) qp (m / 2) c0 sp
  let s := addGen (r.2.set! sp.toNat r.1) (qp + m / 2) sp 1 (qp + m / 2) (m - m / 2)
  (c1 + s.1, s.2)

/-- Algorithm 1.8: the `n + m` limbs at `ap`, `n ≥ m`, divided by the normalized `n ≥ 2` limbs at
`bp`, with `baseDiv` below `max T 3` quotient limbs.  The `m` quotient limbs go to `qp` and the top
quotient word is returned; the remainder replaces the low `n` limbs at `ap`, with zeros above it,
and the scratch is the `6 m + 9` limbs from `sp`.  The halves split at `k = ⌊m / 2⌋`. -/
def rdiv (t T : UInt64) (W : Array UInt64) (ap bp qp sp n m : UInt64) : UInt64 × Array UInt64 :=
  if hc : m < T ∨ m < 3 then baseDiv W ap bp qp n m
  else
    let r1 := rdiv t T W (ap + 2 * (m / 2)) (bp + m / 2) (qp + m / 2) sp (n - m / 2) (m - m / 2)
    let r2 := halfStep t r1.2 (ap + m / 2) bp n (m / 2) (qp + m / 2) (m - m / 2) r1.1 sp
    let r3 := rdiv t T r2.2 (ap + m / 2) (bp + m / 2) qp sp (n - m / 2) (m / 2)
    lowHalf t r3.2 ap bp n qp sp m r2.1 r3.1
termination_by m.toNat
decreasing_by
  all_goals
    have := UInt64.toNat_lt m
    simp only [not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat] at hc
    simp only [UInt64.toNat_sub, UInt64.toNat_div, UInt64.reduceToNat]
    omega

/-- The steps 3 to 5 of Algorithm 1.8 for a quotient of `m < n` limbs: the top `2 m` limbs of the
dividend divided by the top `m` limbs of the divisor, and the product of that quotient by the low
`n - m` limbs of the divisor subtracted. -/
def tdiv (t T : UInt64) (W : Array UInt64) (ap bp qp sp n m : UInt64) : UInt64 × Array UInt64 :=
  let r := rdiv t T W (ap + (n - m)) (bp + (n - m)) qp sp m m
  halfStep t r.2 ap bp n (n - m) qp m r.1 sp

/-- Algorithm 1.9: the `n + M` limbs at `ap`, below `β^M` times the normalized `n` limbs at `bp`,
divided `n` quotient limbs at a time from the top, and the last `M'` quotient limbs by `rdiv`, or by
`tdiv` when `M' < n` and `M'` is at least the threshold. -/
def udiv (t T : UInt64) (W : Array UInt64) (ap bp qp sp n M : UInt64) : Array UInt64 :=
  let c := (M - 1) / n
  let W := LeanExe.loop c W fun j W =>
    (rdiv t T W (ap + (M - n - j * n)) bp (qp + (M - n - j * n)) sp n n).2
  if n ≤ M - c * n ∨ M - c * n < T ∨ M - c * n < 3 then
    (rdiv t T W ap bp qp sp n (M - c * n)).2
  else (tdiv t T W ap bp qp sp n (M - c * n)).2

/-- The `len` limbs at `p` divided in place by the word `d`, `0 < d ≤ 2^32`, from the top limb
down, with the remainder. -/
def divSmallSeg (W : Array UInt64) (p len d : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.loop len ((0 : UInt64), W) fun e s =>
    let x := s.1 * 4294967296 + s.2[(p + len - 1 - e).toNat]!
    (x % d, s.2.set! (p + len - 1 - e).toNat (x / d))

/-- The `lx` limbs at `xp` divided by the `n ≥ 2` limbs at `dp`, whose top limb is not 0: the
`lx + 1 - n` quotient limbs go to `qp`, and the remainder replaces the low `n` limbs at `xp`, with
zeros above it.  The normalized divisor, the normalized dividend with one more limb, and the
scratch of `udiv` take the `13 n + lx + 10` limbs from `sp`. -/
def divSeg (t T : UInt64) (W : Array UInt64) (xp lx dp n qp sp : UInt64) : Array UInt64 :=
  let d := (1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits W[(dp + n - 1).toNat]!)
  let W := mulAddSeg (addGen W dp dp 0 sp n).2 sp n d 0
  let W := mulAddSeg ((addGen W xp xp 0 (sp + n) lx).2.set! (sp + n + lx).toNat 0) (sp + n)
    (lx + 1) d 0
  let W := udiv t T W (sp + n) sp qp (sp + n + lx + 1) n (lx + 1 - n)
  let s := divSmallSeg W (sp + n) n d
  LeanExe.loop (lx - n) (addGen s.2 (sp + n) (sp + n) 0 xp n).2 fun i W =>
    W.set! (xp + n + i).toNat 0

/-! ## Division of naturals and integers -/

/-- The first iteration's `natDivMod` over the second iteration's shift-carry Algorithm D. -/
@[inline] def natDivModS (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  if v.size.toUInt64 == 0 then (#[], natTrim u)
  else
    let r := divideS u v
    (natTrim (slice r 0 u.size.toUInt64), natTrim (slice r u.size.toUInt64 v.size.toUInt64))

/-- The quotient and the remainder, with `u / 0 = 0` and `u % 0 = u`: 0 and `u` when `u` is
shorter than `v`, Algorithm D when the divisor or the quotient has fewer than `max D 2` limbs,
and otherwise `divSeg` in a workspace of `3 m + 15 n + 11` limbs for operands of `m` and `n`
limbs.  It follows Lean's convention at a zero divisor, so it is expanded into the exports that
return a status rather than exported. -/
@[inline] def natDivModBZWith (t T D : UInt64) (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  let n := v.size.toUInt64
  let lu := u.size.toUInt64
  if lu < n then (#[], natTrim u)
  else if n < 2 ∨ n < D ∨ lu < n + D ∨ lu < n + 2 then natDivModS u v
  else
    let W := LeanExe.build (3 * lu + 15 * n + 11) fun i =>
      if i < lu then u[i.toNat]! else if i < lu + n then v[(i - lu).toNat]! else 0
    let W := divSeg t T W 0 lu lu n (lu + n) (2 * lu + 1)
    (trimSeg W (lu + n) (lu + 1 - n), trimSeg W 0 n)

/-- The base case of the recursive division, `baseDiv` below 32 quotient limbs, and the length of
the divisor and the quotient below which the division is the first iteration's Algorithm D, 192
limbs, from the timings of the compiled module. -/
def divBase : UInt64 := 32

def divThreshold : UInt64 := 192

@[inline] def natDivModBZ (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  natDivModBZWith karaThreshold divBase divThreshold u v

/-- The status 1 and two zeros for a zero divisor, and otherwise the status 0, the quotient, and
the remainder, with the thresholds as parameters. -/
def natDivModCheckedBZWith (t T D : UInt64) (u v : Array UInt64) :
    UInt64 × Array UInt64 × Array UInt64 :=
  if v.size.toUInt64 == 0 then (1, #[], #[])
  else
    let qr := natDivModBZWith t T D u v
    (0, qr.1, qr.2)

/-- The status 1 and two zeros for a zero divisor, and otherwise the status 0, the quotient, and
the remainder. -/
def natDivModCheckedBZ (u v : Array UInt64) : UInt64 × Array UInt64 × Array UInt64 :=
  natDivModCheckedBZWith karaThreshold divBase divThreshold u v

/-- The signs of the truncated division: the quotient's from both signs, the remainder's from the
dividend's, after the first iteration's `intTDivMod`, with the status 0. -/
def signTDiv (xn yn : Bool) (q r : Array UInt64) : UInt64 × BigInt × BigInt :=
  (0, ⟨(xn != yn) && q.size.toUInt64 != 0, q⟩, ⟨xn && r.size.toUInt64 != 0, r⟩)

/-- The Euclidean quotient and remainder from the truncated ones, after the first iteration's
`intEDivMod`, with the status 0: one step of the quotient away from zero and the remainder
`|y| - |r|` when the remainder is negative and the divisor, of magnitude `ym`, is not 0. -/
def signEDiv (xn yn : Bool) (ym q r : Array UInt64) : UInt64 × BigInt × BigInt :=
  if (xn && r.size.toUInt64 != 0) && ym.size.toUInt64 != 0 then
    (0, ⟨!yn, natAdd q #[1]⟩, ⟨false, (natSub ym r).2⟩)
  else (0, ⟨(xn != yn) && q.size.toUInt64 != 0, q⟩, ⟨xn && r.size.toUInt64 != 0, r⟩)

/-- Truncated division with the statuses of the first iteration's `intTDivModChecked`. -/
def intTDivModCheckedBZ (x y : BigInt) : UInt64 × BigInt × BigInt :=
  if y.mag.size.toUInt64 == 0 then (1, ⟨false, #[]⟩, ⟨false, #[]⟩)
  else
    let r := natDivModCheckedBZ x.mag y.mag
    signTDiv x.neg y.neg r.2.1 r.2.2

/-- Euclidean division with the statuses of the first iteration's `intEDivModChecked`. -/
def intEDivModCheckedBZ (x y : BigInt) : UInt64 × BigInt × BigInt :=
  if y.mag.size.toUInt64 == 0 then (1, ⟨false, #[]⟩, ⟨false, #[]⟩)
  else
    let r := natDivModCheckedBZ x.mag y.mag
    signEDiv x.neg y.neg y.mag r.2.1 r.2.2

/-! ## Conversion to decimal text -/

/-- The `K` chunks of nine digits of the `len` limbs at `p`, least significant first, to the `K`
words at `cp`: `K` divisions by `10^9` in place, each over the limbs below the top zero limbs. -/
def leafChunks (W : Array UInt64) (p len cp K : UInt64) : Array UInt64 :=
  (LeanExe.loop K (len, W) fun j st =>
    let s := divSmallSeg st.2 p st.1 1000000000
    let W := s.2.set! (cp + j).toNat s.1
    let top := W[(p + st.1 - 1).toNat]!
    (if st.1 != 0 ∧ top = 0 then st.1 - 1 else st.1, W)).2

/-- The powers `P_i = 10^(9·2^i)` for `i ≤ K`, `P_0` at `pb` and each square after the power it
squares: the table at `tb` holds the position of `P_i` at `tb + 2 i` and its number of limbs at
`tb + 2 i + 1`. -/
def powInit (t : UInt64) (W : Array UInt64) (tb pb K : UInt64) : Array UInt64 :=
  LeanExe.loop K (((W.set! pb.toNat 1000000000).set! tb.toNat pb).set! (tb + 1).toNat 1)
    fun i W =>
      let p := W[(tb + 2 * i).toNat]!
      let n := W[(tb + 2 * i + 1).toNat]!
      let W := kara t W p p (p + n) (p + 3 * n) n
      let top := W[(p + 3 * n - 1).toNat]!
      (W.set! (tb + 2 * i + 2).toNat (p + n)).set! (tb + 2 * i + 3).toNat
        (if top = 0 then 2 * n - 1 else 2 * n)

/-- Algorithm 1.26 at level `i`: the `2 n_i` limbs at `p`, below `P_i²`, written as `2^(i+1)`
chunks of nine digits to `cp`.  With `sl` the number's significant limbs, a number below
`β^(n_i)` has the quotient 0 and is converted at level `i - 1` with `2^i` zero chunks above it, and
any other number is divided by `P_i` and the quotient and the remainder are converted at level
`i - 1`, down to level `max L 0`, where `leafChunks` writes the chunks.  The quotient and the
scratch take the words from `fp`. -/
def toChunks (t T L : UInt64) (W : Array UInt64) (tb i p cp fp : UInt64) : Array UInt64 :=
  let n := W[(tb + 2 * i + 1).toNat]!
  let dp := W[(tb + 2 * i).toNat]!
  let sl := LeanExe.loop (2 * n) (0 : UInt64) fun j k => if W[(p + j).toNat]! = 0 then k else j + 1
  if hc : i ≤ L ∨ i = 0 then leafChunks W p sl cp ((2 : UInt64) <<< i)
  else if sl < n then
    toChunks t T L (LeanExe.loop ((1 : UInt64) <<< i) W fun j W =>
      W.set! (cp + ((1 : UInt64) <<< i) + j).toNat 0) tb (i - 1) p cp fp
  else
    let W := divSeg t T W p sl dp n fp (fp + n + 1)
    let W := LeanExe.loop (2 * n - sl) W fun j W => W.set! (fp + (sl - n + 1) + j).toNat 0
    let W := toChunks t T L W tb (i - 1) fp (cp + ((1 : UInt64) <<< i)) (fp + n + 1)
    toChunks t T L W tb (i - 1) p cp fp
termination_by i.toNat
decreasing_by
  all_goals
    simp only [not_or, UInt64.not_le, UInt64.lt_iff_toNat_lt] at hc
    have : i.toNat ≠ 0 := fun h => hc.2 (UInt64.toNat_inj.mp (by simpa using h))
    simp only [UInt64.toNat_sub_of_le i 1 (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega

/-- The least `K` with `2^(K+1) ≥ c`, for `c ≤ 2^40`. -/
@[inline] def levelsFor (c : UInt64) : UInt64 :=
  LeanExe.repeatWhile 40 (0 : UInt64) (fun k => (2 : UInt64) <<< k < c) fun k => k + 1

/-- The text of `K` chunks of nine digits at `cp`, with `-` for `neg`: the first iteration's
`intToText` over a copy of the chunks. -/
def textOfChunks (neg : Bool) (W : Array UInt64) (cp K : UInt64) : Array UInt64 :=
  let c := LeanExe.build K fun i => W[(cp + i).toNat]!
  let sc := Library.Numerics.MultiPrecision.significant c
  let t := if sc == 0 then 0 else sc - 1
  let sign : UInt64 := if neg then 1 else 0
  let len := sign + digitCount c[t.toNat]! + 9 * t
  LeanExe.build len fun i =>
    if i < sign then 45 else digitByte c[((len - 1 - i) / 9).toNat]! ((len - 1 - i) % 9)

/-- The chunks of nine digits of `u`, by Algorithm 1.26 from level `K`, the least with
`2^(K+1) ≥ n + n / 14 + 2` for `n` limbs, in a workspace of `31·2^K + 2 K + 22` words: the table
at 0, the `2^(K+1)` chunks after it, the powers, the number, and the frames of `toChunks`. -/
def chunksDC (t T L : UInt64) (u : Array UInt64) : Array UInt64 :=
  let n := u.size.toUInt64
  let K := levelsFor (n + n / 14 + 2)
  let cp := 2 * K + 2
  let pb := cp + ((2 : UInt64) <<< K)
  let xp := pb + 7 * ((1 : UInt64) <<< K)
  let W := LeanExe.build (xp + 22 * ((1 : UInt64) <<< K) + 20) fun i =>
    if xp ≤ i ∧ i < xp + n then u[(i - xp).toNat]! else 0
  let W := powInit t W 0 pb K
  toChunks t T L W 0 K xp cp (xp + 2 * W[(2 * K + 1).toNat]!)

/-- The decimal text of the value of `u`, by Algorithm 1.26 from `P` limbs on and by the first
iteration's printer below. -/
def natToTextDCWith (t T L P : UInt64) (u : Array UInt64) : Array UInt64 :=
  if u.size.toUInt64 < P then intToText ⟨false, u⟩
  else
    let K := levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)
    textOfChunks false (chunksDC t T L u) (2 * K + 2) ((2 : UInt64) <<< K)

/-- The level of the leaves of the printer's recursion and the length from which the printer
uses Algorithm 1.26, from the timings of the compiled module. -/
def printLeaf : UInt64 := 5

def printThreshold : UInt64 := 32

def natToTextDC (u : Array UInt64) : Array UInt64 :=
  natToTextDCWith karaThreshold divBase printLeaf printThreshold u

/-- The decimal text of `x`, with `-` for a negative sign. -/
def intToTextDC (x : BigInt) : Array UInt64 :=
  if x.mag.size.toUInt64 < printThreshold then intToText x
  else
    let K := levelsFor (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2)
    textOfChunks x.neg (chunksDC karaThreshold divBase printLeaf x.mag) (2 * K + 2)
      ((2 : UInt64) <<< K)

end Library.Numerics.Bignum
