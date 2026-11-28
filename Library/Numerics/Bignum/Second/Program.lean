module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build
public import LeanExe.Dialect.RepeatWhile
public import Library.Numerics.Bignum.Program

@[expose] public section

namespace Library.Numerics.Bignum

/-- The sum of the `n` words of `W` from `xp` and the first `min k n` words from `yp`, written
over the `n` words from `dp`, with the final carry. -/
def addGen (W : Array UInt64) (xp yp k dp n : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.loop n ((0 : UInt64), W) fun i s =>
    let t : UInt64 := s.2[(xp + i).toNat]! + (if i < k then s.2[(yp + i).toNat]! else 0) + s.1
    (t >>> 32, s.2.set! (dp + i).toNat (t &&& 0xFFFFFFFF))

/-- The difference of the `n` words of `W` from `xp` and the first `min k n` words from `yp`,
written over the `n` words from `dp`, with the final borrow. -/
def subGen (W : Array UInt64) (xp yp k dp n : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.loop n ((0 : UInt64), W) fun i s =>
    let t : UInt64 :=
      s.2[(xp + i).toNat]! + 4294967296 - (if i < k then s.2[(yp + i).toNat]! else 0) - s.1
    ((1 : UInt64) - (t >>> 32), s.2.set! (dp + i).toNat (t &&& 0xFFFFFFFF))

/-- Algorithm M in place: the `ma + nb` limbs from `rp` receive the product of the `ma` limbs
from `ap` and the `nb` limbs from `bp`. -/
def baseMul (W : Array UInt64) (ap ma bp nb rp : UInt64) : Array UInt64 :=
  LeanExe.loop nb (LeanExe.loop (ma + nb) W fun i W => W.set! (rp + i).toNat 0) fun j W =>
    let y := W[(bp + j).toNat]!
    let s := LeanExe.loop ma ((0 : UInt64), W) fun i s =>
      let t := s.2[(ap + i).toNat]! * y + s.2[(rp + i + j).toNat]! + s.1
      (t >>> 32, s.2.set! (rp + i + j).toNat (t &&& 0xFFFFFFFF))
    s.2.set! (rp + j + ma).toNat s.1

/-- Karatsuba's product in place. -/
def kara (t : UInt64) (W : Array UInt64) (ap bp rp tp n : UInt64) : Array UInt64 :=
  if hc : n < t ∨ n < 16 then baseMul W ap n bp n rp
  else
    let h := n - n / 2
    let l := n / 2
    let W := kara t W ap bp rp tp h
    let W := kara t W (ap + h) (bp + h) (rp + 2 * h) tp l
    let s := addGen W ap (ap + h) l tp h
    let W := s.2.set! (tp + h).toNat s.1
    let s := addGen W bp (bp + h) l (tp + h + 1) h
    let W := s.2.set! (tp + 2 * h + 1).toNat s.1
    let W := kara t W tp (tp + h + 1) (tp + 2 * h + 2) (tp + 4 * h + 4) (h + 1)
    let W := (subGen W (tp + 2 * h + 2) rp (2 * h) (tp + 2 * h + 2) (2 * h + 2)).2
    let W := (subGen W (tp + 2 * h + 2) (rp + 2 * h) (2 * l) (tp + 2 * h + 2) (2 * h + 2)).2
    (addGen W (rp + h) (tp + 2 * h + 2) (2 * h + 2) (rp + h) (2 * n - h)).2
termination_by n.toNat
decreasing_by
  all_goals
    have := UInt64.toNat_lt n
    simp only [not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat] at hc
    simp only [UInt64.toNat_sub, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega

/-- The canonical limbs of the `len` words of `W` from `p`. -/
def trimSeg (W : Array UInt64) (p len : UInt64) : Array UInt64 :=
  let k := LeanExe.loop len (0 : UInt64) fun i k => if W[(p + i).toNat]! = 0 then k else i + 1
  LeanExe.build k fun i => W[(p + i).toNat]!

/-- The product of `u` and `v`, `u` at least as long as `v`, with the threshold `t`. -/
@[inline] def mulLong (t : UInt64) (u v : Array UInt64) : Array UInt64 :=
  let m := u.size.toUInt64
  let n := v.size.toUInt64
  if n < t ∨ n < 16 then
    let W := LeanExe.build (2 * (m + n)) fun i =>
      if i < m then u[i.toNat]! else if i < m + n then v[(i - m).toNat]! else 0
    trimSeg (baseMul W 0 m m n (m + n)) (m + n) (m + n)
  else
    let q := (m + n - 1) / n
    let B := q * n
    let R := B + n
    let T := R + B + n
    let S := T + 2 * n
    let W := LeanExe.build (S + 6 * n) fun i =>
      if i < m then u[i.toNat]! else if B ≤ i ∧ i < R then v[(i - B).toNat]! else 0
    let W := LeanExe.loop q W fun c W =>
      let len := if c + 1 < q then n else m - c * n
      if len < t ∨ len < 16 then
        let W := baseMul W (c * n) len B n T
        (addGen W (R + c * n) T (len + n) (R + c * n) (len + n)).2
      else
        let W := kara t W (c * n) B T S n
        (addGen W (R + c * n) T (2 * n) (R + c * n) (2 * n)).2
    trimSeg W R (m + n)

def natMulKaraWith (t : UInt64) (u v : Array UInt64) : Array UInt64 :=
  if u.size.toUInt64 < v.size.toUInt64 then mulLong t v u else mulLong t u v

/-- The threshold of Karatsuba's method, in limbs, from the timings of the compiled module. -/
def karaThreshold : UInt64 := 48

def natMulKara (u v : Array UInt64) : Array UInt64 := natMulKaraWith karaThreshold u v

def intMulKara (x y : BigInt) : BigInt :=
  let p := natMulKara x.mag y.mag
  ⟨(x.neg != y.neg) && p.size.toUInt64 != 0, p⟩

/-! ## Decimal reading by divide and conquer -/

/-- The value of chunk `k` of nine digits of the text, most significant chunk first, with `pad`
leading zeros: the loop of the first iteration's `decimalValue`. -/
@[inline] def chunkValue (s : Array UInt64) (start pad k : UInt64) : UInt64 :=
  LeanExe.loop 9 (0 : UInt64) fun e v =>
    10 * v + (if 9 * k + e < pad then 0 else s[(start + (9 * k + e - pad)).toNat]! - 48)

/-- The `len` limbs of `W` from `p` times `m`, plus `a`, in place, without the final carry. -/
def mulAddSeg (W : Array UInt64) (p len m a : UInt64) : Array UInt64 :=
  (LeanExe.loop len (a, W) fun i st =>
    let x := st.2[(p + i).toNat]! * m + st.1
    (x >>> 32, st.2.set! (p + i).toNat (x &&& 0xFFFFFFFF))).2

/-- The workspace of the reader: the `N = e0 P2` limbs of the `P2` base elements, each the value
of `e0` chunks of nine digits read by Horner's rule, `10^(9 e0)` at position `N`, and zeros up to
`6 N` limbs. -/
def readInit (s : Array UInt64) (start count C e0 N : UInt64) : Array UInt64 :=
  let pad := 9 * C - count
  let W := LeanExe.loop (N / e0)
      (LeanExe.build (if e0 < N then 6 * N else N) fun _ => (0 : UInt64)) fun k W =>
    LeanExe.loop e0 W fun j W =>
      let i := (k + 1) * e0 - 1 - j
      mulAddSeg W (k * e0) (j + 1) 1000000000
        (if i < C then chunkValue s start pad (C - 1 - i) else 0)
  if e0 < N then LeanExe.loop e0 (W.set! N.toNat 1) fun j W => mulAddSeg W N (j + 1) 1000000000 0
  else W

/-- One pass of the reader at element size `e`: each pair of elements `l0`, `l1` becomes
`l0 + 10^(9 e) l1`, and `10^(9 e)` is squared when a later pass needs it. -/
def readPass (t : UInt64) (W : Array UInt64) (N e0 e : UInt64) : Array UInt64 :=
  let W := LeanExe.loop (N / e / 2) W fun k W =>
    let W := kara t W ((2 * k + 1) * e) (N + e - e0) (2 * N) (3 * N) e
    (addGen W (2 * N) (2 * k * e) e (2 * k * e) (2 * e)).2
  if 2 * e < N then kara t W (N + e - e0) (N + e - e0) (N + 2 * e - e0) (3 * N) e else W

/-- The canonical limbs of the value of the `count` decimal digits of `s` from `start`, by
Brent and Zimmermann's Algorithm 1.25 from base elements of `e0 ≤ max E 1` chunks: `P2` base
elements of `e0` chunks in `N = e0 P2` limbs, then passes that combine adjacent pairs with the
threshold `t` of the product, until one element remains. -/
def decimalValueDC (t E : UInt64) (s : Array UInt64) (start count : UInt64) : Array UInt64 :=
  let C := (count + 8) / 9
  let P2 := LeanExe.repeatWhile 32 (1 : UInt64) (fun p => E * p < C) fun p => 2 * p
  let e0 := (C + P2 - 1) / P2
  let N := e0 * P2
  let W := (LeanExe.repeatWhile 32 (e0, readInit s start count C e0 N) (fun st => st.1 < N)
    fun st => (2 * st.1, readPass t st.2 N e0 st.1)).2
  trimSeg W 0 N

def natOfTextDCWith (t E : UInt64) (s : Array UInt64) : Bool × Array UInt64 :=
  let n := s.size.toUInt64
  if n == 0 then (false, #[])
  else if allDigits s 0 n && (s[(0 : UInt64).toNat]! != 48 || n == 1) then
    (true, decimalValueDC t E s 0 n)
  else (false, #[])

/-- The bound on the reader's base elements, in chunks of nine digits, from the timings of the
compiled module. -/
def readBase : UInt64 := 768

def natOfTextDC (s : Array UInt64) : Bool × Array UInt64 := natOfTextDCWith karaThreshold readBase s

def intOfTextDC (s : Array UInt64) : Bool × BigInt :=
  let n := s.size.toUInt64
  if n == 0 then (false, ⟨false, #[]⟩)
  else
    let neg := s[(0 : UInt64).toNat]! == 45
    let start : UInt64 := if neg then 1 else 0
    let count := n - start
    if count == 0 then (false, ⟨false, #[]⟩)
    else if allDigits s start count && (s[start.toNat]! != 48 || (count == 1 && !neg)) then
      (true, ⟨neg, decimalValueDC karaThreshold readBase s start count⟩)
    else (false, ⟨false, #[]⟩)

/-! ## New versions of the first iteration's natural functions

Algorithms A, S, and D of MultiPrecision with the carries and borrows by `>>> 32` and
`&&& 0xFFFFFFFF`, each word computed once, and the first iteration's `natAdd`, `natSub`, and
`natDivModChecked` over them.  `Loops.lean` proves each equal to its first-iteration function. -/

def addS (u v : Array UInt64) : Array UInt64 :=
  let s := LeanExe.loop (Library.Numerics.MultiPrecision.width u v)
      ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    let t := u[j.toNat]! + v[j.toNat]! + s.1
    (t >>> 32, s.2.push (t &&& 0xFFFFFFFF))
  s.2.push s.1

def subS (u v : Array UInt64) : Array UInt64 :=
  (LeanExe.loop (Library.Numerics.MultiPrecision.width u v)
      ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    let t := u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1
    ((1 : UInt64) - (t >>> 32), s.2.push (t &&& 0xFFFFFFFF))).2

def longDivS (u v : Array UInt64) (t : UInt64) : Array UInt64 :=
  let m := u.size.toUInt64
  let d := (1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)
  let vn := Library.Numerics.Arithmetic.Uscale.mulSmall v d 0
  let s := LeanExe.loop (if t ≤ m then m - t + 1 else 0)
    (LeanExe.build m (fun _ => (0 : UInt64)), Library.Numerics.Arithmetic.Uscale.mulSmall u d 0)
      fun e s =>
      let qh := Library.Numerics.MultiPrecision.trial s.2 vn (m - t - e) t
      let ms := LeanExe.loop (t + 1) ((0 : UInt64), (0 : UInt64), s.2) fun i x =>
        let p := qh * vn[i.toNat]! + x.1
        let r := x.2.2[(i + (m - t - e)).toNat]! + 4294967296 - (p &&& 0xFFFFFFFF) - x.2.1
        (p >>> 32, (1 : UInt64) - (r >>> 32),
          x.2.2.set! (i + (m - t - e)).toNat (r &&& 0xFFFFFFFF))
      (s.1.set! (m - t - e).toNat (if ms.2.1 = 1 then qh - 1 else qh),
        if ms.2.1 = 1 then
          (LeanExe.loop (t + 1) ((0 : UInt64), ms.2.2) fun i x =>
            let a := x.2[(i + (m - t - e)).toNat]! + vn[i.toNat]! + x.1
            (a >>> 32, x.2.set! (i + (m - t - e)).toNat (a &&& 0xFFFFFFFF))).2
        else ms.2.2)
  let r := Library.Numerics.MultiPrecision.shortDiv s.2 d t
  LeanExe.build (m + v.size.toUInt64) fun i =>
    if i < m then s.1[i.toNat]! else if i - m < t then r[(i - m).toNat]! else 0

def divideS (u v : Array UInt64) : Array UInt64 :=
  if Library.Numerics.MultiPrecision.significant v = 0 then
    LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun i =>
      if i < u.size.toUInt64 then 0 else u[(i - u.size.toUInt64).toNat]!
  else if Library.Numerics.MultiPrecision.significant v = 1 then
    let r := Library.Numerics.MultiPrecision.shortDiv u v[(0 : UInt64).toNat]! u.size.toUInt64
    LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun i =>
      if i ≤ u.size.toUInt64 then r[i.toNat]! else 0
  else longDivS u v (Library.Numerics.MultiPrecision.significant v)

def natAddS (u v : Array UInt64) : Array UInt64 := natTrim (addS u v)

def natSubS (u v : Array UInt64) : Bool × Array UInt64 :=
  if Library.Numerics.Arithmetic.Uscale.le v u then (false, natTrim (subS u v))
  else (true, natTrim (subS v u))

def natDivModCheckedS (u v : Array UInt64) : UInt64 × Array UInt64 × Array UInt64 :=
  if v.size.toUInt64 == 0 then (1, #[], #[])
  else
    let r := divideS u v
    (0, natTrim (slice r 0 u.size.toUInt64), natTrim (slice r u.size.toUInt64 v.size.toUInt64))

end Library.Numerics.Bignum
