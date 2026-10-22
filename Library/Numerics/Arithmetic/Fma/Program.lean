import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32

/-! The forty-fifth program of the verified compiler: `fma a b c`, the fused multiply-add of IEEE
754 (2019, clause 5.4.1), the double nearest to the exact `a · b + c` with ties to even, computed
with 64-bit words.  WebAssembly has no fused multiply-add, and the CORE-MATH functions call one.
The product of the two significands, each below `2 ^ 53`, is a 128-bit pair of words formed from the
products of their 32-bit halves.  The product and the significand of `c` are each shifted so that
the highest set bit lies at bit 125, which leaves bits 0 to 19 clear, and the operand of smaller
magnitude is shifted right to the other's scale, with the bits that it loses ORed into bit 0.  A
shift of 20 or less loses no bit, and the sum is exact.  A longer shift leaves the highest bit of
the sum at 124 or above, so that 72 or more bits lie below the rounding position, and the sticky
bit, which makes the sum odd, leaves the rounded result unchanged.  The sum is then normalized and
rounded to 53 bits, or to the bit of weight `2 ^ -1074` for a subnormal result, and a result beyond
the largest double is infinite.  IEEE 754 defines the special cases.  `0 · ∞ + c` and `∞ · 0 + c`
are invalid, and so is the sum of infinities of opposite signs, and an invalid operation gives the
default quiet NaN `0x7FF8000000000000`.  A NaN operand gives the first NaN of `a`, `b`, and `c`,
quieted, which keeps an input's payload as clause 6.2.3 recommends and also covers `0 · ∞` plus a
NaN.  An exact zero sum is `+0` unless both the product and `c` are zeros of negative sign, and a
nonzero sum that rounds to zero keeps its sign.  The dialect has no floating-point flags, and the
function raises none.  `FmaAccuracy.lean` checks the results against the exact value. -/

namespace Library.Numerics.Arithmetic.Fma.Fma

/-- The position of the highest set bit of a nonzero word, by binary search. -/
def msb64 (x : UInt64) : UInt64 :=
  let (x, n) := if x >>> 32 != 0 then (x >>> 32, (32 : UInt64)) else (x, (0 : UInt64))
  let (x, n) := if x >>> 16 != 0 then (x >>> 16, n + 16) else (x, n)
  let (x, n) := if x >>> 8 != 0 then (x >>> 8, n + 8) else (x, n)
  let (x, n) := if x >>> 4 != 0 then (x >>> 4, n + 4) else (x, n)
  let (x, n) := if x >>> 2 != 0 then (x >>> 2, n + 2) else (x, n)
  if x >>> 1 != 0 then n + 1 else n

/-- The position of the highest set bit of the nonzero 128-bit number `h · 2 ^ 64 + l`. -/
def msb128 (h l : UInt64) : UInt64 :=
  if h != 0 then 64 + msb64 h else msb64 l

/-- The 128-bit product of two words below `2 ^ 53`, as its high and low words, from the products
of their 32-bit halves.  The middle sum `a0 · b1 + a1 · b0` lies below `2 ^ 54`. -/
def mul128 (a b : UInt64) : UInt64 × UInt64 :=
  let a1 := a >>> 32
  let a0 := a &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let p00 := a0 * b0
  let mid := a0 * b1 + a1 * b0
  let l := p00 + (mid <<< 32)
  (a1 * b1 + (mid >>> 32) + (if l < p00 then 1 else 0), l)

/-- `(h, l)` shifted left by `s < 128`. -/
def shl128 (h l s : UInt64) : UInt64 × UInt64 :=
  if s == 0 then (h, l)
  else if s < 64 then ((h <<< s) ||| (l >>> (64 - s)), l <<< s)
  else (l <<< (s - 64), 0)

/-- `(h, l)` shifted right by `d`, which may exceed 127. -/
def shr128 (h l d : UInt64) : UInt64 × UInt64 :=
  if d == 0 then (h, l)
  else if d < 64 then (h >>> d, (l >>> d) ||| (h <<< (64 - d)))
  else if d < 128 then (0, h >>> (d - 64))
  else (0, 0)

/-- Whether any of the bits 0 to `k - 1` of `(h, l)` is set. -/
def lowBits128 (h l k : UInt64) : Bool :=
  if k == 0 then false
  else if k < 64 then l &&& (((1 : UInt64) <<< k) - 1) != 0
  else if k < 128 then l != 0 || h &&& (((1 : UInt64) <<< (k - 64)) - 1) != 0
  else l != 0 || h != 0

/-- `(h, l)` shifted right by `d`, with bit 0 set if a set bit was shifted out. -/
def sticky128 (h l d : UInt64) : UInt64 × UInt64 :=
  let (h', l') := shr128 h l d
  (h', if lowBits128 h l d then l' ||| 1 else l')

/-- Bit `k < 128` of `(h, l)`. -/
def bit128 (h l k : UInt64) : Bool :=
  if k < 64 then (l >>> k) &&& 1 == 1 else (h >>> (k - 64)) &&& 1 == 1

/-- Whether `(h1, l1) < (h2, l2)`. -/
def lt128 (h1 l1 h2 l2 : UInt64) : Bool :=
  h1 < h2 || (h1 == h2 && l1 < l2)

def add128 (h1 l1 h2 l2 : UInt64) : UInt64 × UInt64 :=
  let l := l1 + l2
  (h1 + h2 + (if l < l1 then 1 else 0), l)

def sub128 (h1 l1 h2 l2 : UInt64) : UInt64 × UInt64 :=
  (h1 - h2 - (if l1 < l2 then 1 else 0), l1 - l2)

/-- The bits of the double nearest to `(-1) ^ s · (h, l) · 2 ^ (w - 2400)` for a nonzero `(h, l)`
below `2 ^ 127`.  `m` is the position of the highest set bit.  A normal result, with `w + m ≥ 1378`,
keeps 53 bits from bit `m`, and a subnormal one keeps the bits from the one of weight `2 ^ -1074`,
bit `1326 - w`.  `e` is the biased exponent of the result, 1 for a subnormal one, so that the
encoding `(e - 1) · 2 ^ 52 + q` of the 53-bit significand `q` holds for both and absorbs a carry of
the rounding into the exponent.  A shift to the left loses no bits and needs no rounding. -/
def roundPack (s w h l : UInt64) : UInt64 :=
  let m := msb128 h l
  let (left, r, e) : Bool × UInt64 × UInt64 :=
    if w + m ≥ 1378 then
      if m ≥ 52 then (false, m - 52, w + m - 1377) else (true, 52 - m, w + m - 1377)
    else if w ≤ 1326 then (false, 1326 - w, 1) else (true, w - 1326, 1)
  let q :=
    if left then (shl128 h l r).2
    else if r ≥ 128 then 0
    else
      let q := (shr128 h l r).2
      if r ≥ 1 && bit128 h l (r - 1) && (lowBits128 h l (r - 1) || q &&& 1 == 1) then q + 1 else q
  let inf := (s <<< 63) ||| 0x7FF0000000000000
  if e ≥ 2047 then inf
  else
    let out := ((e - 1) <<< 52) + q
    if out ≥ 0x7FF0000000000000 then inf else (s <<< 63) ||| out

/-- The bits of `fma a b c` from the bits of its operands.  A finite operand `x` with biased
exponent `ex` and significand `mx` is `mx · 2 ^ (max ex 1 - 1075)`.  `w` is the exponent of bit 0
of a shifted operand plus 2400, which keeps it positive. -/
def fmaBits (a b c : UInt64) : UInt64 :=
  let frac : UInt64 := 0xFFFFFFFFFFFFF
  let ea := (a >>> 52) &&& 0x7FF
  let eb := (b >>> 52) &&& 0x7FF
  let ec := (c >>> 52) &&& 0x7FF
  let sp := (a ^^^ b) >>> 63
  let sc := c >>> 63
  if ea == 0x7FF && a &&& frac != 0 then a ||| 0x8000000000000
  else if eb == 0x7FF && b &&& frac != 0 then b ||| 0x8000000000000
  else if ec == 0x7FF && c &&& frac != 0 then c ||| 0x8000000000000
  else
    let zeroA := a <<< 1 == 0
    let zeroB := b <<< 1 == 0
    let zeroC := c <<< 1 == 0
    if ea == 0x7FF || eb == 0x7FF then
      if zeroA || zeroB || (ec == 0x7FF && sc != sp) then 0x7FF8000000000000
      else (sp <<< 63) ||| 0x7FF0000000000000
    else if ec == 0x7FF then c
    else if zeroA || zeroB then
      if zeroC then (sp &&& sc) <<< 63 else c
    else
      let ma := if ea == 0 then a &&& frac else (a &&& frac) ||| 0x10000000000000
      let mb := if eb == 0 then b &&& frac else (b &&& frac) ||| 0x10000000000000
      let ea1 := if ea == 0 then 1 else ea
      let eb1 := if eb == 0 then 1 else eb
      let (ph, pl) := mul128 ma mb
      let shiftP := 125 - msb128 ph pl
      let (ph, pl) := shl128 ph pl shiftP
      let wP := ea1 + eb1 + 250 - shiftP
      if zeroC then roundPack sp wP ph pl
      else
        let mc := if ec == 0 then c &&& frac else (c &&& frac) ||| 0x10000000000000
        let ec1 := if ec == 0 then 1 else ec
        let shiftC := 125 - msb64 mc
        let (ch, cl) := shl128 0 mc shiftC
        let wC := ec1 + 1325 - shiftC
        let first := wP > wC || (wP == wC && !lt128 ph pl ch cl)
        let (xh, xl, wX, sX) := if first then (ph, pl, wP, sp) else (ch, cl, wC, sc)
        let (yh, yl, wY, sY) := if first then (ch, cl, wC, sc) else (ph, pl, wP, sp)
        let (yh, yl) := sticky128 yh yl (wX - wY)
        let (h, l) := if sX == sY then add128 xh xl yh yl else sub128 xh xl yh yl
        if h == 0 && l == 0 then 0 else roundPack sX wX h l

/-- `a · b + c` rounded once to the nearest double, ties to even. -/
def fma (a b c : Float) : Float :=
  Float.ofBits (fmaBits a.toBits b.toBits c.toBits)

end Library.Numerics.Arithmetic.Fma.Fma
