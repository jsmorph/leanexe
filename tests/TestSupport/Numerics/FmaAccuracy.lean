import Library.Numerics.Arithmetic.Fma.Program
import TestSupport.Numerics.Reference

/-! A native check of `Library.Numerics.Arithmetic.Fma.fma` against the exact value of `a · b + c`, an integer times a power of
two, rounded to the nearest double by `Reference.toFloat`.  The check requires the same bits as the
reference, or a quiet NaN where the reference is NaN.  The operands are every triple of 24 special
values: the zeros, the infinities, a quiet and a signaling NaN, the smallest and largest subnormals,
the smallest normal, the largest double, 1, 2, 3, and `1/2`, all with both signs.  To these the
check adds hashed operands of six kinds: (a) operands over all exponents; (b) products near 1 with
`c` the negated double nearest the product and the four doubles next to it, so that the result is
the rounding error of the product or a few units more; (c) products of operands with 26-bit
significands, which are exact doubles, with `c` their negation, so that the sum is an exact zero;
(d) products and addends near the smallest normal, with subnormal results; (e) products and addends
near the largest double, which overflow; and (f) products with a power of two and `c` half a unit of
the product in the last place, of either sign, or one of the two doubles next to that half, which
give ties and the results next to them.  It exits with an error at the first result that differs.
Run with `lake env lean --run`. -/

namespace TestSupport.Numerics.FmaAccuracy

open TestSupport.Numerics Reference

/-- The double nearest to `a · b + c`, with IEEE 754's special values and signed zeros. -/
def fmaReference (a b c : Float) : Float :=
  let nan := Float.ofBits 0x7FF8000000000000
  let sp := (a.toBits ^^^ b.toBits) >>> 63
  if a.isNaN || b.isNaN || c.isNaN then nan
  else if a.isInf || b.isInf then
    if a == 0.0 || b == 0.0 || (c.isInf && c.toBits >>> 63 != sp) then nan
    else Float.ofBits ((sp <<< 63) ||| 0x7FF0000000000000)
  else if c.isInf then c
  else
    let (ma, ea) := exactValue a
    let (mb, eb) := exactValue b
    let (mc, ec) := exactValue c
    let e := min (ea + eb) ec
    let v := ma * mb * 2 ^ (ea + eb - e).toNat + mc * 2 ^ (ec - e).toNat
    if v != 0 then toFloat v e
    else if (a == 0.0 || b == 0.0) && c == 0.0 && sp == 1 && c.toBits >>> 63 == 1 then -0.0
    else 0.0

/-- The `i`th word of the stream `seed`, from SplitMix64's mixing function. -/
def word (seed i : Nat) : UInt64 :=
  let z := UInt64.ofNat i * 0x9e3779b97f4a7c15 + UInt64.ofNat seed * 0x632be59bd9b4e019
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- A double with the sign and fraction of `h` and a biased exponent from `lo` to
`lo + span - 1`. -/
def double (h lo span : UInt64) : Float :=
  let e : UInt64 := lo + (h >>> (52 : UInt64) &&& 0x7FF) % span
  Float.ofBits ((h &&& 0x800FFFFFFFFFFFFF) ||| (e <<< (52 : UInt64)))

def special : Array Float :=
  let positive : Array UInt64 := #[0, 0x7FF0000000000000, 0x7FF8000000000000,
    0x7FF0000000000001, 1, 0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x7FEFFFFFFFFFFFFF,
    0x3FF0000000000000, 0x4000000000000000, 0x3FE0000000000000, 0x4008000000000000]
  (positive ++ positive.map (· ||| 0x8000000000000000)).map Float.ofBits

def triples : Array (Float × Float × Float) :=
  let n := 40000
  let any := (Array.range 200000).map fun i =>
    (double (word 1 i) 0 2047, double (word 2 i) 0 2047, double (word 3 i) 0 2047)
  let rounding := (Array.range n).flatMap fun i =>
    let a := double (word 4 i) 1013 20
    let b := double (word 5 i) 1013 20
    let p := (a * b).toBits ^^^ 0x8000000000000000
    #[p - 2, p - 1, p, p + 1, p + 2].map fun c => (a, b, Float.ofBits c)
  let exact := (Array.range n).map fun i =>
    let a := double (word 6 i &&& 0xFFFFFFFFF8000000) 900 200
    let b := double (word 7 i &&& 0xFFFFFFFFF8000000) 900 200
    (a, b, -(a * b))
  let subnormal := (Array.range n).map fun i =>
    (double (word 8 i) 450 120, double (word 9 i) 450 120, double (word 10 i) 0 60)
  let overflow := (Array.range n).map fun i =>
    (double (word 11 i) 1500 547, double (word 12 i) 1000 600, double (word 13 i) 1900 147)
  let ties := (Array.range n).flatMap fun i =>
    let a := double (word 14 i) 1 2045
    let b := Float.ofBits (((word 15 i % 200) + 924) <<< 52)
    let p := (a * b).abs.toBits
    let e := p >>> 52
    if e < 55 || p ≥ 0x7FF0000000000000 then #[]
    else
      let half := (e - 53) <<< 52
      #[half, half + 1, half - 1].flatMap fun h =>
        #[(a, b, Float.ofBits h), (a, b, Float.ofBits (h ||| 0x8000000000000000))]
  let specials := special.flatMap fun a => special.flatMap fun b => special.map fun c => (a, b, c)
  specials ++ any ++ rounding ++ exact ++ subnormal ++ overflow ++ ties

end TestSupport.Numerics.FmaAccuracy

open TestSupport.Numerics TestSupport.Numerics.FmaAccuracy in
def main : IO UInt32 := do
  let args := triples
  let mut unequal := 0
  for (a, b, c) in args do
    let r := Library.Numerics.Arithmetic.Fma.fma a b c
    let ref := fmaReference a b c
    let ok := if ref.isNaN then r.isNaN && r.toBits &&& 0x8000000000000 != 0
      else r.toBits == ref.toBits
    unless ok do
      IO.eprintln s!"fail: fma at bits {a.toBits} {b.toBits} {c.toBits}: {r.toBits}, the \
        reference {ref.toBits}"
      return 1
    if !ref.isNaN && (a * b + c).toBits != r.toBits then unequal := unequal + 1
  IO.println s!"fma accuracy: {args.size} results equal the exact value rounded to the nearest \
    double, {unequal} of them unequal to the separately rounded product and sum"
  return 0
