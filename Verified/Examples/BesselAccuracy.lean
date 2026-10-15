import Verified.Examples.Bessel
import Verified.Examples.WorstCases
import Verified.Examples.BesselReference

/-! A native check of `Bessel.j0`, `j1`, `y0`, `y1`, `jn`, and `yn` against the references of
`BesselReference`, in units of the modulus.  For a result `y` of order `n` at `x`, with references
`J` and `Y` of that order at `q` bits, the modulus is `M = isqrt (J ² + Y ²) · 2 ^ -q`, its unit is
`2 ^ (⌊log₂ M⌋ - 52)`, with no clamp at the subnormal range, and the error is `|y - F|` in that
unit, with `F` the reference of the function, computed exactly from the integers.  The check
requires an error of at most 4 units for `j0`, `j1`, `y0`, and `y1`, the coordinator's bound, and of
at most `4 + |n|/3` units for `jn` and `yn` of order `n`, the coordinator's form `a + b |n|` with
constants that the measured errors allow, and the first argument of `main` replaces the divisor 3.
It reports the largest error, in thousandths of a unit rounded down, with its argument and the
largest of each order.  At NaN, the zeros, the infinities, and the negative arguments of `y0`, `y1`,
and `yn` it requires the special values that `Bessel`'s docstring lists, with the signs of the zeros
that fdlibm gives.  The arguments of the four functions of orders 0 and 1 are evenly spaced values
from 0.001 to 2, from 2 to 40, and from 40 to 300, the doubles within three steps of the first two
zeros of each function, hashed values from `2 ^ 9` to `2 ^ 201`, from `2 ^ 201` to `2 ^ 1000`, and
below 1, the inputs of `WorstCases`, which give the largest known errors of thirteen libraries in
Tables 4 to 11 of the August 2026 report by Gladman, Innocente, Mather, Ozaki, and Zimmermann, and
the special values, with both signs for `j0` and `j1`.  `jn` and `yn` take the orders 2, 3, 5, 10,
20, 50, and 100, -2, -3, and -7, and `2 ^ 32 + 5`, whose low 32 bits are 5, at evenly spaced values
up to `2 n + 30`, hashed values from `2 ^ 9` to `2 ^ 60` and from `2 ^ 302` to `2 ^ 1000`, values
below `2 ^ -29`, and the special values.  It exits with an error at the first result that fails.
Run with `lake env lean --run`. -/

namespace Verified.Examples.BesselAccuracy

open Verified.Examples Reference ArcReference BesselReference

/-- The error of `y` from `v · 2 ^ -q` in thousandths of the unit `2 ^ (⌊log₂ M⌋ - 52)`, rounded
down, for the modulus `M = isqrt (j² + w²) · 2 ^ -q`.  An infinite `y` has error 0 where
`v · 2 ^ -q` rounds to it and is otherwise infinitely far, which the largest `Nat` stands for here.
-/
def modulusError (y : Float) (v j w : Int) (q : Nat) : Nat :=
  if y.isInf then (if (toFloat v (-(q : Int))).toBits == y.toBits then 0 else 2 ^ 64) else
  let l := Nat.log2 (isqrt (j * j + w * w).toNat)
  let (my, ey) := exactValue y
  let s := ey + q
  let num := if s ≥ 0 then (my * 2 ^ s.toNat - v).natAbs else (my - v * 2 ^ (-s).toNat).natAbs
  let d := if s ≥ 0 then 0 else (-s).toNat
  num * 1000 * 2 ^ 52 / 2 ^ (l + d)

/-- Whether `y` has the bits of `r`, or both are NaN. -/
def same (y r : Float) : Bool := if r.isNaN then y.isNaN else y.toBits == r.toBits

def nan : Float := Float.ofBits 0x7FF8000000000000
def inf : Float := Float.ofBits 0x7FF0000000000000

/-- The doubles within three steps of `x`. -/
def near3 (x : Float) : Array Float :=
  (Array.range 7).map fun i => Float.ofBits (x.toBits + UInt64.ofNat i - 3)

def special : Array Float :=
  #[0.0, -0.0, inf, -inf, nan, Float.ofBits 1, Float.ofBits 0x7FEFFFFFFFFFFFFF, -1.0, -3.5]

/-- The arguments of the function of orders 0 and 1 with index `k`: 0 for `j0`, 1 for `j1`, 2 for
`y0`, and 3 for `y1`. -/
def args01 (k : Nat) : Array Float :=
  let zeros : Array UInt64 := #[0x40033D152E971B40, 0x4016148F5B2C2E45, 0x400EA75575AF6F09,
    0x401C0FF5F3B47250, 0x3FEC982EB8D417EA, 0x400FA9534D98569C, 0x400193BED4DFF243,
    0x4015B7FE4E87B02E]
  let worst := #[WorstCases.j0, WorstCases.j1, WorstCases.y0, WorstCases.y1][k]!
  let base := evenly 1500 0.001 2.0 ++ evenly 3000 2.0 40.0 ++ evenly 1500 40.0 300.0 ++
    (zeros.extract (2 * k) (2 * k + 2)).flatMap (fun z => near3 (Float.ofBits z)) ++
    (hashed 800 (79 + UInt64.ofNat k) 1032 192 ++ hashed 300 (83 + UInt64.ofNat k) 1224 799 ++
      hashed 300 (89 + UInt64.ofNat k) 0 1023).map Float.abs ++
    worst.map Float.ofBits
  let base := if k < 2 then base.flatMap fun x => #[x, -x] else base
  base ++ special

/-- The special value of the function `k` of orders 0 and 1 at `x`, or `none` for an ordinary
argument. -/
def special01 (k : Nat) (x : Float) : Option Float :=
  if x.isNaN then some nan
  else if k == 0 then
    if x.isInf then some 0.0 else if x == 0.0 then some 1.0 else none
  else if k == 1 then
    if x.isInf then some (1.0 / x) else if x == 0.0 then some x else none
  else if x.isInf then some (if x > 0.0 then 0.0 else nan)
  else if x == 0.0 then some (-inf)
  else if x < 0.0 then some nan
  else none

/-- The orders of the check of `jn` and `yn`. -/
def orders : Array UInt64 :=
  #[2, 3, 5, 10, 20, 50, 100, 0xFFFFFFFE, 0xFFFFFFFD, 0xFFFFFFF9, 0x100000005]

/-- The arguments of `jn` and `yn` at the order of magnitude `n`. -/
def argsN (n : Nat) (seed : UInt64) : Array Float :=
  evenly 150 0.01 (Float.ofNat (2 * n + 30)) ++ (hashed 30 seed 1032 51 ++
    hashed 10 (seed + 1) 1325 698 ++ hashed 10 (seed + 2) 900 92).map Float.abs ++ special

end Verified.Examples.BesselAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.BesselReference
  Verified.Examples.BesselAccuracy in
def main (argv : List String) : IO UInt32 := do
  let bound01 : Nat := 4
  let divisor : Nat := (argv.head? >>= String.toNat?).getD 3
  for (name, k, f) in [("j0", 0, Bessel.j0), ("j1", 1, Bessel.j1), ("y0", 2, Bessel.y0),
      ("y1", 3, Bessel.y1)] do
    let mut worst : Nat := 0
    let mut loc : Float := 0.0
    let args := args01 k
    for x in args do
      let y := f x
      match special01 k x with
      | some r =>
        unless same y r do
          IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, expected {r.toBits}"
          return 1
      | none =>
        let (j0, j1, y0, y1) := bessel01 x.abs
        let q := precisionAt x.abs
        let (v, j, w) := if k == 0 then (j0, j0, y0) else if k == 1 then (j1, j1, y1)
          else if k == 2 then (y0, j0, y0) else (y1, j1, y1)
        let v := if k == 1 && x < 0.0 then -v else v
        let err := modulusError y v j w q
        if err > worst then
          worst := err
          loc := x
        unless err ≤ bound01 * 1000 do
          IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, {err} thousandths"
          return 1
    IO.println s!"bessel accuracy: {args.size} results of {name} lie within {worst} thousandths \
      of a unit of the modulus, the largest at bits {loc.toBits}"
  for (name, isJ) in [("jn", true), ("yn", false)] do
    let mut worst : Nat := 0
    let mut loc : String := ""
    let mut count := 0
    let mut perOrder : Array String := #[]
    for n in orders do
      let mut worstN : Nat := 0
      let n32 := n &&& 0xFFFFFFFF
      let neg := n32 ≥ 0x80000000
      let an := (if neg then 0x100000000 - n32 else n32).toNat
      for x in argsN an (97 + n) do
        let y := if isJ then Bessel.jn n x else Bessel.yn n x
        count := count + 1
        let odd := an % 2 == 1
        let flip := neg && odd
        let expected : Option Float :=
          if x.isNaN then some nan
          else if isJ then
            let x' := if neg then -x else x
            if x.isInf || x == 0.0 then some (if odd && x'.toBits >>> 63 == 1 then -0.0 else 0.0)
            else none
          else if x == 0.0 then some (-inf)
          else if x < 0.0 then some nan
          else if x.isInf then some 0.0
          else none
        match expected with
        | some r =>
          unless same y r do
            IO.eprintln s!"fail: {name} {n} at bits {x.toBits}: {y.toBits}, expected {r.toBits}"
            return 1
        | none =>
          let (jr, yr) := besselN an x.abs
          let q := precisionAt x.abs
          let v := if isJ then jr else yr
          let v := if flip then -v else v
          let v := if isJ && x < 0.0 && odd then -v else v
          let err := modulusError y v jr yr q
          worstN := max worstN err
          if err > worst then
            worst := err
            loc := s!"order {n} and bits {x.toBits}"
          unless err ≤ 4000 + 1000 * an / divisor do
            IO.eprintln s!"fail: {name} {n} at bits {x.toBits}: {y.toBits}, {err} thousandths"
            return 1
      perOrder := perOrder.push s!"{n}: {worstN}"
    IO.println s!"bessel accuracy: {count} results of {name} lie within {worst} thousandths of a \
      unit of the modulus, the largest at {loc}; by order {perOrder}"
  return 0
