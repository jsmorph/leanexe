import Verified.Examples.Tanh
import Verified.Examples.Reference

/-! A native check of `Tanh.expm1` and `Tanh.tanh` against `Reference.expm1` and `Reference.tanh`
rounded to the nearest double.  fdlibm states an error below one unit in the last place for
`expm1`, so each of its results must lie within one unit of the reference.  fdlibm states no bound
for `tanh`, whose quotients enlarge the error of `expm1`.  Its results must lie within two units,
the largest distance that the check finds, and glibc's `tanh`, derived from the same source,
lies two units from the reference at the same arguments.  The arguments of `expm1` are evenly
spaced values from -40 to 710, hashed values over the exponents from `2 ^ -60` to `2 ^ 9` with
both signs, the doubles next to the high words that the code compares with and next to
`(n + 1/2) ln 2` for the `n` at which `k` changes the form of the result, evenly spaced values
from the high-word thresholds to `ln 2/2`, `1.5 ln 2`, and `o_threshold`, tiny values, and the
special values.  Those of `tanh` are evenly spaced
values from -25 to 25, hashed values over the exponents from `2 ^ -60` to `2 ^ 5` with both signs,
the doubles next to its thresholds, tiny values, and the special values.  The check also reports,
for information, the distance from the reference of the C library's `tanh`, which Lean's
`Float.tanh` calls, and it exits with an error at the first result further from the reference
than its bound.  Run with `lake env lean --run`. -/

namespace Verified.Examples.TanhAccuracy

open Verified.Examples Reference

/-- The double nearest to `expm1 x`. -/
def expm1Reference (x : Float) : Float :=
  if x.isNaN || x == 0.0 then x
  else if x.isInf then if x > 0.0 then x else -1.0
  else if x > 1100.0 then Float.ofBits 0x7FF0000000000000
  else if x < -1100.0 then -1.0
  else
    let q := precision x
    toFloat (Reference.expm1 (scaled x q) q) (-(q : Int))

/-- The double nearest to `tanh x`.  From 550 on in magnitude, `tanh x` lies within `2 e ^ -1100`
of `±1` and rounds to it. -/
def tanhReference (x : Float) : Float :=
  if x.isNaN || x == 0.0 then x
  else if x.abs ≥ 550.0 then if x > 0.0 then 1.0 else -1.0
  else
    let q := precision x
    toFloat (Reference.tanh (scaled x q) q) (-(q : Int))

def tiny : Array Float :=
  #[Float.ofBits 1, Float.ofBits 0x000FFFFFFFFFFFFF, Float.ofBits 0x0010000000000000, 1e-300,
    Float.ofBits 0x3C8FFFFFFFFFFFFF, Float.ofBits 0x3C90000000000000, 1e-10].flatMap
    fun x => #[x, -x]

def special : Array Float :=
  #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1e300, -1e300, Float.ofBits 0x7FEFFFFFFFFFFFFF]

/-- `ln 2`, rounded. -/
def ln2 : Float := Float.ofBits 0x3FE62E42FEFA39EF

/-- The first doubles above the high words that `expm1` compares with: those of `ln 2/2`,
`1.5 ln 2`, `56 ln 2`, `o_threshold`, and `2 ^ -54`. -/
def highWords : Array Float :=
  #[0x3FD62E4300000000, 0x3FF0A2B200000000, 0x4043687A00000000, 0x40862E4200000000,
    0x3C90000000000000].map Float.ofBits

def expm1Args : Array Float :=
  let halves := #[1.5, 2.5, 19.5, 20.5, 56.5, 57.5, 1023.5].map (· * ln2)
  let edges := (highWords ++ halves ++ #[ln2 - 0.25, 709.782712893384, 1.0, 0.25]).flatMap
    fun x => near x ++ near (-x)
  let between := (evenly 1000 highWords[1]! (1.5 * ln2) ++ evenly 200 (0.5 * ln2) highWords[0]! ++
    evenly 1000 highWords[3]! 709.782712893384).flatMap fun x => #[x, -x]
  evenly 120000 (-40.0) 710.0 ++ hashed 60000 17 963 70 ++ edges ++ between ++ tiny ++ special

def tanhArgs : Array Float :=
  let edges := #[Float.ofBits 0x3E30000000000000, 1.0, 22.0, 0.5, 2.0].flatMap
    fun x => near x ++ near (-x)
  evenly 100000 (-25.0) 25.0 ++ hashed 60000 19 963 66 ++ edges ++ tiny ++ special

end Verified.Examples.TanhAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.TanhAccuracy in
def main : IO UInt32 := do
  let mut expm1s : Tally := {}
  for x in expm1Args do
    let ref := expm1Reference x
    let y := Tanh.expm1 x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: expm1 at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    expm1s := expm1s.add y ref
  IO.println s!"tanh accuracy: {expm1Args.size} results of expm1 lie within \
    {units expm1s.worst} of the reference, {expm1s.unequal} of them unequal"
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in tanhArgs do
    let ref := tanhReference x
    let y := Tanh.tanh x
    unless (distance y ref).any (· ≤ 2) do
      IO.eprintln s!"fail: tanh at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.tanh x) ref
  IO.println s!"tanh accuracy: {tanhArgs.size} results of tanh lie within {units ours.worst} of \
    the reference, {ours.unequal} of them unequal"
  IO.println s!"tanh accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
