import Verified.Reflect.Command
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile

/-! `Int64` in the verified compiler's dialect: one function for each place where the reflector
admits an `Int64` value, each reflected through the word forms of `LeanExe.ProofKit.Signed64`.
`arith` applies the operations whose bits are the word operations' and negation, `divs` the word
forms of `/`, `%`, and `>>>` on variables and on compound operands, `cmps` the comparisons as
`Bool` values, `sign` an `if` with word branches on comparisons, `dist` an `if` with `Int64`
branches on an `Int64` comparison, `least` and `most` `min` and `max`, `update` and `count` `set!`,
`push`, and `LeanExe.build` on `Array Int64`, `triple` a loop and `grow` a `repeatWhile` with
`Int64` state, `walk` a recognized tail recursion that tests an `Int64` value, `addItem` a
structure with an `Int64` field and an array of `Int64`, and `lits` the literals. -/

namespace Verified.Examples.Signed

open LeanExe.Pipeline

def arith (a b : Int64) : Int64 :=
  ((a + b) * (3 : Int64) - (-a)) ^^^ (b <<< (2 : Int64)) ||| (a &&& (-5 : Int64))

def divs (a b : Int64) : Int64 := a / b + a % b - (a >>> 3) + (a + 1) / (b - 1)

def cmps (a b : Int64) : Bool :=
  a < b && b ≤ 7 || a > -3 && b ≥ a || a == b || a != -1 || decide (a = b) || decide (a ≠ b)

def sign (a : Int64) : UInt64 := if a < 0 then 1 else if a = 0 then 0 else 2

def dist (a b : Int64) : Int64 := if a < b then b - a else a - b

def least (a b : Int64) : Int64 := min a b

def most (a b : Int64) : Int64 := max a b

def update (xs : Array Int64) (i : UInt64) (v : Int64) : Array Int64 :=
  (xs.set! i.toNat (v / 2)).push (-v)

def count (n : UInt64) : Array Int64 := LeanExe.build n fun i => i.toInt64 - 3

def triple (n : UInt64) (x : Int64) : Int64 := LeanExe.loop n x fun i acc => acc * 3 - i.toInt64

def grow (x : Int64) : Int64 := LeanExe.repeatWhile 100 x (fun s => s < 1000) (fun s => s * 2 + 1)

def walk (x : Int64) (n : UInt64) : Int64 :=
  if n = 0 then x else if x < 0 then walk (x + 7) (n - 1) else walk (x - 5) (n - 1)
termination_by n.toNat
decreasing_by
  all_goals
    rename_i hn _
    simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
    omega

/-- A running total and the values it has added. -/
structure Acc where
  total : Int64
  items : Array Int64

instance : Flat Acc (Int64 × Array Int64) := ⟨fun s => (s.total, s.items)⟩

def addItem (s : Acc) (v : Int64) : Acc := { total := s.total + v, items := s.items.push v }

def lits : Int64 := Int64.minValue + Int64.maxValue + (-9) * 2

verified_compile compiled :=
  [arith, divs, cmps, sign, dist, least, most, update, count, triple, grow, walk, addItem, lits]

#print axioms compiled.bytes
#print axioms compiled.divs.implements
#print axioms compiled.walk.implements
#print axioms compiled.addItem.implements

end Verified.Examples.Signed
