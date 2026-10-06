import LeanExe.Dialect.Loop

/-!
Truth values as data: `Bool` parameters, results, record fields, and loop states, built with
`decide`, `&&`, `||`, `!`, `==`, and `!=`.  A `Bool` is the word of its constructor index,
0 for `false` and 1 for `true`.
-/

namespace Examples.Bools

def isPositive (x : UInt64) : Bool := decide (0 < x)

def both (a b : Bool) : Bool := a && b

def either (a b : Bool) : Bool := a || b

def negate (a : Bool) : Bool := !a

def same (x y : UInt64) : Bool := x == y

def differ (x y : UInt64) : Bool := x != y

def agree (a b : Bool) : Bool := a == b

/-- IEEE equality: NaN equals nothing, and the two zeros are equal. -/
def floatSame (x y : Float) : Bool := x == y

def inRange (lo hi x : Float) : Bool := lo ≤ x && x ≤ hi

def pick (a : Bool) (x y : UInt64) : UInt64 := if a then x else y

/-- Whether `k` is below `n`, by a loop whose state is a `Bool`. -/
def anyEqual (n k : UInt64) : Bool := LeanExe.loop n false fun i acc => acc || i == k

structure Flagged where
  flag : Bool
  value : UInt64

def mark (x : UInt64) : Flagged := ⟨x == 0, x⟩

def flagOf (f : Flagged) : Bool := f.flag

end Examples.Bools
