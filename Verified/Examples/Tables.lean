import Verified.Reflect.Command

/-! The twenty-seventh program of the verified compiler: constant tables.  A table is a constant
array of words, which the module holds in a data segment.  A function takes it as a borrowed array
parameter, and a wrapper, a definition that applies such a function to tables, becomes an exported
entry that passes the tables' addresses.  The wrapper's theorem holds from a store that holds the
tables at their addresses, apart from the blocks that the arguments move. -/

namespace Verified.Examples.Tables

def squares : Array UInt64 := #[0, 1, 4, 9, 16, 25, 36, 49]

def primes : Array UInt64 := #[2, 3, 5, 7, 11, 13]

def squareWith (t : Array UInt64) (k : UInt64) : UInt64 := t[k.toNat]!

def sumWith (s p : Array UInt64) (k : UInt64) : UInt64 :=
  s[k.toNat]! + p[k.toNat]! + p.size.toUInt64

/-- An update of an owned array from a table. -/
def setWith (t xs : Array UInt64) (k : UInt64) : Array UInt64 := xs.set! k.toNat t[k.toNat]!

/-- An extension of an owned array by a table's entry: the array is a paid parameter. -/
def pushWith (t xs : Array UInt64) (k : UInt64) : Array UInt64 := xs.push t[k.toNat]!

def square (k : UInt64) : UInt64 := squareWith squares k

def sum (k : UInt64) : UInt64 := sumWith squares primes k

def setSquare (xs : Array UInt64) (k : UInt64) : Array UInt64 := setWith squares xs k

def pushSquare (xs : Array UInt64) (k : UInt64) : Array UInt64 := pushWith squares xs k

verified_compile compiled := [squareWith, sumWith, setWith, pushWith, square, sum, setSquare,
  pushSquare]

/-- `pushSquare xs k` charges the credit of `xs`, 16 bytes for each of its words and its length,
and a header and four times the 8 bytes that its push adds. -/
theorem pushSquare_bound (xs : Array UInt64) (k : UInt64) :
    compiled.pushSquare.bound (⟨xs⟩, k) = 16 * (xs.size + 1) + 80 := by
  rw [compiled.pushSquare.bound_eq, compiled.pushWith.bound_eq, compiled.pushWith.cost_eq,
    creditCost, paidGrowCost_eq]

end Verified.Examples.Tables
