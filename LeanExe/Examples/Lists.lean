/-!
Lists of words, held on the heap as chains of records of two slots: the element and the
pointer to the rest.
-/

namespace LeanExe.Examples.Lists

/-- The sum of the elements modulo 2^64. -/
def listSum (xs : List UInt64) : UInt64 := xs.foldl (· + ·) 0

end LeanExe.Examples.Lists
