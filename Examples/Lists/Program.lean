import LeanExe.Dialect.Loop

/-!
Lists of words, held on the heap as chains of records of two slots: the element and the
pointer to the rest.
-/

namespace Examples.Lists

/-- The sum of the elements modulo 2^64. -/
def listSum (xs : List UInt64) : UInt64 := xs.foldl (· + ·) 0

/-- The words below `n` in increasing order, built from the last: step `i` puts `n - 1 - i` in
front. -/
def listRange (n : UInt64) : List UInt64 := LeanExe.loop n [] fun i xs => (n - 1 - i) :: xs

/-- The sum of the words below `n` modulo 2^64, through the list `listRange n`. -/
def sumRange (n : UInt64) : UInt64 := (listRange n).foldl (· + ·) 0

end Examples.Lists
