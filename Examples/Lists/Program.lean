module

public import Library.Lists.Word.Program
public import LeanExe.Dialect.Loop

@[expose] public section

/-!
Lists of words, held on the heap as chains of records of two slots: the element and the
pointer to the rest.
-/

namespace Examples.Lists

export Library.Lists.Word (listSum)

/-- The words below `n` in increasing order, built from the last: step `i` puts `n - 1 - i` in
front. -/
def listRange (n : UInt64) : List UInt64 := Library.Lists.Word.range n

/-- The sum of the words below `n` modulo 2^64, through the list `listRange n`. -/
def sumRange (n : UInt64) : UInt64 := (listRange n).foldl (· + ·) 0

end Examples.Lists
