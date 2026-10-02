/-!
A list of words declared by the program, held on the heap as records: the empty list is the
null pointer, and `cons x w` a record of two slots, the word `x` and the pointer to `w`.
-/

namespace LeanExe.Examples.Words

/-- A list of words. -/
inductive Words where
  | nil
  | cons (head : UInt64) (tail : Words)

/-- The first word, or 0 for the empty list. -/
def Words.first : Words → UInt64
  | .nil => 0
  | .cons x _ => x

/-- `acc` plus the sum of the words modulo 2^64, by tail recursion. -/
def Words.sumAcc (acc : UInt64) : Words → UInt64
  | .nil => acc
  | .cons x w => Words.sumAcc (acc + x) w

end LeanExe.Examples.Words
