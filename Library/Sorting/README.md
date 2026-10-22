# Sorting

[Insertion sort](Insertion/Program.lean) inserts each word at the count of smaller words in the
accumulated array.  It takes quadratic time and uses `UInt64` comparisons.

[The compiled module](Insertion/Compiled.lean) has the verified compiler's execution and allocation
theorems.  [The compiler example](../../Verified/Examples/Insert.lean) retains its allocation-bound
proof and execution cases.  Sortedness and permutation proofs remain future work.
