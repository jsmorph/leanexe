# Sorting

[Insertion sort](Insertion/Program.lean) inserts each word at the count of smaller words in the
accumulated array.  It takes quadratic time and uses `UInt64` comparisons.  [The compiled
module](Insertion/Compiled.lean) has the verified compiler's execution and allocation theorems.
[The insertion example](../../Verified/Examples/Insert.lean) compiles the same function with an
allocation bound, `sortInsert_bound`, and its cases run on the library's module as well.
Sortedness and permutation proofs remain future work.
