# Sorting

[Insertion sort](Insertion/Program.lean) inserts each word at the count of smaller words in the
accumulated array.  It takes quadratic time and uses `UInt64` comparisons.  [The compiled
module](Insertion/Compiled.lean) has the verified compiler's execution and allocation theorems.
[The insertion example](../../Verified/Examples/Insert.lean) compiles the same function with an
allocation bound, `sortInsert_bound`, and its cases run on the library's module as well.
Sortedness and permutation proofs remain future work.

[Heapsort](Heapsort/README.md) is Algorithm H of TAOCP §5.2.3.  It sorts the array in its own block
and allocates nothing, and its proofs show that the module returns the array's elements in
nondecreasing order, a permutation of the input equal to Lean's `List.mergeSort` of it.

[Merge sort](MergeSort/README.md) is straight two-way merge sort, TAOCP §5.2.4.  It merges sorted
runs of width 1, 2, 4, and so on, each pass into a new array, and its proofs show that the module
returns the same nondecreasing permutation.
