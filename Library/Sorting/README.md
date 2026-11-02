# Sorting

[Insertion sort](Insertion/Program.lean), `sortInsert`, builds a new array: it counts the words of
the accumulated array below the next word and inserts the word at that count with `insertAt`, in
quadratic time.  [Its proof](Insertion/Proof.lean) shows that the result is the array's elements in
nondecreasing order, and [the compiled module](Insertion/Compiled.lean) states the module's call,
`sortInsert_callSpec`.  [The insertion example](../../Verified/Examples/Insert.lean) compiles the
same function with an allocation bound, `sortInsert_bound`, and its cases run on the library's
module as well.

[Straight insertion](StraightInsertion/README.md) is Algorithm S of TAOCP §5.2.1.  It moves each
larger word one place right to make room for the next word, in the array's own block, and allocates
nothing.  Its proofs show that the module returns the same nondecreasing permutation, and both
insertion sorts reach `List.mergeSort` through the uniqueness of a sorted permutation, which [the
sorted lists](Sorted.lean) state.

[Quicksort](Quicksort/README.md) is Algorithm Q of TAOCP §5.2.2.  It partitions subfiles around
their first words in the array's own block, keeps the pending subfiles on a stack of 64 entries,
the module's one allocation, and finishes with straight insertion.  Its proofs show that the
partitions permute the array, so straight insertion returns the same nondecreasing permutation.

[Selection](Find/README.md) is Hoare's FIND with quicksort's partition.  It partitions the subfile
that holds a rank `k` and continues with the part that holds it, in the array's own block, and
returns the word of rank `k`, or 0 when `k` is not a position.  Its proofs show that the word left
at `k` lies between the words before it and the words after it, so it is the word at `k` of the
sorted array.

[Heapsort](Heapsort/README.md) is Algorithm H of TAOCP §5.2.3.  It sorts the array in its own block
and allocates nothing, and its proofs show that the module returns the array's elements in
nondecreasing order, a permutation of the input equal to Lean's `List.mergeSort` of it.

[Merge sort](MergeSort/README.md) is straight two-way merge sort, TAOCP §5.2.4.  It merges sorted
runs of width 1, 2, 4, and so on, each pass into a new array, and its proofs show that the module
returns the same nondecreasing permutation.
