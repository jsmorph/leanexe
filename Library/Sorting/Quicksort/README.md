# Quicksort: Algorithm Q of TAOCP §5.2.2

## Request and specification

[The request](request.txt) asks for quicksort of an array of words into nondecreasing order, in place apart from a stack of pending subfiles, with a call stack that does not grow.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and leaves the method to the program, and arrays of 0 and 1 elements are their own result.  The specification reads "in place apart from a stack of pending subfiles" as a module whose storage beyond the array has a fixed bound: `quicksort_implements` bounds the rise of `top` by the generated bound, and `quicksort_bound` states that the bound is the cost of one block of 128 words.  It reads "a call stack that does not grow" as the generated `trapFree` theorem with no call-depth premise, since the compiler gives a call depth to every recursive function other than a recognized tail recursion, which it translates into a loop.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) is Knuth's Algorithm Q on the array `xs[0, n)` with indices from 0, subfiles written as half-open ranges `[l, e)`, and `M = 9`.  Steps Q3 and Q4 are `scanUp` and `scanDown`: from position `i`, `scanUp K e i a` finds the first position below `e` whose word is not below `K`, and from position `j`, `scanDown K l j a` finds the last position above `l` whose word is not above `K`.  Knuth's sentinel `K_{N+1} = ∞` stops step Q3 at the end of the file and the first word `K` stops step Q4, where `scanUp` tests `i < e` and `scanDown` tests `l < j`.  `part K l e i j a` performs steps Q3 to Q6: while the scans have not crossed, step Q6 exchanges the words where they stop, and when they cross, step Q5 exchanges `K` with the word where step Q4 stopped, which is the final position of `K`, and returns that position with the array.

`stages l e sp st a` performs steps Q2 to Q8 as one tail loop over the current subfile, a stack `st` of `sp` pending subfiles, and the array, and entry `k` of the stack is the subfile `[st[2k], st[2k + 1])`.  When both parts of a partition exceed `M` words and the stack has room, step Q7 pushes the larger part and continues with the smaller, which keeps the stack within `lg N` entries.  Otherwise the loop continues with the larger part, which is the one part that exceeds `M` when only one does, and when neither does, step Q8 replaces it at the next stage with the subfile on top of the stack.  The stack holds 64 entries and every array in memory has fewer than `2^64` words, so the stack does not fill, and if it did, the loop would leave the smaller part to step Q9 without changing the result.  `quicksort` runs `stages` on the whole array with an empty stack and then step Q9, `straightInsertion` over the whole array, which then needs to move each word only within its subfile of at most `M` words.

Each stage lowers the loop's rank, twice the sum of the sizes of the current subfile and the stacked subfiles plus the number of entries, so the loop ends on every input.  Each scan reads the array before the exchange that consumes it, and the compiler binds the scans first, so the module updates the array in its own block.  The generated bounds of `part` and `stages` are 0.  The first word of each subfile is the partitioning word, so on an array in increasing or decreasing order every partition leaves an empty part, and steps Q2 to Q7 make about `N²/2` comparisons.

## The module sorts in place

`verified_compile compiled := [swap, shift, straightInsertion, scanUp, scanDown, part, stages, quicksort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `quicksort` is function 9.  The compiler translates the tail recursions of `scanUp`, `scanDown`, `part`, `stages`, and `shift` into loops.  The caller hands the array over as `Moved (Array UInt64)`, and by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the array in its own block.

| Theorem | File | Statement |
|---|---|---|
| `scanUp_ge`, `scanDown_bounds` | [The program](Program.lean) | Step Q3 stops at or after its start, and step Q4 stops at or before its start and, from a start at or after `l`, at or after `l`. |
| `part_fst` | [The program](Program.lean) | From `l ≤ i < j`, the final position of `K` lies in `[l, j)`. |
| `stacked_push`, `dec_left`, `dec_right`, `dec_push_left`, `dec_push_right`, `dec_pop` | [The program](Program.lean) | Each stage of `stages` lowers the loop's rank. |
| `part_perm` | [The proof](Proof.lean) | When the subfile ends within the array, steps Q3 to Q6 return a permutation of the array of the same size. |
| `part_within` | [The proof](Proof.lean) | The partition of `[l, e)` puts `K` at a position of the subfile and permutes the array. |
| `push_within`, `pop_within` | [The proof](Proof.lean) | A push and a pop keep every stacked subfile within the array, and a pop takes such a subfile. |
| `stages_perm` | [The proof](Proof.lean) | When the current subfile and the stacked subfiles end within the array, `stages` returns a permutation of the array of the same size. |
| `quicksort_eq` | [The proof](Proof.lean) | `quicksort xs = expected xs` for every array with fewer than `2^64` elements. |
| `quicksort_export` | [The compilation](Compiled.lean) | Export `quicksort` of `compiled.module` is function 9. |
| `quicksort_implements` | [The compilation](Compiled.lean) | Function 9, called with an array that the caller hands over, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.quicksort.bound`, returns without a trap the owned array `expected xs` and raises `top` by at most the bound. |
| `quicksort_bound` | [The compilation](Compiled.lean) | `compiled.quicksort.bound` is `Verified.blockCost 128`, the block of the stack. |
| `quicksort_file`, `quicksort_file_decode` | [The file theorems](File.lean) | `build/verified/quicksort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

Step Q9 sorts every array, so the proof of `quicksort_eq` needs only that steps Q1 to Q8 permute the input, and `straightInsertion_sorted_perm` of [straight insertion's proof](../StraightInsertion/Proof.lean) gives a nondecreasing permutation of that permutation.  `part_perm` follows the recursion of `part`: each exchange of step Q6 lies below the end of the subfile, and the exchange of step Q5 lies between `l` and the position where step Q4 stopped.  `stages_perm` proceeds by functional induction on `stages`, with the invariant that the current subfile and every stacked subfile end within the array.  `quicksort_implements` is an `ImplementsA` theorem, since the caller moves the array into the call, and its axiom report names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.Quicksort.Compiled
tests/verified/run.sh --cases quicksort
tests/native/verified.sh --module quicksort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `quicksortInputs` in [the case inputs](../../../tests/TestSupport/Modules/Quicksort.lean): the inputs of straight insertion and heapsort, arrays of 10 and 11 words, first words above and below every other word, which run the scans to the ends of the subfile, and long arrays in increasing, decreasing, and organ-pipe order, of few values, of one word, and of arbitrary words, up to 10,000 words.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the module's allocations, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
