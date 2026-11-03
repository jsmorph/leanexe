# Selection: Hoare's FIND

## Request and specification

[The request](request.txt) asks for the word of rank `k` of an array of words, counting from 0, which is the word at position `k` of the array sorted into nondecreasing order, or 0 when `k` is not a position of the array.  It asks for Hoare's selection method, FIND, with the partition steps of quicksort, in place, with a call stack that does not grow.  [The specification](Spec.lean) states the result as `expected xs k`, the word at position `k` of Lean's `List.mergeSort` of the array with the unsigned comparison of words, read with `!`, which gives 0 at a position past the end.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the word of each rank is determined, and equal words at different positions give the same result.  The specification reads "in place" as a call that does not raise the heap's `top`, since `select_implements` bounds the rise of `top` by the generated bound and `select_bound` states that the bound is 0, and it reads "a call stack that does not grow" as the generated `trapFree` theorem with no call-depth premise, since the compiler gives a call depth to every recursive function other than a recognized tail recursion, which it translates into a loop.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) applies `part`, steps Q3 to Q6 of [quicksort](../Quicksort/README.md), to the subfile `[l, e)` that holds position `k`, with the subfile's first word `K` as the partitioning word.  When the final position `j` of `K` is above `k`, `find` continues with `[l, j)`, when it is below `k`, with `[j + 1, e)`, and when it equals `k`, it stops, as it does when the subfile has fewer than two words.  `select xs k` returns 0 when `k` is not a position of the array, and otherwise runs `find` on the whole array and reads the word at `k`.  Hoare's FIND, Algorithm 65, applies his partition procedure, Algorithm 63, which he published with it, to the segment that holds position `k`, and continues with the part that holds it.  The program uses Knuth's partition in its place, which puts the subfile's first word at its final position, so that selection shares its partition with quicksort.

The first word of each subfile is the partitioning word, so on an array in increasing order a rank near the end takes about `n²/2` comparisons.  Each scan reads the array before the exchange that consumes it, and the compiler binds the scans first, so the module partitions the array in its own block.  The generated bounds of `find` and `select` are 0.

## The module partitions in place

`verified_compile compiled := [swap, scanUp, scanDown, part, find, select]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `select` is function 7.  The compiler translates the tail recursions of `scanUp`, `scanDown`, `part`, and `find` into loops.  The caller hands the array over as `Moved (Array UInt64)`, and by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module partitions the array in its own block and releases it after its last use.

| Theorem | File | Statement |
|---|---|---|
| `scanUp_spec`, `scanDown_spec` | [The proof](Proof.lean) | Step Q3 from `i` stops at the first word not below `K`, or at `e`, after words below `K`, and step Q4 from `j` stops at the last word not above `K`, or at `l`, before words above `K`. |
| `swap_within`, `Frame.trans`, `FromSeg.trans`, `Frame.widen`, `FromSeg.widen` | [The proof](Proof.lean) | An exchange of two positions of `[l, e)` keeps every word outside the subfile in place and takes every word inside it from the subfile, and such changes compose and hold for every larger subfile. |
| `part_spec` | [The proof](Proof.lean) | Steps Q3 to Q6 put `K` at its final position `m`, every word of `[l, m)` at most `K`, and every word of `(m, e)` at least `K`, by a change within `[l, e)`. |
| `part_full` | [The proof](Proof.lean) | The partition of `[l, e)` around its first word, as the record `Parted`, which adds the size and the permutation. |
| `find_spec` | [The proof](Proof.lean) | `find` permutes the array by a change within `[l, e)`, and when the subfile holds `k`, it leaves at `k` a word at least every word of `[l, k)` and at most every word of `(k, e)`. |
| `rank_of_around` | [The proof](Proof.lean) | In a permutation of `xs` whose word at `k` is at least every earlier word and at most every later word, that word is the word at `k` of `xs` sorted. |
| `select_eq` | [The proof](Proof.lean) | `select xs k = expected xs k` for every array with fewer than `2^64` elements and every rank. |
| `pairwise_mergeSort_le` | [The sorted lists](../Sorted.lean) | `List.mergeSort` with the unsigned order of words returns a list in nondecreasing order. |
| `select_export` | [The compilation](Compiled.lean) | Export `select` of `compiled.module` is function 7. |
| `select_implements` | [The compilation](Compiled.lean) | Function 7, called with an array that the caller hands over and a rank `k`, returns without a trap `expected xs k`, with `top` raised by at most `compiled.select.bound`. |
| `select_bound` | [The compilation](Compiled.lean) | `compiled.select.bound` is 0, so a call does not raise `top`. |
| `find_file`, `find_file_decode` | [The file theorems](File.lean) | `build/verified/find.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`part_spec` follows the recursion of `part` with the invariant that the words of `(l, i]` are at most `K` and the words of `[j, e)` at least `K`: step Q6 exchanges a word not below `K` with a word not above `K`, and when the scans cross, step Q5 moves `K` to the position where step Q4 stopped.  `find_spec` proceeds by functional induction on `find`.  When the loop continues with the part before `j`, the word that it leaves at `k` comes from that part and is at most `K`, while every word from `j` on is at least `K`, and the part after `j` is symmetric.  `rank_of_around` sorts the words before `k` and after `k` around the word at `k`, which gives a nondecreasing permutation of the array, equal to `List.mergeSort` by `eq_mergeSort_of_sorted_perm`, and that sorted list holds at position `k` the permutation's word at `k`.  `select_implements` is an `ImplementsA` theorem, since the caller moves the array into the call, and its axiom report names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.Find.Compiled
tests/verified/run.sh --cases find
tests/native/verified.sh --module find
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `selectInputs` in [the case inputs](../../../tests/TestSupport/Modules/Find.lean): the arrays of quicksort, every rank of each array of at most 12 words and the first rank past it, the ranks 0, `⌊n / 2⌋`, `n - 1`, and `n` of each longer array, the middle rank of 10,000 words in decreasing order, which takes about 10,000 partitions, and the ranks `2^32 + 1` and `2^64 - 1` of ten arbitrary words.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each case with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that the module leaves no block live and allocates none beyond the host's array, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [C. A. R. Hoare, Algorithm 65: Find, Communications of the ACM 4(7), 1961, 321–322](https://doi.org/10.1145/366622.366647)
- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
