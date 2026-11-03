# Straight insertion: Algorithm S of TAOCP §5.2.1

## Request and specification

[The request](request.txt) asks for straight insertion of an array of words into nondecreasing order, in place, with no storage beyond the array.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and not the method, and arrays of 0 and 1 elements are their own result.  The specification reads "in place, using no storage beyond the array" as a call that does not raise the heap's `top`, which `straightInsertion_bound` states, and whose call stack does not grow, which the generated `trapFree` theorem shows by having no call-depth premise.  That reading is weaker than the request's: a call could place its result in a free block below `top`, and no theorem states that the result occupies the input's block.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) is Knuth's Algorithm S on the array `xs[0, n)` with indices from 0.  For `j` from 1 to `n - 1`, the loop of `straightInsertion` performs steps S2 to S5: the words `xs[0, j)` are in order, and `shift v j xs` inserts the word `v` of position `j` among them.  `shift v i xs` holds a vacant position `i`: while `0 < i` and `v < xs[i - 1]`, step S4 moves the word at `i - 1` to `i` and decreases `i`, and when either test fails, step S5 stores `v` at `i`.  A word equal to `v` stops the search, so equal words keep their order, a property that no result can reveal, since equal words are identical.

Step S4 runs once for each inversion of the input, a pair of positions whose words are out of order, since each move puts `v` ahead of one larger word that preceded it.  A sort of `n` words therefore moves at most `n(n − 1)/2` words, `n(n − 1)/4` on average over the permutations of distinct words, and makes at most `n − 1` more comparisons than moves.  Knuth's step S4 tests `i > 0` after it decreases `i`, and `shift` tests `0 < i` before it reads `xs[i - 1]`, so no index wraps.  With 0 or 1 elements the loop of step S1 is empty, and `straightInsertion` returns the array unchanged.  The program reads the array's size once, before the loop takes the array, so the module copies no array.

## The module sorts in place

`verified_compile compiled := [shift, straightInsertion]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `straightInsertion` is function 3.  The compiler translates the tail recursion of `shift` into a loop.  The caller moves the array to `straightInsertion` as `Moved (Array UInt64)`, and every update is the array's last use, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the array in its own block.

| Theorem | File | Statement |
|---|---|---|
| `orderedInsert_append_of_lt`, `orderedInsert_of_forall_not_lt` | [The proof](Proof.lean) | Inserting `v` after every word at most `v`, `orderedInsert (· < ·) v`, into `l ++ [y]` with `v < y` gives the insertion into `l` followed by `y`, and into a list with no word above `v` appends `v`. |
| `pairwise_orderedInsert` | [The proof](Proof.lean) | The insertion keeps a list in nondecreasing order. |
| `shift_toList` | [The proof](Proof.lean) | When `xs[0, i)` is in order, `shift v i xs` holds `xs[0, i)` with `v` inserted in positions `0` to `i`, followed by the words of `xs` after `i`. |
| `straightInsertion_sorted_perm` | [The proof](Proof.lean) | `straightInsertion` returns a permutation of its input in nondecreasing order. |
| `straightInsertion_eq` | [The proof](Proof.lean) | `straightInsertion xs = expected xs` for every array with fewer than `2^64` elements. |
| `eq_mergeSort_of_sorted_perm` | [The sorted lists](../Sorted.lean) | A list of words in nondecreasing order that is a permutation of `m` is `List.mergeSort` of `m`. |
| `straightInsertion_export` | [The compilation](Compiled.lean) | Export `straightInsertion` of `compiled.module` is function 3. |
| `straightInsertion_implements` | [The compilation](Compiled.lean) | Function 3, called with an array that the caller moves to it, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.straightInsertion.bound`, returns without a trap the owned array `expected xs` and raises `top` by at most the bound. |
| `straightInsertion_bound` | [The compilation](Compiled.lean) | `compiled.straightInsertion.bound` is 0, so a call does not raise `top`. |
| `straightInsertion_file`, `straightInsertion_file_decode` | [The file theorems](File.lean) | `build/verified/straightInsertion.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

In the proof of `straightInsertion_sorted_perm`, each pass of the loop keeps the first `j + 1` words in order, a permutation of the first `j + 1` words of the input, and the rest of the input unchanged.  `shift_toList` proceeds by induction on the vacant position: a move turns the insertion into `xs[0, i)` into the insertion into `xs[0, i - 1)` followed by the moved word, and the store at a word at most `v` appends `v`, since every word of the sorted prefix is at most that word.  `straightInsertion_implements` is an `ImplementsA` theorem, since the caller moves the array into the call, and its axiom report names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.StraightInsertion.Compiled
tests/verified/run.sh --cases straightInsertion
tests/native/verified.sh --module straightInsertion
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `insertionInputs` in [the case inputs](../../../tests/TestSupport/Modules/StraightInsertion.lean): the inputs of heapsort, arrays whose insertions move every earlier word, move one word each, or stop at an equal word, the words 0 and `2^64 - 1` in adjacent positions, 1,500 words in decreasing order, and 1,000 words in increasing order except for a 0 at the end or a `2^64 - 1` at the front.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that the module allocates nothing beyond the host's input array and keeps one block, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, sections 5.1.1 and 5.2.1](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
