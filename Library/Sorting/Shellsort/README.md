# Shellsort: Algorithm D of TAOCP §5.2.1

## Request and specification

[The request](request.txt) asks for Shellsort of an array of words into nondecreasing order with the increments that Knuth recommends, in place, with a call stack that does not grow.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words, as for the library's other sorts.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and not the method or the increments.  The specification reads "in place" as a call that does not raise the heap's `top`, which is weaker than the request, since no theorem states that the result occupies the input's block, and it reads "a call stack that does not grow" as theorems with no call-depth premise.  [The review](review.md) records the specification's two independent reviews and the cases that they added.

## The program

[The program](Program.lean) is Knuth's Algorithm D on the array `xs[0, n)` with indices from 0.  The increments are `h_1 = 1` and `h_{s+1} = 3h_s + 1`, from `h_t`, the first increment with `h_{t+2} ≥ n`, down to 1, so 100 words take the increments 13, 4, and 1, and fewer than 14 words take only 1.  `firstIncrement n 1` computes `h_t`: from `h = 1` it replaces `h` by `3h + 1` while `9h + 4`, the increment two steps above `h`, is below `n`, a test that it makes as `h ≤ (n - 5) / 9` after the guard `4 < n`, so that no word wraps.  `passes h xs` runs `pass h` for `h` and each smaller increment above 1, with `(h - 1) / 3` the increment below `h`, and `shellsort` ends with the library's `straightInsertion`, which is the pass with increment 1, as quicksort's step Q9 is.

`pass h xs` performs steps D2 to D6 for one increment: for `j` from `h` to `n - 1`, `insertBy` inserts the word at `j` among the words `h`, `2h`, … places before it, which the earlier steps of the pass have put in order.  `insertBy v h i xs` holds a vacant position `i`: while `h ≤ i` and `v < xs[i - h]`, step D5 moves the word at `i - h` to `i` and decreases `i` by `h`, and when either test fails, step D6 stores `v` at `i`.  A word equal to `v` stops the search, as Knuth's test `K ≥ K_i` in step D4 does.  Knuth tests `i > 0` after he decreases `i`, and `insertBy` tests `h ≤ i` before it reads `xs[i - h]`, so no index wraps.  `pass` reads the array's size once, before the loop takes the array, so the module copies no array.

## The module sorts in place

`verified_compile compiled := [shift, straightInsertion, insertBy, pass, passes, firstIncrement, shellsort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `shellsort` is function 8.  The compiler translates the tail recursions of `shift`, `insertBy`, `passes`, and `firstIncrement`, and the loops of `pass` and `straightInsertion`, into loops, so no theorem of the module has a call-depth premise.  The caller moves the array to `shellsort` as `Moved (Array UInt64)`, and every update is the array's last use, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the array in its own block.

| Theorem | File | Statement |
|---|---|---|
| `set!_self` | [The proof](Proof.lean) | Storing an array's own word at a position leaves the array unchanged. |
| `move_eq` | [The proof](Proof.lean) | One move of step D5, the word at `j` stored at `i` and then `v` at `j`, gives the array that holds `v` at `i` with positions `i` and `j` exchanged. |
| `insertBy_perm` | [The proof](Proof.lean) | `insertBy v h i xs` has the size of `xs` and is a permutation of `xs.set! i v`. |
| `pass_perm`, `passes_perm` | [The proof](Proof.lean) | A pass, and the passes from any increment, keep the size and permute the array. |
| `shellsort_eq` | [The proof](Proof.lean) | `shellsort xs = expected xs` for every array with fewer than `2^64` elements. |
| `straightInsertion_sorted_perm` | [Straight insertion's proof](../StraightInsertion/Proof.lean) | `straightInsertion` returns a permutation of its input in nondecreasing order. |
| `eq_mergeSort_of_sorted_perm` | [The sorted lists](../Sorted.lean) | A list of words in nondecreasing order that is a permutation of `m` is `List.mergeSort` of `m`. |
| `shellsort_export` | [The compilation](Compiled.lean) | Export `shellsort` of `compiled.module` is function 8. |
| `shellsort_implements` | [The compilation](Compiled.lean) | Function 8, called with an array that the caller moves to it, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.shellsort.bound`, returns without a trap the owned array `expected xs` and raises `top` by at most the bound. |
| `shellsort_bound` | [The compilation](Compiled.lean) | `compiled.shellsort.bound` is 0, so a call does not raise `top`. |
| `shellsort_file`, `shellsort_file_decode` | [The file theorems](File.lean) | `build/verified/shellsort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The proof needs only that the passes with increments above 1 permute the array, since straight insertion sorts every array and a sorted permutation is unique.  `insertBy_perm` proceeds by induction on the vacant position, with `move_eq` turning each move into an exchange in the array that holds `v` at the vacant position, so each insertion permutes `xs.set! i v`, and `set!_self` gives `xs` itself when `v` is the word at `i`.  `shellsort_implements` is an `ImplementsA` theorem, since the caller moves the array into the call, and its axiom report names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.Shellsort.Compiled
tests/verified/run.sh --cases shellsort
tests/native/verified.sh --module shellsort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `shellsortInputs` in [the case inputs](../../../tests/TestSupport/Modules/Shellsort.lean): the inputs of quicksort, which include those of straight insertion and heapsort, and for each length at which the first increment changes, from 14 to 9,842, and the length below it, an array in decreasing order and an array drawn from eleven arbitrary words, four to six of them at or above `2^63`, in which every pass with an increment above 1 compares equal words and words at or above `2^63`, and for each length up to 3,281 an array of distinct arbitrary words.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that the module allocates nothing beyond the host's input array and keeps one block, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.  The increments change only the work, so no case can detect a wrong increment or a pass with an increment above 1 that keeps the permutation, and the proof of `shellsort_eq` likewise uses only the permutation.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.1](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Thomas Niemann, Sorting and Searching Algorithms: Shell sort](https://profesores.elo.utfsm.cl/~agv/elo320/PLDS210/niemann/s_shl.htm)
