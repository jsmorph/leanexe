# Heapsort: Algorithm H of TAOCP §5.2.3

## Request and specification

[The request](request.txt) asks for heapsort of an array of words into nondecreasing order, in place, with no storage beyond the array.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and leaves the method to the program, and arrays of 0 and 1 elements are their own result.  The specification reads "no storage beyond the array" as a module that allocates nothing, which `heapsort_bound` states, and that uses a fixed number of locals, since the compiler translates the sift into a loop.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) is Knuth's Algorithm H on the array `xs[0, n)` with indices from 0: node `i` has the children `2i + 1` and `2i + 2`, where Knuth's node `j` has `2j` and `2j + 1`, and node `i` has a child exactly when `i < n / 2`.  `siftDown i n xs` is Knuth's siftup, steps H3 to H8: it finds the larger child, as steps H4 and H5 do, and while that child holds a larger word, the test of step H6, it exchanges the word at node `i` with the child and continues from the child.  `heapify n xs` is step H1 and the branch of step H2 that decreases Knuth's `l`: it sifts the nodes `n / 2 - 1` down to 0, which makes `xs[0, n)` a heap, with every node at or above its children.  `heapsort xs` then performs the branch of step H2 that decreases `r`: for `e` from `n - 1` down to 1, it exchanges the root, the largest word, with the word at `e` and sifts the new root down the heap `xs[0, e)`.

The sift keeps the heap order at every node at or after a bound `L` except the moving node `i`, with the children of `i` at most the parent of `i` when `L < i`, which `siftDown_spec` states.  After `heapify` sifts node `L`, the heap order holds at every node at or after `L`, and each pass of the second phase keeps a heap on `xs[0, e)`, a sorted suffix `xs[e, n)`, and every word of the prefix at most every word of the suffix.  A sift from node `i` of a heap of `n` words descends at most `⌊lg(n / (i + 1))⌋` levels, the height of node `i`, and makes at most two comparisons and one exchange at each level.  The nodes of height at least `h` number `⌊n / 2^h⌋`, so the heights sum to `n − ν(n)`, where `ν(n)` is the number of 1 bits of `n`, and `heapify` makes at most `2(n − ν(n))` comparisons.  The root of a heap of `e` words has height `⌊lg e⌋`, so the second phase makes at most `2(⌊lg 2⌋ + ⋯ + ⌊lg(n − 1)⌋)` comparisons, and a sort of `n ≥ 1` words makes at most `2n⌊lg n⌋` in all.

Knuth's step H7 moves the larger child up into the vacant node and step H8 stores the word once, where the program exchanges the word with the child at each level.  Knuth runs both phases in the one loop of step H2 and assumes at least two records, and `heapsort` returns arrays of 0 and 1 elements unchanged.  Each branch of `siftDown` names its child index, so the new index reads no array.  `swap i j xs` takes the array last, so that a caller reads the array in the other arguments before the call takes it, and `heapsort` reads the array's size once, before `heapify` takes the array.  The program tests `i < n / 2` before it computes `2i + 1`, so no index wraps, and the compiler translates the tail recursion of `siftDown` into a loop.

## The module sorts in place

`verified_compile compiled := [swap, siftDown, heapify, heapsort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `heapsort` is function 5.  The compiler generates `compiled.heapsort.implements`, which states that the module computes `heapsort`.  The caller hands the array over as `Moved (Array UInt64)`, and every update is the array's last use, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the array in its own block.

| Theorem | File | Statement |
|---|---|---|
| `swap_get`, `swap_perm` | [The proof](Proof.lean) | An exchange changes the two positions and no other, and it permutes the elements. |
| `maxChild_spec` | [The proof](Proof.lean) | The larger child of node `i < n / 2` is `2i + 1` or `2i + 2`, lies below `n`, and holds a word at least as large as each child. |
| `siftDown_eq` | [The proof](Proof.lean) | The sift's two branches move to the larger child, `maxChild`, which the proof defines. |
| `siftDown_frame` | [The proof](Proof.lean) | The sift keeps the size, permutes the elements, leaves the elements at `n` and beyond unchanged, and keeps every upper bound on the elements below `n`. |
| `siftDown_spec` | [The proof](Proof.lean) | When the heap order holds at every node at or after `L` except the moving node `i`, and, when `L < i`, the children of `i` are at most the parent of `i`, the sift makes the heap order hold at every node at or after `L`. |
| `heap_root` | [The proof](Proof.lean) | In a heap the root is the largest element. |
| `heapify_spec` | [The proof](Proof.lean) | `heapify n a` keeps the size, permutes the elements, and makes `a[0, n)` a heap. |
| `heapsort_sorted_perm` | [The proof](Proof.lean) | `heapsort` returns a permutation of its input, sorted in nondecreasing order. |
| `heapsort_eq` | [The proof](Proof.lean) | `heapsort xs = expected xs` for every array with fewer than `2^64` elements. |
| `heapsort_export` | [The compilation](Compiled.lean) | Export `heapsort` of `compiled.module` is function 5. |
| `heapsort_implements` | [The compilation](Compiled.lean) | Function 5, called with an array that the caller hands over, returns without a trap the owned array `expected xs`, with `top` raised by at most `compiled.heapsort.bound`. |
| `heapsort_bound` | [The compilation](Compiled.lean) | `compiled.heapsort.bound` is 0: the module allocates nothing. |
| `heapsort_file`, `heapsort_file_decode` | [The file theorems](File.lean) | `build/verified/heapsort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

In the proof of `heapsort_sorted_perm`, each pass of the second phase moves the root, the largest word of the prefix by `heap_root`, to the front of the suffix, and `siftDown_spec` restores the heap on the shorter prefix.  A sorted permutation is unique, which `eq_mergeSort_of_sorted_perm` of [the sorted lists](../Sorted.lean) states, so the result equals `expected`.  `heapsort_implements` is an `ImplementsA` theorem: `Verified.Call` and `Verified.CallSpec`, which the library's functions of borrowed arguments state, assume arguments that move no object, and the caller moves the array into `heapsort`.  The axiom report of `heapsort_implements` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.Heapsort.Compiled
tests/verified/run.sh --cases heapsort
tests/native/verified.sh --module heapsort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `sortInputs` in [the case inputs](../../../tests/TestSupport/Modules/Heapsort.lean): the empty array, one and two elements, sorted and reversed arrays, repeated words, the words 0, `2^63 - 1`, `2^63`, and `2^64 - 1`, the arrays `[2^64 - 1, 2^64 - 2, 1, 0]` and `[3, 1, 3, 1, 3, 1, 2]`, arbitrary words of every length from 1 to 40, arrays of 100, 255, 256, and 1,000 elements, and arrays of 300 elements in increasing order, of one repeated word, and of only 0 and `2^64 - 1`.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that the module allocates nothing beyond the host's input array and keeps one block, and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
