# Heapsort: Algorithm H of TAOCP §5.2.3

## Request, specification, and program

[The request](request.txt) asks for heapsort of an array of words into nondecreasing order, in place, with no storage beyond the array.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words.  Exactly one list holds a given collection of words in nondecreasing order, so the specification names the result and not a method.

[The program](Program.lean) is Knuth's Algorithm H on the array `xs[0, n)`, whose node `i` has the children `2i + 1` and `2i + 2`.  `siftDown i n xs` moves the word at node `i` down the heap: it compares the two children, as steps H4 and H5 do, and exchanges the word with the larger child while that child holds a larger word.  Each branch names its child index directly, so the new index reads no array.  `heapify n xs` sifts the nodes `n / 2 - 1` down to 0, which makes the array a heap.  `heapsort xs` then exchanges the root, the largest word, with the last word of the heap, shrinks the heap by one, and sifts the new root down, until one word remains.  A node `i` has a child exactly when `i < n / 2`, which the program tests before it computes `2i + 1`, so no index wraps.  `swap i j xs` takes the array last, so that a caller reads the array in the other arguments before the call takes it, and `heapsort` reads the array's size once, before `heapify` takes the array.  The compiler translates the tail recursion of `siftDown` into a loop.

## The module sorts in place

`verified_compile compiled := [swap, siftDown, heapify, heapsort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `heapsort` is function 5.  The caller hands the array over as `Moved (Array UInt64)`, and every update is the array's last use, so the module changes the array in its own block.

| Theorem | File | Statement |
|---|---|---|
| `swap_get`, `swap_perm` | [The proof](Proof.lean) | An exchange changes the two positions and no other, and it permutes the elements. |
| `maxChild_spec` | [The proof](Proof.lean) | The larger child of node `i < n / 2` is `2i + 1` or `2i + 2`, lies below `n`, and holds a word at least as large as each child. |
| `siftDown_eq` | [The proof](Proof.lean) | The sift's two branches move to the larger child, `maxChild`. |
| `siftDown_frame` | [The proof](Proof.lean) | The sift keeps the size, permutes the elements, leaves the elements at `n` and beyond, and keeps every upper bound on the elements below `n`. |
| `siftDown_spec` | [The proof](Proof.lean) | When the heap order holds at every node at or after `L` except the moving node `i`, and the children of `i` are at most the parent of `i`, the sift makes the heap order hold at every node at or after `L`. |
| `heap_root` | [The proof](Proof.lean) | In a heap the root is the largest element. |
| `heapify_spec` | [The proof](Proof.lean) | `heapify` keeps the size, permutes the elements, and makes the whole array a heap. |
| `heapsort_sorted_perm` | [The proof](Proof.lean) | `heapsort` returns a permutation of its input, sorted in nondecreasing order. |
| `heapsort_eq` | [The proof](Proof.lean) | `heapsort xs = expected xs` for every array with fewer than `2^64` elements. |
| `heapsort_export` | [The compilation](Compiled.lean) | Export `heapsort` of `compiled.module` is function 5. |
| `heapsort_implements` | [The compilation](Compiled.lean) | Function 5, called with an array that the caller hands over, returns without a trap the owned array `expected xs`, with `top` raised by at most `compiled.heapsort.bound`. |
| `heapsort_bound` | [The compilation](Compiled.lean) | `compiled.heapsort.bound` is 0: the module allocates nothing. |
| `heapsort_file`, `heapsort_file_decode` | [The file theorems](File.lean) | `build/verified/heapsort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The extraction loop of `heapsort_sorted_perm` keeps a heap on the prefix `[0, e)`, a sorted suffix `[e, n)`, and every element of the prefix at most every element of the suffix.  Each step moves the root, the largest element of the prefix by `heap_root`, to the front of the suffix, and `siftDown_spec` restores the heap on the shorter prefix.  A sorted permutation is unique, which `List.Perm.eq_of_pairwise` states, so the result equals `expected`.  `heapsort_implements` is an `ImplementsA` theorem, where the library's functions of borrowed arguments state `Verified.CallSpec`, because `Verified.Call` concerns arguments that move no object.  The axiom report of `heapsort_implements` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.Heapsort.Compiled
tests/verified/run.sh --cases heapsort
tests/native/verified.sh --module heapsort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `sortInputs` in [the case inputs](../../../tests/TestSupport/Modules/Heapsort.lean): the empty array, one and two elements, sorted and reversed arrays, repeated words, the words 0, `2^63 - 1`, `2^63`, and `2^64 - 1`, arbitrary words of every length from 1 to 40, and arrays of 100, 255, 256, and 1,000 elements.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that the module allocates nothing beyond the host's input array and keeps one block, and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, section 5.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [J. W. J. Williams, Algorithm 232: Heapsort, Communications of the ACM 7 (1964)](https://doi.org/10.1145/512274.512284)
- [Verified Compiler Manual](../../../docs/verified-manual.md)
