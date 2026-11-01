# BinaryHeap: the priority queue of TAOCP §5.2.3

## Request and specification

[The request](request.txt) asks for a priority queue of words kept as a binary heap.  The input is a sequence of operations, each a pair of words: code 0 inserts the value, and any other code removes the largest word of the queue and outputs it, or does nothing when the queue is empty.  The result is the sequence of outputs.  [The specification](Spec.lean) runs the operations on a list that holds the queue's words in any order: `runOps` adds an inserted value to the list, and a removal outputs `largest`, the largest word of the list, and deletes one copy of it.  `operations` reads the pairs `xs[2i], xs[2i + 1]` and ignores a last word without a partner, a removal ignores its value, and `expected xs` is the list of outputs.  The specification fixes the outputs and leaves the arrangement of the words to the program.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) keeps the queue as the heap of TAOCP §5.2.3 in the prefix `h[0, n)` of an array: node `i` is the parent of nodes `2i + 1` and `2i + 2`, where Knuth numbers the nodes from 1 and gives node `j` the children `2j` and `2j + 1`, and every node is at or above its children, as in [heapsort](../../Sorting/Heapsort/README.md).  An insertion writes the value at position `n`, or appends it when the array holds exactly `n` words, and `siftUp` exchanges it with its parent, node `(i - 1) / 2`, while the parent holds a smaller word, as the procedure INHEAP of J. W. J. Williams's Algorithm 232 moves a new element up its heap.  A removal outputs the root, copies the last word of the heap to the root, and moves that word down the heap of `n - 1` words with heapsort's `siftDown`, steps H3 to H8 of Algorithm H, as Williams's OUTHEAP does.  `step` performs one operation on the state of the outputs, the heap's size, and the array, and `heapQueue` runs it once for each pair of the input.  A removal leaves the array's size unchanged, and a later insertion overwrites the word past the heap.

The loop keeps `Agrees`: `n` is at most the array's size, `h[0, n)` is a heap, its words are a permutation of the specification's list, and the outputs are equal.  The sift up keeps the heap order at every node except between the moving node and its parent, with the children of the moving node at most that parent, which `siftUp_spec` states, and the sift down keeps the invariant of heapsort's `siftDown_spec`.  An operation that leaves a heap of `s ≥ 1` words moves one word at most `⌊lg s⌋` levels, with one exchange at each level: an inserted word starts at depth `⌊lg s⌋` and rises, and the word copied to the root descends at most the height of the root, `⌊lg s⌋`, with at most two comparisons at each level.

Williams's heap keeps its least element at the root, and his procedures, like Knuth's step H7, move a word into the vacant node at each level and store the moving word once, where the program exchanges two words at each level.  Each component of the state that `step` returns chooses its own new value, so the loop's body ends in one tuple, since the compiler does not accept a body that chooses among whole states with nested `if`s.  The outputs come first in the state, so the body reads the root before it changes the array, and the compiler translates the tail recursions of `siftUp` and `siftDown` into loops.

## The module computes the outputs

`verified_compile compiled := [swap, siftDown, siftUp, heapQueue]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `heapQueue` is function 5.  The compiler unfolds `step` into the loop of `heapQueue`, whose state owns the two arrays, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) each operation changes them in place.  The generated bound `compiled.heapQueue.bound` counts the blocks of the two empty arrays that the loop starts from and one word of growth for each push onto either array, and no copy.

| Theorem | File | Statement |
|---|---|---|
| `largest_eq` | [The proof](Proof.lean) | A word of a list that is at least every word of the list is `largest` of the list. |
| `take_perm_of_frame` | [The proof](Proof.lean) | Two arrays that are permutations of each other and agree at `m` and beyond have prefixes `[0, m)` that are permutations of each other. |
| `remove_perm` | [The proof](Proof.lean) | The words of `h[0, j + 1)` are the root and the words of `h[0, j)` after the word at `j` replaces the root. |
| `siftUp_frame` | [The proof](Proof.lean) | `siftUp i` keeps the size, permutes the words, and leaves the words after position `i` unchanged. |
| `siftUp_spec` | [The proof](Proof.lean) | When the heap order on `a[0, m)` holds at every node except between `i` and its parent, and the children of `i` are at most the parent of `i`, `siftUp i` makes `a[0, m)` a heap. |
| `insert_spec` | [The proof](Proof.lean) | After an insertion, `[0, n + 1)` is a heap whose words are the queue's words and the new value. |
| `remove_spec` | [The proof](Proof.lean) | On a heap of `n > 0` words, the root is `largest` of the queue, and after the removal `[0, n - 1)` is a heap whose words are the queue's words with one copy of the root deleted. |
| `runOps_eq` | [The proof](Proof.lean) | `runOps` is a fold of `specStep`, one operation of the list queue. |
| `step_agrees` | [The proof](Proof.lean) | One operation keeps `Agrees`, the invariant of the loop. |
| `heapQueue_eq` | [The proof](Proof.lean) | `heapQueue xs = expected xs` for every array with fewer than `2^64` words. |
| `heapQueue_export` | [The compilation](Compiled.lean) | Export `heapQueue` of `compiled.module` is function 5. |
| `heapQueue_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for `compiled.heapQueue.bound xs` bytes, function 5 returns `expected xs` without a trap and leaves a ready store, as `Verified.CallSpec` states. |
| `heapQueue_file`, `heapQueue_file_decode` | [The file theorems](File.lean) | `build/verified/heapQueue.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`Agrees` states the heap order with heapsort's `HeapFrom` from node 0.  An insertion keeps `Agrees` by `siftUp_spec`, and a removal by heapsort's `siftDown_spec`.  The root of a heap is its largest word, heapsort's `heap_root`, so the removal outputs `largest` of the list, and `remove_perm` shows that the remaining words are the list with that word deleted.  After `k` operations the heap's size and the array's size are at most `k`, which is below `2^63`, so `n + 1` and the array's size as a word do not wrap.  The axiom report of `heapQueue_callSpec` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Queues.BinaryHeap.Compiled
tests/verified/run.sh --cases heapQueue
tests/native/verified.sh --module heapQueue
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `heapInputs` in [the case inputs](../../../tests/TestSupport/Modules/BinaryHeap.lean): the empty input, a word without a partner, removals from the empty queue, repeated words, the words 0, `2^63`, and `2^64 - 1`, removal codes other than 1, a heap that shrinks and grows again in the same array, insertions in increasing and decreasing order, and long sequences of arbitrary operations.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [J. W. J. Williams, Algorithm 232: Heapsort, Communications of the ACM 7(6):347–348, 1964](https://doi.org/10.1145/512274.3734138)
