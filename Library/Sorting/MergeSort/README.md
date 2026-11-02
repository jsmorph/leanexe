# MergeSort: straight two-way merge sort, TAOCP §5.2.4

## Request and specification

[The request](request.txt) asks for straight two-way merge sort of an array of words: passes that merge adjacent sorted runs of length 1, 2, 4, and so on, each pass writing into a new array of the same length.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words, as [heapsort's specification](../Heapsort/Spec.lean) does.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and leaves the method to the program, and only the program text shows the bottom-up merges and the new array of each pass.  The theorems concern arrays of fewer than `2^64` elements, which every array in memory is.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) sorts bottom-up, as Knuth's Algorithm S does, with passes that merge runs of width 1, 2, 4, and so on, until a run covers the array.  `merge src k i iEnd j jEnd out` merges the runs `src[i, iEnd)` and `src[j, jEnd)` into `out` from position `k`, as steps S3 to S11 merge a pair of runs: it takes the word of the first run while it is at most the word of the second, as `List.merge` does, and copies the rest of the other run when one run ends.  `pass src w n lo out` merges each pair of adjacent runs of width `w`, `[lo, mid)` and `[mid, hi)`, from position `lo` on, with the run ends `runEnd lo w n = lo + min w (n - lo)`, so the last pair of a pass may be short or have an empty second run.  `sortLoop w n xs` runs the passes, each into a new array `LeanExe.build n fun _ => 0`, and doubles the width while `2w < n`, as step S13 doubles Knuth's `p`, and sets it to `n` otherwise, which ends the loop.  `mergeSort xs` is `sortLoop 1 n xs` with `n` the array's size, and the compiler translates the tail recursions of `merge`, `pass`, and `sortLoop` into loops.

Before the pass of width `w`, every run `[tw, (t + 1)w)` of the array is sorted, which `RunsSorted w` states of the array's list, and the pass permutes the words and leaves every run of width `2w` sorted.  The widths are the powers of 2 below `n`, so a sort of `n ≥ 1` words makes `⌈lg n⌉` passes, allocates an array of `n` words for each, and writes every word once in each pass.  While both runs hold words, a comparison decides each word that the merge writes, at most `a + b − 1` times for runs of `a` and `b` words, and once one run ends the merge copies the rest of the other, so a pass makes at most `n − 1` deciding comparisons and the sort at most `(n − 1)⌈lg n⌉`.  The module evaluates both parts of the merge's test, as it does for every [connective](../../../docs/verified-manual.md#array-literals-and-conditions-on-propositions), so it compares two words each time the merge tests its condition, `a + b + 1` times for runs of `a` and `b` words: once for each word that it writes and once to stop.

Knuth's Algorithm S takes its runs from the two ends of one area of `N` records and writes the merged runs to the two ends of the other area, alternating between the two areas, and copies the records back to the first area when the last pass ends in the second.  The program pairs adjacent runs from left to right, as the request describes, writes each pass into a new array, and returns the array of the last pass.  Both orders of the runs give the same result, the one sorted permutation of the input.  Each run end is at most `n`, and the width doubles only while `2w < n`, so neither an index nor the width wraps.

## The module sorts by merging

`verified_compile compiled := [runEnd, merge, pass, sortLoop, mergeSort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `mergeSort` is function 6.  The compiler generates `compiled.mergeSort.implements`, which states that the module computes `mergeSort`.  The caller hands the array over as `Moved (Array UInt64)`, and each pass releases the array it read.

| Theorem | File | Statement |
|---|---|---|
| `merge_toList` | [The proof](Proof.lean) | The merge writes `List.merge` of the two runs at `k` and keeps the rest of `out`. |
| `pass_toList` | [The proof](Proof.lean) | The array pass writes `passList` of the segment `[lo, n)` after the first `lo` words of `out`. |
| `passList_perm`, `passList_runs` | [The proof](Proof.lean) | A pass permutes its list and turns sorted runs of width `w` into sorted runs of width `2w`. |
| `sortLoop_toList`, `sortList_spec` | [The proof](Proof.lean) | The array passes compute `sortList`, which returns a sorted permutation of its list. |
| `mergeSort_eq` | [The proof](Proof.lean) | `mergeSort xs = expected xs` for every array with fewer than `2^64` elements. |
| `mergeSort_export` | [The compilation](Compiled.lean) | Export `mergeSort` of `compiled.module` is function 6. |
| `mergeSort_implements` | [The compilation](Compiled.lean) | Function 6, called with an array that the caller hands over, from a heap with room for `compiled.mergeSort.bound`, returns without a trap the owned array `expected xs`. |
| `mergeSort_bound` | [The compilation](Compiled.lean) | `compiled.mergeSort.bound xs` equals `compiled.sortLoop.bound (1, n, xs)`, the bound of the passes. |
| `mergeSort_file`, `mergeSort_file_decode` | [The file theorems](File.lean) | `build/verified/mergeSort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The proof states each pass on lists with `passList w l`, which merges each pair of adjacent runs of width `w` with `List.merge`, and moves from the array to its list with `Array.toList`.  `List.merge_perm_append` and `List.pairwise_merge` of Lean's library give the permutation and the sortedness of each merge.  Every list satisfies `RunsSorted 1`, each pass doubles the width, and the last pass leaves one run that covers the list.  A sorted permutation is unique, which `eq_mergeSort_of_sorted_perm` of [the sorted lists](../Sorted.lean) states, so the result equals `expected`.  The axiom report of `mergeSort_implements` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.MergeSort.Compiled
tests/verified/run.sh --cases mergeSort
tests/native/verified.sh --module mergeSort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `mergeInputs` in [the case inputs](../../../tests/TestSupport/Modules/MergeSort.lean): the arrays of heapsort's cases, which cover every length from 0 to 40, and four more: 1,025 arbitrary words, whose last pass merges a run of 1,024 words with a run of one, 513 words of 13 values, and 300 and 1,025 words in decreasing order, in which every merge writes all of its second run, a short last run included, before its first.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 5.2.4](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
