# MergeSort: straight two-way merge sort, TAOCP §5.2.4

## Request, specification, and program

[The request](request.txt) asks for straight two-way merge sort of an array of words: passes that merge adjacent sorted runs of length 1, 2, 4, and so on, each pass writing into a new array of the same length.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words, as [heapsort's specification](../Heapsort/README.md) does.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and not a method.

[The program](Program.lean) sorts bottom-up, merging adjacent runs from left to right.  Knuth's Algorithm S takes its runs from the two ends of the input area and writes them to the two ends of the output area, and the left-to-right form performs the same straight two-way merges in another order of runs.  `merge src k i iEnd j jEnd out` writes the merge of the runs `src[i, iEnd)` and `src[j, jEnd)` into `out` from position `k`, taking the word of the first run while it is at most the word of the second, as `List.merge` does.  `pass src w n lo out` merges each pair of adjacent runs of width `w`, `[lo, mid)` and `[mid, hi)`, from position `lo` on.  The run ends are `runEnd lo w n = lo + min w (n - lo)`, which never exceeds `n`, so the last pair of a pass may be short or have an empty second run, and no index wraps.  `sortLoop w n xs` runs passes of widths 1, 2, 4, and so on, each into a new array `LeanExe.build n fun _ => 0`, until a run covers the array.  The width doubles while `2w < n` and becomes `n` otherwise, so it never wraps either.  `mergeSort xs` is `sortLoop 1 n xs` with `n` the array's size.  The compiler translates the tail recursions of `merge`, `pass`, and `sortLoop` into loops.

## The module sorts by merging

`verified_compile compiled := [runEnd, merge, pass, sortLoop, mergeSort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `mergeSort` is function 6.  The caller hands the array over as `Moved (Array UInt64)`, and each pass releases the array it read.  `merge` and `pass` allocate nothing, and each pass of `sortLoop` charges the block of its new array of `n` words.

| Theorem | File | Statement |
|---|---|---|
| `merge_toList` | [The proof](Proof.lean) | The merge writes `List.merge` of the two runs at `k` and keeps the rest of `out`. |
| `passList` | [The proof](Proof.lean) | One pass of width `w` on a list: `List.merge` of each pair of adjacent runs of width `w`. |
| `pass_toList` | [The proof](Proof.lean) | The array pass writes `passList` of the segment `[lo, n)` after the first `lo` words of `out`. |
| `passList_perm`, `passList_runs` | [The proof](Proof.lean) | A pass permutes its list and turns sorted runs of width `w` into sorted runs of width `2w`. |
| `sortLoop_toList`, `sortList_spec` | [The proof](Proof.lean) | The array passes compute `sortList`, which returns a sorted permutation of its list. |
| `mergeSort_eq` | [The proof](Proof.lean) | `mergeSort xs = expected xs` for every array with fewer than `2^64` elements. |
| `mergeSort_export` | [The compilation](Compiled.lean) | Export `mergeSort` of `compiled.module` is function 6. |
| `mergeSort_implements` | [The compilation](Compiled.lean) | Function 6, called with an array that the caller hands over, from a heap with room for `compiled.mergeSort.bound`, returns without a trap the owned array `expected xs`. |
| `mergeSort_bound` | [The compilation](Compiled.lean) | The room a call needs is the bound of the passes, `compiled.sortLoop.bound (1, n, xs)`, which charges one block of `n` words per pass. |
| `mergeSort_file`, `mergeSort_file_decode` | [The file theorems](File.lean) | `build/verified/mergeSort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The proof states each pass on lists and moves from the array to its list with `Array.toList`.  `List.merge_perm_append` and `List.pairwise_merge` of Lean's library give the permutation and the sortedness of each merge, and `RunsSorted w l` states that every run `l[t·w, (t+1)·w)` is sorted.  Every list satisfies `RunsSorted 1`, each pass doubles the width, and the last pass leaves a run that covers the list.  A sorted permutation is unique, which `List.Perm.eq_of_pairwise` states, so the result equals `expected`.  The axiom report of `mergeSort_implements` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.MergeSort.Compiled
tests/verified/run.sh --cases mergeSort
tests/native/verified.sh --module mergeSort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `mergeInputs` in [the case inputs](../../../tests/TestSupport/Modules/MergeSort.lean): the arrays of heapsort's cases, which cover every length from 0 to 40, and four more: 1,025 arbitrary words, whose last pass merges a run of 1,024 words with a run of one, 513 words of 13 values, and 300 and 1,025 words in decreasing order, which put a short last run ahead of its partner in every pass.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, section 5.2.4](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Verified Compiler Manual](../../../docs/verified-manual.md)
