# BinarySearch: Algorithm B of TAOCP §6.2.1

## Request and specification

[The request](request.txt) asks for binary search in the form that returns the least index of a sorted array of words whose element is at least a given key, or the array's length when no element is.  [The specification](Spec.lean) states the result as `expected (xs, key)`, the number of elements of `xs` less than `key`.  On an array sorted in nondecreasing order, the elements less than the key form a prefix, so that number is the least index whose element is at least the key.  `Sorted xs` states the order: `xs[i]! ≤ xs[j]!` whenever `i ≤ j < xs.size`.  The search's result on an unsorted array is not specified, and every theorem below that concerns the result assumes `Sorted`.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) is Algorithm B of TAOCP §6.2.1 in its lower-bound form.  `lowerBound` performs step B1 by calling `search` on the whole array, and each call of `search` performs steps B2 to B5 on a half-open range `[lo, hi)` of indices.  Indices start at 0, and the range with `lo = l - 1` and `hi = u` holds Knuth's records `l` through `u`.  The array is an `Array UInt64`, and `lo`, `hi`, and the midpoint `lo + (hi - lo) / 2` are words.  The midpoint lies in `[lo, hi)`, so its computation does not wrap, where the sum `l + u` in Knuth's `⌊(l + u)/2⌋` can exceed a word.  The compiler translates the tail recursion of `search` into a loop.

The loop keeps the invariant that `search_spec` states: every element before `lo` is less than the key, and every element from `hi` on is at least the key.  Knuth assumes distinct keys in increasing order, and his step B3 compares three ways and stops at an equal key.  `search` compares two ways: when the element at the midpoint is less than the key, `lo` becomes the index after the midpoint, as in step B5, and otherwise `hi` becomes the midpoint, which stays a candidate, where step B4 sets `u ← i - 1`.  The search stops only when the range is empty, so it returns the first index of a run of equal words and the insertion point of a missing key.  On a range of even length the midpoint is the upper of the two middle indices, where Knuth's `⌊(l + u)/2⌋` is the lower.

Each iteration reads one element and compares it once with the key.  An iteration on a range of `r` elements leaves `⌊r/2⌋` or `⌊(r - 1)/2⌋` of them, so it replaces `r + 1` by `⌈(r + 1)/2⌉` or `⌊(r + 1)/2⌋`, and the loop stops when `r + 1` reaches 1.  On an array of `n ≥ 1` elements the loop runs `⌊lg n⌋` or `⌊lg n⌋ + 1` times for every key, and exactly `lg (n + 1)` times when `n + 1` is a power of 2, so an array of `2^64 - 1` elements takes 64 comparisons.

## The module returns the lower bound of a sorted array

`verified_compile compiled := [search, lowerBound]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `lowerBound` is function 3.  The compiler generates the theorems that [the Verified Compiler Manual](../../../docs/verified-manual.md#the-implements-and-trapfree-theorems) describes: `compiled.lowerBound.implements`, which states that the module computes `lowerBound`, and `compiled.lowerBound.trapFree`.  The program allocates nothing, so `compiled.lowerBound.trapFree` excludes a trap without a premise on free memory.

| Theorem | File | Statement |
|---|---|---|
| `search_spec` | [The proof](Proof.lean) | For a sorted array and a range `[lo, hi)` with `lo ≤ hi ≤ xs.size`, every element before `lo` less than the key, and every element from `hi` on at least the key, the result of `search` is at most the array's size, every element before it is less than the key, and every element from it on is at least the key. |
| `lowerBound_spec` | [The proof](Proof.lean) | The same three properties for `lowerBound` on a sorted array with fewer than `2^64` elements. |
| `lowerBound_eq` | [The proof](Proof.lean) | `lowerBound xs key = expected (xs, key)` for every sorted array with fewer than `2^64` elements. |
| `lowerBound_export` | [The compilation](Compiled.lean) | Export `lowerBound` of `compiled.module` is function 3. |
| `lowerBound_call` | [The compilation](Compiled.lean) | Function 3, called from a ready store with a sorted array and a key, returns without a trap the word of `expected (xs, key)`, leaves a ready store, and raises `top` by at most `compiled.lowerBound.bound`. |
| `binarySearch_file`, `binarySearch_file_decode` | [The file theorems](File.lean) | `build/verified/binarySearch.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`lowerBound_call` is a `Verified.Call` with the precondition `Sorted`.  The library's total functions state `Verified.CallSpec` instead, whose precondition is room for the bound.  `Verified.call_on` of [the congruence theorems](../../../Verified/Congr.lean) composes the generated `compiled.lowerBound.trapFree` with `lowerBound_eq` on the arguments that meet the precondition.  The axiom report of `lowerBound_call` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Arrays.BinarySearch.Compiled
tests/verified/run.sh --cases binarySearch
tests/native/verified.sh --module binarySearch
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `searchInputs` in [the case inputs](../../../tests/TestSupport/Modules/BinarySearch.lean).  Short arrays of 0 to 34 elements, among them arrays with repeated elements, with the words 0 and `2^64 - 1`, and with the words `2^63 - 1` and `2^63`, are searched for 0, `2^64 - 1`, each element, and each element plus and minus one, which wrap at the ends of the word range.  Five arrays of 200 to 1,000 elements, four of them with runs of 15 to 498 equal words, are searched for 0, `2^64 - 1`, and every 37th element and its neighbors.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the 1,004 cases in Wasmtime, checks that each call allocates nothing beyond the host's input array, and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, 1998, section 6.2.1](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
