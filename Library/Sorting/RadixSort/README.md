# Radix sort by distribution counting, TAOCP §5.2 and §5.2.5

## Request and specification

[The request](request.txt) asks for a least-significant-digit radix sort of an array of words: eight passes, one for each byte from the least significant, each a stable distribution counting sort by Algorithm D of TAOCP §5.2 from one array into another, with no allocation but a second array of the same size and 256 counts, and with a call stack that does not grow.  [The specification](Spec.lean) states the result as `expected xs`, the array's elements in the order of Lean's `List.mergeSort` with the unsigned comparison of words, as for the library's other sorts.  Exactly one list holds the same words with the same repetitions in nondecreasing order, so the specification names the result and leaves the method to the program.  The theorems of the module read the allocation requirement as a call that raises the heap's `top` by at most `blockCost n + blockCost 256`, the costs of a second array and of 256 counts, which is weaker than the request, since allocations from free blocks below `top` do not raise it and no theorem states that the call releases the two arrays or that the result occupies the input's block.  They read "a call stack that does not grow" as theorems with no call-depth premise.  [The review](review.md) records the specification's two independent reviews and the cases that they added.

## The program

[The program](Program.lean) sorts on the byte `digit s x` of each word `x` at bit `s`, for `s` from 0 to 56 in steps of 8.  `countDigits` performs steps D1 to D4 of Algorithm D: it clears the 256 counts, counts the words of each byte value, and accumulates the counts, so that `count[v]` becomes the number of words whose byte is at most `v`.  `distribute` performs steps D5 and D6: for `j` from `n - 1` down to 0, it puts the word `src[j]` at position `count[d] - 1` of `dst`, where `d` is its byte, and decreases `count[d]`, where Knuth, with positions from 1, puts it at `count[d]`.  Because the loop runs from the last word to the first, words with the same byte keep their order, so each pass is stable.

`passes` distributes `src` into `dst` and then calls itself with the two arrays exchanged and the counts reused, so the eighth pass moves the words into the array that held the input, which by the compiler's ownership rules occupies the input's block.  `radixSort` builds the second array and the counts once.  A pass goes over the `n` words twice, to count and to distribute, and over the 256 counts twice, to clear and to accumulate, so each of the eight passes takes time proportional to `n + 256`.

## The module

`verified_compile compiled := [digit, countDigits, distribute, passes, radixSort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `radixSort` is function 6.  The compiler translates the tail recursion of `passes` and the loops of `countDigits` and `distribute` into loops, so no theorem of the module has a call-depth premise.  The caller hands the array over as `Moved (Array UInt64)`, and every update of an array or of the counts is its last use, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the arrays in their blocks.

| Theorem | File | Statement |
|---|---|---|
| `digit_lt`, `digit_eq` | [The proof](Proof.lean) | A byte is below 256, and the byte at bit `8k` is `x / 2^(8k) % 256`. |
| `countDigits_spec` | [The proof](Proof.lean) | Steps D1 to D4 leave 256 counts, with `count[v]` the number of words whose byte is at most `v`. |
| `pos` | [The proof](Proof.lean) | The position of the word at `j` after a pass: the number of words with a smaller byte, plus the number of words before `j` with the same byte. |
| `pos_lt`, `pos_injective`, `pos_lt_of_digit_lt`, `pos_lt_of_lt` | [The proof](Proof.lean) | The positions lie below the size and are distinct, a smaller byte gives an earlier position, and of two words with the same byte the earlier gives the earlier position. |
| `distribute_spec` | [The proof](Proof.lean) | With the counts of steps D1 to D4, steps D5 and D6 put the word at `j` at `pos s src j`. |
| `pass_spec` | [The proof](Proof.lean) | A pass permutes the words, and when a relation `R` holds between the words of the input in order, the output is in nondecreasing order of the byte, with `R` between words of the same byte. |
| `low_step` | [The proof](Proof.lean) | Two words in order by byte `k`, or with equal byte `k` and in order modulo `2^(8k)`, are in order modulo `2^(8(k + 1))`. |
| `passes_spec` | [The proof](Proof.lean) | From byte `k`, on words in nondecreasing order modulo `2^(8k)`, the passes return a permutation in nondecreasing order. |
| `radixSort_eq` | [The proof](Proof.lean) | `radixSort xs = expected xs` for every array of fewer than `2^64` elements. |
| `radixSort_export` | [The compilation](Compiled.lean) | Export `radixSort` of `compiled.module` is function 6. |
| `radixSort_implements` | [The compilation](Compiled.lean) | Function 6, called with an array that the caller hands over, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.radixSort.bound`, returns without a trap the owned array `expected xs` and raises `top` by at most the bound. |
| `radixSort_bound` | [The compilation](Compiled.lean) | `compiled.radixSort.bound` is `blockCost n + blockCost 256`, the costs of the program's two builds. |
| `radixSort_file`, `radixSort_file_decode` | [The file theorems](File.lean) | `build/verified/radixSort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

In the proof of `pass_spec`, the positions `pos s src j` form a bijection of the indices, so the output is the input permuted, which `Equiv.Perm.ofFn_comp_perm` turns into `List.Perm`, and the order of the positions gives the order of the bytes and, for equal bytes, the order of the input.  `low_step` then gives the order modulo `2^(8(k + 1))` from the order of byte `k` and, for equal bytes, the order modulo `2^(8k)`, and after eight passes the order modulo `2^64` is the order of the words.  A sorted permutation is unique, which `eq_mergeSort_of_sorted_perm` of [the sorted lists](../Sorted.lean) states, so the result equals `expected`.  The axiom report of `radixSort_implements`, whose proof uses `radixSort_eq`, names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Sorting.RadixSort.Compiled
tests/verified/run.sh --cases radixSort
tests/native/verified.sh --module radixSort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `radixInputs` in [the case inputs](../../../tests/TestSupport/Modules/RadixSort.lean): the inputs of quicksort, which include those of straight insertion and heapsort, for each byte 300 words that differ only in that byte and 300 words whose higher bytes are fixed, eight arrays of 300 words whose bytes are 0 or 255, 2,000 words whose bytes lie in 0 to 3, 2,000 words whose middle bytes are 0, and 17,000 words with the same lowest byte.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each array with `expected`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that a call makes at most three allocations, the host's input array, the second array, and the counts, and leaves one block, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, sections 5.2 and 5.2.5](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
