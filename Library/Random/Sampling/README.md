# Random shuffling: Algorithm P of TAOCP §3.4.2

## Request and specification

[The request](request.txt) asks for Algorithm P on an array of words, in place, with the random numbers supplied as an array of words, each word `u` serving as the fraction `u / 2^64` of step P3.  The result must be a permutation for every word array, and for independent uniform words every arrangement of distinct words must be equally likely up to the rounding of 64-bit fractions.  [The specification](Spec.lean) states four properties of a function `f`, which the structure `Shuffles` collects.  The result `f us xs` is Knuth's Algorithm P on the words of `us`, `algorithmP`, which exchanges the words at `j` and at `⌊(j + 1)·us[n - 1 - j] / 2^64⌋` for `j` from `n - 1` down to 1, so that the steps take the words in order.  The second and fourth properties state the guarantees that the request asks for, and the third extends the distribution to inputs with repeated words.  For arrays of fewer than `2^32` words the other three follow from the first, and their proofs check the index arithmetic of `algorithmP`.  The result is a permutation of `xs` for every word array.  The positions that `f` moves do not depend on the words, so `f us xs` is the shuffle of the positions `iota n` with each position replaced by the word of `xs` there.  For `n` distinct words and each permutation `ys` of them, the number of word arrays of length `n - 1` with `f us xs = ys` lies between `fewest n = ∏ ⌊2^64 / (j + 1)⌋` and `most n = ∏ ⌈2^64 / (j + 1)⌉`, the products over `j` from 1 to `n - 1`.

For uniform words each permutation therefore has a probability within a relative error of about `n(n - 1) / 2^65` of `1 / n!`, and the second property carries the distribution to inputs with repeated words.  Algorithm P reads only the first `n - 1` words, so further words do not change the distribution.  The method and the count concern arrays of fewer than `2^32` words, which includes every array in a 32-bit WebAssembly memory.  The theorems concern the map from word arrays to results, and whether a generator's words behave as independent uniform words lies outside them: a word array filled from one 64-bit seed reaches at most `2^64` arrangements, fewer than `n!` once `n ≥ 21`.  [The review](review.md) records the specification's two independent reviews.

## The program

[The program](Program.lean) is Knuth's Algorithm P with indices from 0.  For `j` from `n - 1` down to 1, step P2 takes the fraction `U = us[n - 1 - j] / 2^64`, so that the steps read the words in the order in which Knuth's steps generate their numbers, and step P3 exchanges the word at `j` with the word at `k = ⌊(j + 1)U⌋`, which lies from 0 to `j` because `U < 1`.  `scale u m` computes `⌊u·m / 2^64⌋` from the halves of `u = u₁·2^32 + u₀` as `⌊(u₁·m + ⌊u₀·m / 2^32⌋) / 2^32⌋`, whose products and sum stay below `2^64` when `m < 2^32`.  The exchange is heapsort's `swap`, and the loop makes `n - 1` exchanges and reads the `n - 1` words `us[0, n - 1)`.

Knuth's numbers are 1-based and his `U` is a real number, while here `U` is a 64-bit fraction, so an index `i < m` comes from `⌊2^64 / m⌋` or `⌈2^64 / m⌉` words where a real `U` would give each index the probability `1 / m` exactly.  That rounding is the only departure in the distribution.  A missing word of `us` reads as 0, which selects position 0, and arrays of 0 and 1 elements return unchanged.

The proof states Algorithm P with given indices as `byIndices k m a`, which exchanges the words at `k j` and `j` for `j` from `m` down to 1.  With indices `k j ≤ j` it permutes `a` and leaves the words after `m` in place, and the word that ends at position `m` is the word that was at `k m`.  For distinct words the last word of a result therefore fixes the last index, and by induction the whole sequence of indices, while every arrangement has a sequence of indices, obtained by moving the word that belongs at `m` there first.  The module computes `byIndices` with the indices `scale us[n - 1 - j] (j + 1)`, so the word arrays that give one arrangement are those whose word `n - 1 - j` lies, for each `j`, in the set of words that `scale` maps to the arrangement's index `j`.  Their number is the product of the sizes of those sets, and each size is the length of the interval of words `u` with `i·2^64 ≤ u·(j + 1) < (i + 1)·2^64`.

## The module

`verified_compile compiled := [scale, swap, shuffle]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `shuffle` is function 4.  The function borrows the word array and consumes the array it shuffles, which the caller hands over as `Moved (Array UInt64)`, and by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) every exchange changes the array in its own block.  The generated `compiled.shuffle.trapFree` states that function 4 returns `shuffle us xs` without a trap, and `shuffle_spec` states the properties of `shuffle`.

| Theorem | File | Statement |
|---|---|---|
| `scale_toNat`, `scale_lt` | [The index](Scale.lean) | `scale u m = ⌊u·m / 2^64⌋` when `m < 2^32`, and `scale u m < m` for every `m ≥ 1`. |
| `scale_card` | [The index](Scale.lean) | For `0 < m < 2^32` and `i < m`, between `⌊2^64 / m⌋` and `⌈2^64 / m⌉` words `u` have `scale u m = i`. |
| `byIndices_frame`, `byIndices_top` | [The proof](Proof.lean) | With indices `k j ≤ j`, `byIndices k m a` permutes `a`, keeps the words after `m`, and puts at `m` the word that was at `k m`. |
| `byIndices_unique`, `byIndices_exists` | [The proof](Proof.lean) | For distinct words in positions `0` to `m`, the result determines the indices, and every arrangement of those words has indices. |
| `shuffle_eq` | [The proof](Proof.lean) | `shuffle us xs` is `byIndices` with the indices `scale us[n - 1 - j] (j + 1)`. |
| `shuffle_method` | [The proof](Proof.lean) | `shuffle us xs = algorithmP us n (n - 1) xs` for fewer than `2^32` words, through `byIndices_eq_algorithmP`. |
| `shuffle_perm`, `shuffle_positions`, `shuffle_count` | [The proof](Proof.lean) | The other three properties of `Shuffles` for `shuffle`. |
| `shuffle_spec` | [The proof](Proof.lean) | `Shuffles shuffle`. |
| `shuffle_export` | [The compilation](Compiled.lean) | Export `shuffle` of `compiled.module` is function 4. |
| `shuffle_bound` | [The compilation](Compiled.lean) | `compiled.shuffle.bound` is 0: the module allocates nothing. |
| `shuffle_file`, `shuffle_file_decode` | [The file theorems](File.lean) | `build/verified/shuffle.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The axiom reports of `compiled.shuffle.trapFree` and `shuffle_spec` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Random.Sampling.Compiled
tests/verified/run.sh --cases shuffle
tests/native/verified.sh --module shuffle
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `shuffleInputs` in [the case inputs](../../../tests/TestSupport/Modules/Sampling.lean): arrays of 0, 1, and 2 words, the words 0, `2^64 - 1`, and `2^63`, which select positions 0, `j`, and `⌊(j + 1) / 2⌋`, a missing word with words to shuffle of 0 and `2^64 - 1`, arrays with repeated words, the least word that selects an index and the word below it, which depend on the carry from the low half in `scale`, for 3, 5, 7, 1,000, and 1,024 positions, and SplitMix64 words for the positions of every length from 2 to 40, for 100 positions with too few, exactly enough, and too many words, and for 2,000 and 4,500 positions.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each pair with Lean's `shuffle`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that the module allocates nothing beyond the host's two arrays, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, Addison-Wesley, 1997, section 3.4.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
