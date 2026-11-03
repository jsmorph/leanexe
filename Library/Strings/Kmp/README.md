# String matching by Knuth, Morris, and Pratt

## Request and specification

[The request](request.txt) asks for every position at which a pattern of `m` bytes occurs in a text of `n` bytes, both held eight bytes to a word as [the packed bytes](../../Bytes/Packed.lean) state, by the algorithm of Knuth, Morris, and Pratt in two scans of the text, one that counts the occurrences and one that records them in a result of that size, with no allocation but the table of lengths and the result, and with a call stack that does not grow.  [The specification](Spec.lean) states `OccursAt pat m txt n i`, that `i + m ≤ n` and that the bytes `i` to `i + m - 1` of the text equal the bytes of the pattern, where a byte past the end of an array reads as zero, and `expected` lists these positions in increasing order as words.  The empty pattern therefore occurs at every position from 0 to `n`, and a pattern longer than the text occurs nowhere.  The specification names the result and not the method, and the program text shows the algorithm.  The theorems of the module read the allocation requirement as a rise of the heap's `top` by at most the two blocks, which allocations from free blocks below `top` do not raise.  [The review](review.md) records the specification's two independent reviews and the changes that they led to.

## The program

[The program](Program.lean) reads byte `i` of a packed array with `byte`.  `failure` computes, for each prefix `pat[0, q + 1)` of the pattern, the length `pi[q]` of its longest proper border, a prefix that is also a suffix.  The scan keeps in `q` the length of the longest prefix of the pattern shorter than `m` that ends at the current position of the text.  For the next byte `c`, `fall` replaces `q` by `pi[q - 1]` while `0 < q` and byte `q` of the pattern differs from `c`, and `step` adds 1 when byte `q` then equals `c`.  When the length reaches `m`, the pattern ends at the current byte, and the scan continues from `pi[m - 1]`.  `failure` is the same scan of the pattern against itself.

`count` scans the text once to count the occurrences, and `occurrences` builds an array of that size and fills it in a second scan, so the module allocates the table of `m` lengths and the result.  For the empty pattern it builds the positions from 0 to `n` in one block, and for `n = 2^64 - 1`, an array that no memory holds, it builds `n` positions and extends them by `n`.  Each scan reads each byte of the text once, and the fall-backs of a scan number at most the bytes read, since each lowers `q`, which rises by at most 1 per byte, so a scan takes time proportional to `n` and `failure` time proportional to `m`.  The proofs state neither bound.  `fall` takes the count `m` as fuel, and every fall-back lowers `q` below `m`.

## The module

`verified_compile compiled := [byte, fall, step, failure, count, occurrences]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `occurrences` is function 7.  The compiler translates the tail recursion of `fall` and the loops of `failure`, `count`, and `occurrences` into loops, so no theorem of the module has a call-depth premise.  The caller lends the pattern and the text.

| Theorem | File | Statement |
|---|---|---|
| `byte_toNat`, `byte_eq_iff` | [The proof](Proof.lean) | The program's `byte` is the byte that `byteAt` of the specification reads. |
| `Pre`, `pre_trans`, `pre_border` | [The proof](Proof.lean) | `Pre P T s i`: the first `s` bytes of `P` end before position `i` of `T`.  A border of a prefix that ends there ends there too, and a shorter prefix that ends there is a border of the longer. |
| `PiOk`, `failure_spec` | [The proof](Proof.lean) | `failure` returns `m` lengths, each the longest proper border of its prefix of the pattern. |
| `fall_spec`, `step_spec` | [The proof](Proof.lean) | From the longest prefix shorter than `L` that ends before byte `i`, the fall-back and `step` return the longest prefix of length at most `L` that ends after it. |
| `next_state` | [The proof](Proof.lean) | One byte of the scan reaches `m` exactly when the pattern ends after that byte, and keeps the scan's state. |
| `count_spec`, `positions_spec`, `count_eq_size` | [The proof](Proof.lean) | `count` counts the ends of occurrences, and the positions found are the positions of `expected`. |
| `occurrences_eq` | [The proof](Proof.lean) | `occurrences pat m txt n = expected pat m txt n` for all arrays and words. |
| `occurrences_export` | [The compilation](Compiled.lean) | Export `occurrences` of `compiled.module` is function 7. |
| `occurrences_implements` | [The compilation](Compiled.lean) | Function 7, called with a lent pattern, its length, a lent text, and its length, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.occurrences.bound`, returns without a trap the owned array `expected` and raises `top` by at most the bound. |
| `occurrences_bound` | [The compilation](Compiled.lean) | The bound is a block of `n + 1` words for the empty pattern when `n + 1` is a word, and otherwise a block of `m` lengths and a block of the result. |
| `kmp_file`, `kmp_file_decode` | [The file theorems](File.lean) | `build/verified/kmp.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The proof works with the bytes as functions of natural numbers.  From a length `k` with `Pre P T k i`, every shorter length `s` with `Pre P T s i` is a border of `P[0, k)`, so it is at most `pi[k - 1]`, and `pi[k - 1]` has the property itself, so the fall-back visits these lengths in decreasing order and `fall_spec` returns the longest that the next byte extends.  `failure_spec` applies the same step to the pattern, and the scan's invariant, `IsState`, holds the longest prefix shorter than `m` that ends at the current position, which after a full match is `pi[m - 1]`.  `occurrences_implements` composes the generated `compiled.occurrences.trapFree` with `occurrences_eq`, and the axiom reports of the theorems name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Strings.Kmp.Compiled
tests/verified/run.sh --cases kmp
tests/native/verified.sh --module kmp
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `kmpInputs` in [the case inputs](../../../tests/TestSupport/Modules/Kmp.lean): short texts with empty, long, overlapping, and repeated patterns, bytes 0, 127, 128, and 255 and bytes that differ only in bit 7, patterns and texts that cross a word, lengths beyond and within the bytes of the arrays, fall-back chains of up to 9 steps on one byte, Fibonacci words, random texts over 2 and 4 byte values with patterns cut from them, and 8,000 bytes of one value.  Each case expects `expected`, which tests every position directly.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that a call leaves three blocks, the host's two arrays and the result, after at most four allocations, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, James H. Morris Jr., and Vaughan R. Pratt, Fast pattern matching in strings, SIAM Journal on Computing 6(2), 1977](https://doi.org/10.1137/0206024)
