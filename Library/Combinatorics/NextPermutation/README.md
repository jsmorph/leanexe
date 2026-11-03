# Next arrangement: Algorithm L of TAOCP §7.2.1.2

## Request and specification

[The request](request.txt) asks for the next arrangement of an array of words in lexicographic order by one step of Algorithm L: the least arrangement of the same words, repetitions included, that is greater than the input, with the flag 1, and at the greatest arrangement the least arrangement with the flag 0, in place, with a call stack that does not grow.  [The specification](Spec.lean) states the result as `IsNext xs r` through `<` on `List UInt64`, the lexicographic order of Lean's lists with words compared as unsigned numbers, and `List.Perm`.  When some arrangement of `xs` is greater than `xs`, the flag is 1 and the array is the least such arrangement, and otherwise the flag is 0 and the array is `List.mergeSort` of `xs`.  The order is total on lists of words, so `IsNext xs r` determines `r`, and the specification names the result without the steps of Algorithm L.  The theorems of the module read "in place" as a call that does not raise the heap's `top`, which is weaker than the request, since no theorem states that the result occupies the input's block, and they read "a call stack that does not grow" as theorems with no call-depth premise.  [The review](review.md) records the specification's two independent reviews and the cases that they added.

## The program

[The program](Program.lean) performs one step of Algorithm L on the array `a[0, n)` with indices from 0.  `ascent a i` is step L2: from `i = n - 1` down, it returns the last `i` with `a[i - 1] < a[i]`, or 0 when there is none, so that `j = i - 1` is the last position with `a[j] < a[j + 1]` and the words after `j` are in nonincreasing order.  `lastAbove a v lo l` is step L3: from `l = n - 1` down to `lo + 1`, with `lo = j + 1`, it returns the last position whose word exceeds `v = a[j]`, or `lo` when there is none, whose word `a[j + 1]` exceeds `a[j]`.  `nextPerm` exchanges the words at `j` and `l` with heapsort's `swap`, and `reverseRange a lo hi`, step L4, reverses the words from `j + 1` to `n - 1` by exchanges from both ends, which puts them in nondecreasing order.

Knuth's Algorithm L visits every arrangement in one run and stops at the greatest, where step L2 finds no ascent.  The program performs steps L2 to L4 once per call and, at the greatest arrangement, reverses the whole array, which gives the least arrangement, and returns the flag 0, so that repeated calls cycle through the arrangements.  Arrays of 0 and 1 words come back unchanged with the flag 0.  A call reads and writes only positions `j` to `n - 1`, so its work is proportional to `n - j`.  The program tests `0 < i` before it reads `a[i - 1]` and `lo < l` before it moves `l`, so no index wraps.

## The module

`verified_compile compiled := [swap, ascent, lastAbove, reverseRange, nextPerm]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `nextPerm` is function 6.  The compiler translates the tail recursions of `ascent`, `lastAbove`, and `reverseRange` into loops, so no theorem of the module has a call-depth premise.  The caller hands the array over as `Moved (Array UInt64)`, and every update is the array's last use, so by the compiler's [ownership rules](../../../docs/verified-manual.md#ownership) the module changes the array in its own block and returns it with the flag.

| Theorem | File | Statement |
|---|---|---|
| `lt_of_append_lt_append`, `append_lt_append` | [The proof](Proof.lean) | A common prefix does not change the order of two lists. |
| `lt_split` | [The proof](Proof.lean) | A list above `P ++ M` departs upward from a word of `P` or continues `P` with a list above `M`. |
| `not_lt_of_antitone`, `not_lt_of_monotone` | [The proof](Proof.lean) | A list in nonincreasing order lies below none of its arrangements, and a list in nondecreasing order above none. |
| `ascent_spec`, `lastAbove_spec`, `reverseRange_spec` | [The proof](Proof.lean) | Steps L2, L3, and L4 return the positions and the array that the program's docstrings describe. |
| `least_above` | [The proof](Proof.lean) | With `S` nonincreasing, no arrangement above `P ++ p :: S` lies below `P ++ q :: S'`, when `P ++ q :: S'` is an arrangement of `P ++ p :: S`, `q` is at most every word of `S` above `p`, and `S'` is nondecreasing. |
| `nextPerm_isNext` | [The proof](Proof.lean) | `nextPerm a` is the pair that `IsNext a` states, for every array of fewer than `2^64` words. |
| `list_lt_trichotomy`, `isNext_unique` | [The proof](Proof.lean) | The order on lists of words is total, so `IsNext xs` determines the flag and the array. |
| `nextPerm_export` | [The compilation](Compiled.lean) | Export `nextPerm` of `compiled.module` is function 6. |
| `nextPerm_implements` | [The compilation](Compiled.lean) | Function 6, called with an array that the caller hands over, returns without a trap the flag and the owned array of `nextPerm xs`, with `top` raised by at most `compiled.nextPerm.bound`. |
| `nextPerm_bound` | [The compilation](Compiled.lean) | `compiled.nextPerm.bound` is 0, so a call does not raise `top`. |
| `nextPermutation_file`, `nextPermutation_file_decode` | [The file theorems](File.lean) | `build/verified/nextPermutation.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

In the proof of `nextPerm_isNext`, an input without an ascent is nonincreasing, so it has no greater arrangement, and its reversal is nondecreasing, which makes it `List.mergeSort` of the input.  Otherwise the input is `P ++ a[j] :: S` with `S` nonincreasing, and the result is `P ++ a[l] :: S'`, where `a[l]` is the least word of `S` above `a[j]`, since `S` is nonincreasing and no word after `l` exceeds `a[j]`, and `S'` holds the other words of `a[j] :: S` in nondecreasing order.  An arrangement above the input either departs upward within `P`, and so lies above the result, or continues `P` with a word of `S` above `a[j]`, and so starts its remainder with a word at least `a[l]`, and when that word is `a[l]`, the rest is an arrangement of `S'`, which lies below none of them.  `nextPerm_implements` states that the module returns `nextPerm xs`, and every array that the representation of a call holds has fewer than `2^64` words, so `nextPerm_isNext` applies to it, but no theorem joins the two.  The axiom reports of `nextPerm_implements` and `nextPerm_isNext` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Combinatorics.NextPermutation.Compiled
tests/verified/run.sh --cases nextPermutation
tests/native/verified.sh --module nextPermutation
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `nextPermInputs` in [the case inputs](../../../tests/TestSupport/Modules/NextPermutation.lean): every array of up to 5 words from 0, 1, and 2, the arrangements of 1 to 5, every array of 1 to 3 words from 0, `2^63 - 1`, `2^63`, and `2^64 - 1`, arrays of 6 to 999 words drawn from those four, and long arrays of up to 20,000 words with the last ascent at the end, at the start, inside, and nowhere, among them an array on which step L3 passes over 19,997 words.  No case passes a module's result back to the module.  Each case expects the result of `expectedOf`, which computes the next arrangement by a recursion on lists that does not follow Algorithm L: the first word followed by the next arrangement of the rest, when the rest has one, and otherwise the least word of the rest above the first word followed by the other words in nondecreasing order.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that the module allocates nothing beyond the host's input array and keeps one block, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 4A: Combinatorial Algorithms, Part 1, Addison-Wesley, 2011, section 7.2.1.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
