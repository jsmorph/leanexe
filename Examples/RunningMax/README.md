# Running maximum: the largest entry so far

## Request, specification, review, and program

This example is the first run of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md).  [The request](request.txt) asks for a new
list whose entry at each position is the largest value seen up to and including that position.
[The specification](Spec.lean) states entry `i` of the result as the largest of entries `0` through
`i` of the input, the fold of `max` from 0 over that prefix, for every position of the input.  Its
comment records the choices that the request leaves open: the numbers are unsigned 64-bit words
compared as unsigned, the list is an array of words, the empty input gives the empty result, and
the input may have any length.

Two fresh agents reviewed the specification, as [the review](review.md) records.  Neither found a
disagreement with the request.  The first named lengths that no sample covered, and four
[samples](Samples.lean) were added: lengths 6, 7, and 15, and 5,000 entries, more than a page of
memory holds for the input and the result together.  The second review checked all 21 samples.

[The program](Program.lean) folds over the input with a state of the largest entry so far and the
result so far, and each step pushes the new largest entry onto the result.  The verified compiler
grows the result in place, so a call of `n` entries allocates the result's blocks as the array
doubles.  [The verified compilation](Compiled.lean) writes a module of 1,956 bytes that exports
`compute`.

## The module computes the running maximum

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array. |
| `compute_bound` | The generated allocation bound of `compute` is at most `80 * xs.size + 72` bytes. |
| `compute_callSpec` | `Verified.CallSpec compiled.module compiled.tables 2 expected compiled.compute.bound`: function 2, the export `compute`, called with the borrowed array `xs` from a ready store with room for `top` to rise by `compiled.compute.bound xs` bytes, returns without a trap an owned array that holds `expected xs` and leaves a ready store.  Every array borrowed before the call stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most the bound. |

The three theorems use only `propext`, `Classical.choice`, and `Quot.sound`.  `compute_eq`, in
[the proof of the specification](Proof.lean), rewrites the array fold as a fold over the input's
list and proves by induction on the list, `foldl_largest`, that the fold appends the largest entry
of each nonempty prefix.  A ready store is one with the allocator invariant, a memory cap of at most
65,535 pages, and the program's tables at their addresses, and `Verified.Ready.initial` proves that
the store in which the module starts is ready.  `compute_bound` takes the paid side of the
generated bound, the empty result's block of 56 bytes, its credit of 16 bytes, and 80 bytes for each
push, which `foldCost_const` sums.  The bound grows with the input, and a ready store with room for
`80 n + 72` bytes below the memory cap meets the premise of `compute_callSpec` for an input of `n`
words.  [The journal](journal.md) records the run.

## Building, running, and testing

```sh
tools/verified-request-check runningMax
build/tools/leanexe-wasmtime-host call build/verified-request/runningMax/runningMax.wasm compute \
  array-u64 array-u64:3,1,4,1,5,9,2,6
tests/verified/run.sh --cases runningMax
tests/native/verified.sh --module runningMax
```

`tools/verified-request-check runningMax` checks the hashes of the reviewed specification and
samples, writes the statement of `compute_callSpec`, requires the theorem to prove it with the three
axioms, and runs the 21 samples in Wasmtime and, with CompCert's `ccomp` and `clightgen`, in the
module's translation to C.  It printed the theorem line, the module, `samples: 21 passed, 0
failed`, and `native samples: 21 passed, 0 failed`.  The call prints `[3, 3, 4, 4, 5, 9, 9, 9]`.
[The verified driver](../../tests/verified/run.sh) runs the samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against `expected` and requires two blocks to
stay allocated after each call, the input and the result.  [The native
driver](../../tests/native/verified.sh) runs the same cases on the module's translation to C,
compiled with CompCert, which takes `ccomp`, `clightgen`, and the runtime directory as its header
describes.

## Related examples

[`Increment`](../Increment/README.md) and [`Gcd`](../../Library/Numerics/Arithmetic/Gcd/README.md)
hold the worked examples of `Verified.CallSpec`, `compute_callSpec` and `gcd_callSpec`.  The fold
over a pair whose second part grows by pushes follows `pair` of [the fold
example](../../Verified/Examples/Fold.lean).

## References

- [The verified compiler manual](../../docs/verified-manual.md), on the dialect, the generated
  theorems, and the bounds.
- [The call theorem](../../Verified/Call.lean), which defines `Verified.Ready`, `Verified.Call`,
  and `Verified.CallSpec`.
- [The review](review.md) and [the journal](journal.md) of this run.
