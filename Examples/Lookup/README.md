# Lookup: the first of ten pairs

## Request, specification, and program

[The request](request.txt) asks, for 21 words `[query, key1, value1, …, key10, value10]`, for
`[value, 1]` from the first pair whose key equals the query, and for `[0, 0]` when no key matches or
the input has another length.  [The specification](Spec.lean) states it with ten ordered
comparisons.  [The program](Program.lean) runs a loop over the ten pairs with a found flag and the
value of the first match as its state, and it returns a two-word array literal.  For a shorter
input, the reads past the end give 0, Lean's default for `xs[i]!`, and the length test selects
`[0, 0]`.  `verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean)
compiles the definition into a 2,309-byte module that exports `compute`.

## The module returns the first match

The reflector reads the result's literal `#[…, …]` as two pushes onto `#[]`, so the generated
`compiled.compute.bound_eq` charges an empty block and the growth of the array at each push, and
`compute_bound` closes that bound to 232 bytes.  `lookup_call` composes the generated
`compiled.compute.trapFree` with `compute_eq` through `arrayCall` of [the shared call
theorem](../ArrayCall.lean).  The generated `compiled.compute.native` states the computation of the
C function of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | `compute` equals `expected` on every array of fewer than 2^64 words. |
| `compute_bound` | `compiled.compute.bound xs` is 232 bytes for every input. |
| `lookup_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 232 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 232 bytes. |
| `lookup_file`, `lookup_file_decode` | `build/verified/lookup.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

`compute_eq`, in [the proof of the specification](Proof.lean), splits on the input's length and
then on each of the ten key comparisons in order.  `compute_bound` rewrites the bound with
`compiled.compute.bound_eq` and evaluates it with `decide`.  `lookup_call` uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Lookup.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Lookup.Compiled Examples.Lookup.compiled.module build/verified/lookup.wasm
build/tools/leanexe-wasmtime-host call build/verified/lookup.wasm compute array-u64 \
  array-u64:42,1,10,42,20,42,30,4,40,5,50,6,60,7,70,8,80,9,90,10,100
tests/verified/run.sh --cases lookup
tests/native/verified.sh --module lookup
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository README](../../README.md#commands).
The query 42 first matches the second pair, and the call prints `[20, 1]`.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean), among them the
input of the call above, a missing key, a match at the first and last pairs, repeated keys, and
inputs of 0, 20, and 22 words, in Wasmtime against `expected` with the allocation counters.  [The
native driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled
with CompCert.  The cases state the two blocks that stay allocated, the input and the result.

## Related examples

[`TreeLookup`](../TreeLookup/README.md) has the same loop structure over a search tree.
[`Calc`](../Calc/README.md) has a loop whose state is a structure.  The VKB entry
[`loop-combinators`](../../VKB/entries/loop-combinators/README.md) holds the loop lemmas that
`compute_eq` uses.

## References

- [Verified Compiler Manual: Loops and builds](../../docs/verified-manual.md#loops-and-builds).
- [Verified Compiler Manual: Array literals and conditions on
  propositions](../../docs/verified-manual.md#array-literals-and-conditions-on-propositions).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
