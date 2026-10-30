# Lookup: the first of ten pairs

## Request, specification, and program

[The request](request.txt) asks, for 21 words `[query, key1, value1, …, key10, value10]`, for
`[value, 1]` from the first pair whose key equals the query, and for `[0, 0]` when no key matches or
the input has another length.  [The specification](Spec.lean) states it with ten ordered
comparisons.  [The program](Program.lean) runs a loop over the ten pairs with a found flag and the
value of the first match as its state, and it returns a two-word array literal.  The reads past the
end of a shorter input return 0, which Lean's `xs[i]!` also returns, and the length test selects
`[0, 0]` for such an input.  [The module definition](Module.lean) compiles it into a 1,689-byte
`lookup.wasm` that exports `compute`, and [the verified compilation](Compiled.lean) compiles the same
definition with the verified compiler into a 2,309-byte module.

## The bytes return the first match

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `lookup_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

`compute_eq` is in [the proof of the specification](Proof.lean), which the theorems of both
compilers use, and `lookup_bytes` is in [the proofs](Verify.lean).  They use only `propext`,
`Classical.choice`, and `Quot.sound`.  The loop rule and the array-literal rule prove `Implements` for the program.  With
`compute_eq`, proved by ten case splits, `Implements.congr` states it for the specification.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Lookup.Verify
mkdir -p build/lookup
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Lookup.Module Examples.Lookup.lookup.module build/lookup/lookup.wasm
build/tools/leanexe-wasmtime-host call build/lookup/lookup.wasm compute array-u64 \
  array-u64:42,1,10,42,20,42,30,4,40,5,50,6,60,7,70,8,80,9,90,10,100
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The query 42 first matches the second pair, and
the call prints `[20, 1]`.  [The module tests](../../tests/modules/run.sh) of
[`Cases.lean`](Cases.lean) run the request's sample, a missing key, a match at the first and
last pairs, repeated keys, and inputs of 0, 20, and 22 words in Wasmtime against `expected`.

## The verified compiler's module

`verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean) compiles the
same definition.  The reflector reads the result's literal `#[…, …]` as two pushes onto `#[]`,
so the generated `compiled.compute.bound_eq` charges an empty block and the growth of the array at
each push, and `compute_bound` closes that bound to 232 bytes.  `lookup_call` composes the
generated `compiled.compute.trapFree` with `compute_eq` through `arrayCall` of [the shared call
theorem](../ArrayCall.lean).

| Theorem | Statement |
|---------|-----------|
| `compute_bound` | The allocation bound of `compute` is 232 bytes for every input. |
| `lookup_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 232 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 232 bytes. |

`lookup_bytes` allows a trap at `unreachable`, which `lookup_call` excludes under its premise
of room.  The LeanExe compiler allocates the literal once, with 24 payload bytes for the length and the two
words, where the verified module allocates an empty block and grows it at each push, and its bound
charges each growth.  The generated
`compiled.compute.native` states the computation of the C function of the module's translation.

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

The call prints `[20, 1]`, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime against `expected` with the
allocation counters, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state the two blocks that stay
allocated, the input and the result.

## Related examples

[`TreeLookup`](../TreeLookup/README.md) has the same loop structure over a search tree.
[`Calc`](../Calc/README.md) has a loop whose state is a structure.  The LTG entries
[`index-loop`](../../ltg/entries/index-loop/README.md) and
[`array-literal`](../../ltg/entries/array-literal/README.md) describe the rules.

## References

- [LeanExe Compiler Manual: Loops and builds](../../docs/leanexe-manual.md#loops-and-builds).
- *The Lean Language Reference*, version 4.34.0-rc2,
  [Arrays](https://lean-lang.org/doc/reference/4.34.0-rc2/Basic-Types/Arrays/).
