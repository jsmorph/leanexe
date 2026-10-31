# Tree lookup: a search tree of seven nodes

## Request, specification, review, and program

This example is the first run of the verified-executable skill, which [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) replaced.  [The request](request.txt) gives a
complete binary search tree of seven nodes in breadth-first order after a query, in 15 words, and
asks for `[value, 1]` from the node whose key the search finds, `[0, 0]` after a miss at a leaf, and
`[0, 0]` for any other length.  [The specification](Spec.lean) states the request's traversal as a
recursive `search` over node numbers, with node `j`'s key at `2j + 1`, its value at `2j + 2`, and
its children at `2j + 1` and `2j + 2`.  Two fresh agents reviewed it against the request, as [the
review](review.md) records, and the second found no disagreement and checked all 22
[samples](Samples.lean) by hand.

[The program](Program.lean) runs a loop of three steps, one per level of the tree, whose state is
the node number, a found flag, and the value found.  The node number advances at every step, and the
flag and value change only at the first match, so the program needs no early exit.  The result is a
two-word array literal, zeroed when the input does not have 15 words.  The command
`verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean) compiles it
into a 2,362-byte module that exports `compute` as function 2.

## The bytes search the tree

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | `compute` equals `expected` on every array of fewer than 2^64 words. |
| `compute_bound` | `compiled.compute.bound xs` is 232 bytes for every input. |
| `compute_callSpec` | `Verified.CallSpec` of function 2 and `expected`, with the generated bound as the room: from a ready store in which `top` can rise by that bound, the call returns an owned array that holds `expected xs`, leaves a ready store, and raises `top` by at most the bound. |
| `treeLookup_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 232 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 232 bytes. |

`compute_eq` and its two lemmas are in [the proof of the specification](Proof.lean), and the other
theorems are in [the verified compilation](Compiled.lean).  They use only `propext`,
`Classical.choice`, and `Quot.sound`.  `compute_eq` unfolds the three steps and splits on the
comparisons along each of the eleven paths through the tree.

The reflector reads the result's literal `#[…, …]` as two pushes onto `#[]`, so the generated
`compiled.compute.bound_eq` charges an empty block and the growth of the array at each push, and
`compute_bound` closes that bound to 232 bytes.  `treeLookup_call` composes the generated
`compiled.compute.trapFree` with `compute_eq` through `arrayCall` of [the shared call
theorem](../ArrayCall.lean).  `compute_callSpec` states the call in the form that
`tools/verified-request-check` requires, and the generated `compiled.compute.native` states the
computation of the C function of the module's translation.  [The journal](journal.md) records the
run.

## Building, running, and testing

```sh
tools/verified-request-check treeLookup
build/tools/leanexe-wasmtime-host call build/verified-request/treeLookup/treeLookup.wasm compute \
  array-u64 array-u64:40,50,500,30,300,70,700,20,200,40,400,60,600,80,800
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup
of [the repository README](../../README.md#commands).  `tools/verified-request-check treeLookup`
checks the hashes of the reviewed specification, the statement and axioms of `compute_callSpec`,
and the 22 samples in Wasmtime and, when CompCert is found, in the module's translation to C.  The
search finds the query 40 at the root's left child's right child, and the call prints `[400, 1]`.

```sh
tools/leanrun --timeout 60m lake build Examples.TreeLookup.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.TreeLookup.Compiled Examples.TreeLookup.compiled.module build/verified/treeLookup.wasm
build/tools/leanexe-wasmtime-host call build/verified/treeLookup.wasm compute array-u64 \
  array-u64:40,50,500,30,300,70,700,20,200,40,400,60,600,80,800
tests/verified/run.sh --cases treeLookup
tests/native/verified.sh --module treeLookup
```

The first commands build the verified compilation, write the module to
`build/verified/treeLookup.wasm`, and call it with the same input.  [The verified
driver](../../tests/verified/run.sh) runs the 22 [samples](Samples.lean) in Wasmtime against
`expected` with the allocation counters, and [the native driver](../../tests/native/verified.sh)
runs them on the module's translation to C, compiled with CompCert.  The cases state the two blocks
that stay allocated, the input and the result.

## Related examples

[`Lookup`](../Lookup/README.md) has the same loop structure over ten pairs.
[`Trees`](../Trees/README.md) holds trees on the heap as records.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2.
