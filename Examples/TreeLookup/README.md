# Tree lookup: a search tree of seven nodes

## Request, specification, review, and program

This example is the first run of [the verified-executable
skill](../../.claude/skills/verified-executable/SKILL.md).
[The request](request.txt) gives a complete binary search tree of seven nodes in breadth-first
order after a query, in 15 words, and asks for `[value, 1]` from the node whose key the search
finds, `[0, 0]` after a miss at a leaf, and `[0, 0]` for any other length.  [The
specification](Spec.lean) states the request's traversal as a recursive `search` over node numbers,
with node `j`'s key at `2j + 1`, its value at `2j + 2`, and its children at `2j + 1` and `2j + 2`.
Two fresh agents reviewed it against the request, as [the review](review.md) records, and the
second found no disagreement and checked all 22 [samples](Samples.lean) by hand.

[The program](Program.lean) runs a loop of three steps, one per level of the tree, whose state is
the node number, a found flag, and the value found.  The node number advances at every step, and the
flag and value change only at the first match, so the program needs no early exit.  The result is a
two-word array literal, zeroed when the input does not have 15 words.  [The module
definition](Module.lean) compiles it into a 1,734-byte `treeLookup.wasm` that exports `compute`, and
[the verified compilation](Compiled.lean) compiles the same definition with the verified compiler into
a 2,362-byte module.

## The bytes search the tree

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `compute_implements` | Function 2 computes `compute`. |
| `treeLookup_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

`compute_eq` and its two lemmas are in [the proof of the specification](Proof.lean), which the
theorems of both compilers use, and the other theorems are in [the proofs](Verify.lean).  They use
only `propext`, `Classical.choice`, and `Quot.sound`.  `compute_eq` unfolds the three steps and
splits on the comparisons along each of the eleven paths through the tree.  The `Implements` proof
follows the lookup example's: `Stmt.loop_spec` for the loop and `Stmt.arrayLiteral_spec` for the
result.  [The journal](journal.md) records the run.

## Building, running, and testing

```sh
tools/verified-request-check treeLookup
build/tools/leanexe-wasmtime-host call build/verified-request/treeLookup/treeLookup.wasm compute \
  array-u64 array-u64:40,50,500,30,300,70,700,20,200,40,400,60,600,80,800
```

The commands build the proofs, write the verified compiler's module, and call it in the Wasmtime
host, with the setup of [the repository README](../../README.md#commands).
`tools/verified-request-check treeLookup` checks the hashes of the reviewed specification, the
statement and axioms of `compute_callSpec`, and the 22 samples in Wasmtime and, when CompCert is
found, in the module's translation to C.  The query 40 is found at the root's left child's right child, and the call prints `[400,
1]`.  [The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run the same
samples.

## The verified compiler's module

`verified_compile compiled := [compute]` in [the verified compilation](Compiled.lean) compiles the
same definition.  The reflector reads the result's literal `#[…, …]` as two pushes onto `#[]`,
so the generated `compiled.compute.bound_eq` charges an empty block and the growth of the array at
each push, and `compute_bound` closes that bound to 232 bytes.  `treeLookup_call` composes the
generated `compiled.compute.trapFree` with `compute_eq` through `arrayCall` of [the shared call
theorem](../ArrayCall.lean).  `compute_callSpec` states the call in the form that
`tools/verified-request-check` requires.

| Theorem | Statement |
|---------|-----------|
| `compute_bound` | The allocation bound of `compute` is 232 bytes for every input. |
| `compute_callSpec` | `Verified.CallSpec` of function 2 and `expected`, with the generated bound as the room: from a ready store in which `top` can rise by that bound, the call returns an owned array that holds `expected xs`, leaves a ready store, and raises `top` by at most the bound. |
| `treeLookup_call` | Called with a borrowed array from a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 232 bytes, the export `compute` returns without a trap an owned array that holds `expected xs`.  The input stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the result, and `top` rises by at most 232 bytes. |

`treeLookup_bytes` allows a trap at `unreachable`, which `treeLookup_call` excludes under its premise
of room.  The LeanExe compiler allocates the literal once, with 24 payload bytes for the length and the two
words, where the verified module allocates an empty block and grows it at each push, and its bound
charges each growth.  The generated
`compiled.compute.native` states the computation of the C function of the module's translation.

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

The call prints `[400, 1]`, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the 22 [samples](Samples.lean) in Wasmtime against `expected` with the
allocation counters, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state the two blocks that stay
allocated, the input and the result.

## Related examples

[`Lookup`](../Lookup/README.md) has the same loop structure over ten pairs, and its proof is the
model for this one.  [`Trees`](../Trees/README.md) holds trees on the heap as records.  [The
skill](../../.claude/skills/verified-executable/SKILL.md) gives the procedure that produced this
example.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2.
