# Tree lookup: a search tree of seven nodes

## What it is

This example is the first run of [the verified-executable
skill](../../.claude/skills/verified-executable/SKILL.md), on the request of [main's Demo
3](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-3/README.md).
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
definition](Module.lean) compiles it into a 1,734-byte `treeLookup.wasm` that exports `compute`.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `compute_eq` | The program equals the specification on every array of fewer than 2^64 words. |
| `compute_implements` | Function 2 computes `compute`. |
| `treeLookup_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call with an array in memory returns the words of `expected` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), 189 lines, and they use only `propext`,
`Classical.choice`, and `Quot.sound`.  `compute_eq` unfolds the three steps and splits on the
comparisons along each of the eleven paths through the tree.  The `Implements` proof follows the
lookup example's: `Stmt.loop_spec` for the loop and `Stmt.arrayLiteral_spec` for the result.  Main's
proof of its 7,186-byte binary took 1,398 lines.  [The journal](journal.md) records the run.

## Running it

```sh
tools/demo-check treeLookup
build/tools/leanexe-wasmtime-host call build/treeLookup/treeLookup.wasm compute array-u64 \
  array-u64:40,50,500,30,300,70,700,20,200,40,400,60,600,80,800
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  `tools/demo-check treeLookup` checks the hashes
of the reviewed specification, the statement and axioms of `treeLookup_bytes`, and the 22 samples in
Wasmtime.  The query 40 is found at the root's left child's right child, and the call prints `[400,
1]`.  [The module tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) run the same
samples.

## Related examples

[`Lookup`](../Lookup/README.md) has the same loop structure over ten pairs, and its proof is the
model for this one.  [`Trees`](../Trees/README.md) holds trees on the heap as records.  [The
skill](../../.claude/skills/verified-executable/SKILL.md) gives the procedure that produced this
example.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2, on binary search trees.
- [The review](review.md) and [the journal](journal.md) of this run.
