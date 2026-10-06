# Trees: recursion, moves, and records on the heap

## What it is

[The program](Program.lean) declares `KeyTree`, a binary tree with a word at each node, and about
thirty functions on it.  A leaf is the null pointer, and `node l k r` is a record of three slots:
the pointer to `l`, the word `k`, and the pointer to `r`.  The functions compute sizes, sums, and
heights by non-tail recursion, rewrite keys, insert into a search tree, drop and pick subtrees,
return pairs, and lend a tree to another function inside a loop.  Three module definitions compile
them: [`Module.lean`](Module.lean) gives the 3,166-byte `trees.wasm` of functions that read their
tree, [`Moves.lean`](Moves.lean) the 3,758-byte `treeMoves.wasm` of functions that consume it, and
[`Frame.lean`](Frame.lean) the 1,686-byte `treeFrame.wasm`, which exists for the depth test only.

## What it shows

A definition that calls itself other than in tail position compiles to an entry function and an
internal function `f.rec` with a depth parameter, which traps at `unreachable` at depth 1,000 so
that the deepest accepted recursion fits Wasmtime's stack.  `Func.recursion` proves such a function
by strong induction on a measure of the tree.  A function that consumes its tree rewrites the
records in place: `incr` adds 1 to every key without allocating, `insert` allocates one record for a
new key, and `dropRight` releases the records it drops.  A tree that a call consumes and the code
uses again is copied by `KeyTree.copy`, which the compiler generates and [`Copy.lean`](Copy.lean)
proves.

| Theorem | Statement |
|---------|-----------|
| `trees_bytes` | `encode` succeeds on `trees.module`, and the decoded module implements its seventeen functions, from `KeyTree.size` to `KeyTree.keyPair`. |
| `treeMoves_bytes` | The same for the eighteen functions of `treeMoves.module`, each with its consumed tree of type `Moved KeyTree`. |
| `copy_rec` in [`Copy.lean`](Copy.lean) | At any index of any module, the generated copy function, called on a borrowed tree at any depth, stops at `unreachable` or returns a pointer to an equal tree in new records, and keeps every region of the heap. |

The proofs are in [`Verify.lean`](Verify.lean), [`MovesVerify.lean`](MovesVerify.lean),
[`Node.lean`](Node.lean), and [`Copy.lean`](Copy.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  `treeFrame.wasm` has no theorem: its `KeyTree.wide` holds 24
values in its frame, the most the compiler accepts, and the depth test checks that it still returns
at depth 999 and traps at 1,000.  [The manual](../../docs/manual.md#recursion) gives the rules for
recursion, and [its section on ownership](../../docs/manual.md#ownership) the rules for moves and
lending.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Trees.Verify Examples.Trees.MovesVerify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Trees.Module Examples.Trees.trees.module build/trees/trees.wasm
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Trees.Moves Examples.Trees.treeMoves.module build/treeMoves/treeMoves.wasm
build/tools/leanexe-wasmtime-host call build/trees/trees.wasm size i64 tree-u64:5,1,.,.,9,.,.
build/tools/leanexe-wasmtime-host call-stats build/treeMoves/treeMoves.wasm insert tree-u64 \
  i64:7 tree-u64:5,1,.,.,9,.,.
```

The commands build the proofs, write two modules, and call them in the Wasmtime host, with the setup
of [the repository README](../../README.md#commands).  The host writes a tree in preorder, key,
left, right, with `.` for a leaf.  The first call prints 3, and the second prints
`5,1,.,.,9,7,.,.,.` and `stats 4 0`: the host's three records and one new record, with no free.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 2,446 cases of
[`Cases.lean`](Cases.lean) with native Lean, checks the allocation and free counts of the consuming
functions, and runs the depth test on chains of 999 and 1,000 nodes.

## Related examples

[`Words`](../Words/README.md) and [`Lists`](../Lists/README.md) have records with one child and tail
recursion or loops.  [`TreeLookup`](../TreeLookup/README.md) searches a binary search tree stored in
an array.  [`Clob`](../Clob/README.md) has the same ownership rules for arrays.  The LTG entries
[`recursive-calls`](../../ltg/entries/recursive-calls/README.md),
[`consumed-recursion`](../../ltg/entries/consumed-recursion/README.md),
[`record-reuse`](../../ltg/entries/record-reuse/README.md),
[`partial-release`](../../ltg/entries/partial-release/README.md),
[`node-match`](../../ltg/entries/node-match/README.md), and
[`tree-copy`](../../ltg/entries/tree-copy/README.md) describe the rules.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2, on binary search trees and insertion.
- [The manual's section on recursion](../../docs/manual.md#recursion), on the depth limit and the
  frame size.
