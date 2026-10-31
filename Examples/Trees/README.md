# Trees: recursion, moves, and records on the heap

## `KeyTree` and the program's functions

[The program](Program.lean) uses `KeyTree`, a binary tree with a word at each node.  A leaf is the
null pointer, and `node l k r` is a record of three slots: the pointer to `l`, the word `k`, and the
pointer to `r`.  The functions compute sizes, sums, and heights by non-tail recursion, rewrite keys,
insert into a search tree, drop and pick subtrees, return pairs, and lend a tree to another function
inside a loop.  [The encoding](Encode.lean) exports the library's `encode`, which defines that
layout, and `encode_slotted`, which proves that every record of an encoded tree has a slot.

The type and shared operations come from [the word-tree library](../../Library/Trees/README.md), and
the program exports the library's `size`, `sum`, `height`, `incr`, `setKey`, `insert`, `leftChild`,
and `splitRoot` under `Examples.Trees.KeyTree`.  This example adds operations of its own over
`KeyTree`, which no verified module compiles.  [The test support](Cases.lean) writes a tree in the
host's preorder form with `KeyTree.describe` and builds trees with `KeyTree.arbitrary`, whose shape
and keys follow arbitrary words, and `KeyTree.chain`, a chain of nodes with a leaf on the left of
each.

## The verified compiler's module

[The recursive-type example](../../Verified/Examples/RecursiveTypes.lean) of the verified compiler,
`recursivetypes` in [the module registry](../../tests/verified/modules.txt), imports [the
encoding](Encode.lean) and [the library's derivation](../../Library/Trees/WordTree/Reflected.lean),
which runs `verified_recursive_type` for `KeyTree`.  Its `verified_compile compiled` compiles the
library operations `KeyTree.setKey`, `KeyTree.leftChild`, `KeyTree.splitRoot`, `KeyTree.size`, and
`KeyTree.incr`, which the program exports, beside definitions of its own over `KeyTree`: the
identity, a duplication into a pair, the empty tree, a node built from its parts, and `followRight`,
which follows right children by tail recursion.  The same module compiles the functions of
[`Words`](../Words/README.md).  The operations that this example adds to the library have no
verified module.

`size` and `incr` call themselves other than in tail position, so their code takes the call depth,
and the cases check that they return on a chain of 999 nodes and trap at `unreachable` on chains of
1,000 and 4,096 nodes.  `followRight` compiles as a loop and returns on the chain of 4,096 nodes.
The allocation counts of the cases show that `setKey` and `incr` rewrite the records of the tree
that they consume without allocating, that `leftChild`, `splitRoot`, and `followRight` release the
records that they drop, and that a node built from two trees allocates one record.  [The verified
compiler manual's section on calls and recursion](../../docs/verified-manual.md#calls-and-recursion)
gives the rules for guarded and tail recursion, and [its section on
ownership](../../docs/verified-manual.md#ownership) the rules for owned and borrowed trees.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, for `f` among `setKey`, `leftChild`, `splitRoot`, `size`, and `incr` | Each function of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, with each tree in the representation of [the library's `Encode` instance](../../Library/Trees/WordTree/Encoding.lean), returns its Lean function's result, owned by the caller, or stops at `unreachable` when its `aborts` flag allows it.  A tree that the function consumes has type `Moved KeyTree`. |
| `compiled.f.trapFree` | Calls of these functions return without a trap when `top` can rise by the function's allocation bound within the memory cap and, for `size` and `incr`, when the frames condition `compiled.f.fits` places every call of the run below depth 1,000. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `recursivetypes_file`, `recursivetypes_file_decode` | `build/verified/recursivetypes.wasm` holds the module's encoding and decodes to the module, as [the file module](../../Verified/Examples/RecursiveTypesFile.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.RecursiveTypes
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.RecursiveTypes \
  Verified.Examples.RecursiveTypes.compiled.module build/verified/recursivetypes.wasm
build/tools/leanexe-wasmtime-host call build/verified/recursivetypes.wasm size i64 \
  tree-u64:5,1,.,.,9,.,.
build/tools/leanexe-wasmtime-host call-stats build/verified/recursivetypes.wasm incr tree-u64 \
  tree-u64:5,1,.,.,9,.,.
tests/verified/run.sh --cases recursivetypes
tests/native/verified.sh --module recursivetypes
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the drivers, with the setup of [the repository
README](../../README.md#commands).  The host writes a tree in preorder, key, left, right, with `.`
for a leaf.  The first call prints 3, and the second prints `6,2,.,.,10,.,.` and `stats 3 0`: the
host's three records, rewritten in place, with no new record and no free.

[The verified driver](../../tests/verified/run.sh) compares the cases of [the recursive-type
cases](../../Verified/Examples/RecursiveTypesCases.lean), which build their trees with the helpers
of [`Cases.lean`](Cases.lean), between the Wasmtime host and native Lean, and it checks the blocks
left allocated and the number of allocations.  Through [the library case
map](../../tests/verified/library-cases.txt), the driver runs the cases of `size`, `incr`, `setKey`,
`leftChild`, and `splitRoot` again on `libtrees`, the library's own compilation.  [The native
driver](../../tests/native/verified.sh) runs the same cases on the module's translation to C,
compiled with CompCert, for the exports that the translation contains.  Without `--cases`, the
verified driver also checks the file module against the written file and requires the axiom reports
of both file theorems to name only `propext`, `Classical.choice`, and `Quot.sound`.  [The copy
cases](../../Verified/Examples/TreeCopyCases.lean) and [the heap sum
cases](../../Verified/Examples/HeapSumsCases.lean) build and describe their trees with the same
helpers.

## Related examples

[`Words`](../Words/README.md) and [`Lists`](../Lists/README.md) have records with one child and tail
recursion or loops.  [`TreeLookup`](../TreeLookup/README.md) searches a binary search tree stored in
an array.  [`Clob`](../../Demos/Clob/README.md) has the same ownership rules for arrays.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2.
