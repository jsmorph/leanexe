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
`KeyTree`, which [the verified compilation](Compiled.lean) compiles into the module
`exampleTrees`.  [The test support](Cases.lean) writes a tree in the host's preorder form with
`KeyTree.describe` and builds trees with `KeyTree.arbitrary`, whose shape and keys follow arbitrary
words, `KeyTree.chain`, a chain of nodes with a leaf on the left of each, and `KeyTree.leftChain`,
a chain with a leaf on the right of each.

## The module of the library operations

[The recursive-type example](../../Verified/Examples/RecursiveTypes.lean) of the verified compiler,
`recursivetypes` in [the module registry](../../tests/verified/modules.txt), imports [the
encoding](Encode.lean) and [the library's derivation](../../Library/Trees/WordTree/Reflected.lean),
which runs `verified_recursive_type` for `KeyTree`.  Its `verified_compile compiled` compiles the
library operations `KeyTree.setKey`, `KeyTree.leftChild`, `KeyTree.splitRoot`, `KeyTree.size`, and
`KeyTree.incr`, which the program exports, beside definitions of its own over `KeyTree`: the
identity, a duplication into a pair, the empty tree, a node built from its parts, and `followRight`,
which follows right children by tail recursion.  The same module compiles the functions of
[`Words`](../Words/README.md).

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

## The module of the program's operations

`verified_compile compiled` in [the verified compilation](Compiled.lean) compiles every operation
that the program adds, from `dropRight` to `wide`, into the 10,994-byte `exampleTrees.wasm` of [the
module registry](../../tests/verified/modules.txt).  The command lists the library's `size`, `sum`,
`incr`, and `insert` first, since the operations call them, and the compilation imports the
library's derivation, as the recursive-type example does.  No rule of the dialect rejects one of
the operations, so the module leaves none out.  The registry names the module `exampleTrees`, as it
names the modules of [`Lists`](../Lists/README.md) and [`Updates`](../Updates/README.md)
`exampleLists` and `exampleUpdates`.

`addAll`, `leftSpine`, `leftSizes`, `leftHeavy`, and `wide` call themselves other than in tail
position, as the library's `size`, `sum`, `incr`, and `insert` do, so their code takes the call
depth, and so does the code of each operation that calls one of them, such as `dropSmall`,
`insertTwo`, and `sumSizes`.
The entry starts at depth 0, each call of such a function adds 1, and a recursion descends the
height of its tree, the path of left children for `leftSpine`, or the search path for `insert`.
The cases run each of these functions on chains of lengths around 1,000, with the leaves on the
left and on the right, and on a chain of 4,096 nodes, and they check that a call returns when its
deepest call stays below depth 1,000 and traps at `unreachable` otherwise.  `wide` keeps sixteen
words live across its two self-calls within the 32 positions that such a function may use.

The allocation counts of the cases show how each operation treats its trees.  `dropRight`, `trim`,
`rootAndRest`, `leftSizes`, and the second tree of `addAll` are rewritten in place without a new
record, `insertTwo` allocates one record for each new key, and `dropRight`, `trim`, `splitOr`, and
`leftSpine` release the records that they drop, as `sizeAfterDrop`, `sizeFirst`, and `droppedSize`
release the whole tree.  `keyPair`, `sizeSum`, `leftHeavy`, `sumSizes`, `wide`, and the first tree
of `addAll` stay borrowed, and `keepOld` copies its tree for `incr` and returns the tree itself.  A
record built in the branch of a match reuses the header of the innermost matched node, so `addRoot`
consumes both of its trees: when both are nodes, the result is the first tree's root record over
the second tree's children, and the code releases the other records of the first tree and the root
record of the second.  `addLeft` therefore copies the left child that its record keeps, and
`addSelf`, whose tree is the argument of both parameters of `addRoot`, keeps the tree borrowed and
passes two copies.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements`, for each listed `f` | Each function of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, with each tree in the representation of the library's `Encode` instance, returns its Lean function's result, owned by the caller, or stops at `unreachable` when its `aborts` flag allows it.  A tree that the function consumes has type `Moved KeyTree`. |
| `compiled.f.trapFree` | Calls of these functions return without a trap when `top` can rise by the function's allocation bound within the memory cap and, for a function whose code takes the call depth, when the frames condition `compiled.f.fits` places every call of the run below depth 1,000. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements every function. |
| `exampleTrees_file`, `exampleTrees_file_decode` | `build/verified/exampleTrees.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

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
tools/leanrun --timeout 60m lake build Examples.Trees.Compiled
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Examples.Trees.Compiled \
  Examples.Trees.compiled.module build/verified/exampleTrees.wasm
build/tools/leanexe-wasmtime-host call-stats build/verified/exampleTrees.wasm dropRight tree-u64 \
  tree-u64:5,1,.,.,9,.,.
build/tools/leanexe-wasmtime-host call-stats build/verified/exampleTrees.wasm addRoot tree-u64 \
  tree-u64:5,1,.,.,9,.,. tree-u64:7,2,.,.,3,.,.
tests/verified/run.sh --cases exampleTrees
tests/native/verified.sh --module exampleTrees
```

The commands build the verified compilations and their theorems, write the modules, call them in
the Wasmtime host, and run the drivers, with the setup of [the repository
README](../../README.md#commands).  The host writes a tree in preorder, key, left, right, with `.`
for a leaf.  The first call prints 3, and the second prints `6,2,.,.,10,.,.` and `stats 3 0`: the
host's three records, rewritten in place, with no new record and no free.  The third prints
`5,1,.,.,.` and `stats 3 1`, since `dropRight` keeps the root record and its left child and
releases the right child.  The fourth prints `12,2,.,.,3,.,.` and `stats 6 3`: the first tree's
root record holds the sum of the root keys over the second tree's children, and the code releases
the first tree's children and the second tree's root record.

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

[The verified compiler's cases](../../Verified/Examples/Cases.lean) of `exampleTrees` run every
operation on the trees of `keyTreeArgs` and the pairs of `keyTreePairs` of
[`Cases.lean`](Cases.lean), 1,638 cases, which the verified driver compares between the Wasmtime
host and native Lean.  Each
case that returns states the blocks left allocated and bounds the allocations, the host's records
included, and each case whose deepest call reaches depth 1,000 must trap at `unreachable`.  The
module's translation to C contains every export, and the native driver runs all the cases on it.
Without `--cases`, the verified driver also checks [the file module](File.lean) against the written
file and requires the axiom reports of both file theorems to name only `propext`,
`Classical.choice`, and `Quot.sound`.

## Related examples

[`Words`](../Words/README.md) and [`Lists`](../Lists/README.md) have records with one child and tail
recursion or loops.  [`TreeLookup`](../TreeLookup/README.md) searches a binary search tree stored in
an array.  [`Clob`](../../Demos/Clob/README.md) applies the same ownership rules to arrays.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 3, *Sorting and Searching*, 2nd ed.,
  Addison-Wesley, 1998, section 6.2.2.
