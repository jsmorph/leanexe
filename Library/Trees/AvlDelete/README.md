# Balanced trees: deletion

## Request and specification

[The request](request.txt) asks for the deletion of a key from the balanced tree of [Algorithm A](../Avl/README.md), with the symmetric form of TAOCP §6.2.2, Algorithm D: a node with an empty subtree gives way to its other subtree, and a node with two subtrees takes the key of its successor, the leftmost node of its right subtree, and the successor gives way to its right subtree.  Knuth's step D1 tests only the right link, and his steps move the successor's node into the deleted node's place, while the program keeps the deleted node's block with the successor's key, and on a balanced tree the two methods give the same tree.  The deletion restores the balance on the way back to the root, as §6.2.3 describes, reuses the tree's nodes, allocates no node, runs with a call stack that does not grow, and leaves the tree unchanged when the key is absent.  [The specification](Spec.lean) states the deletion as `deleteA x t`, a recursion that gives a flag and the tree afterward, where on a balanced tree the flag tells whether the tree shrank one level, with `deleteMinA` for the removal of the successor and `shrinkLeftA` and `shrinkRightA` for one node above a subtree that shrank.  A node that leaned toward the shrunk side becomes balanced and shrinks, a balanced node leans to the other side and keeps its height, and a node that leaned to the other side is rotated.  The single rotation keeps the height when the child on the other side was balanced, which happens only in a deletion, and shrinks it otherwise, and the double rotation shrinks it.  `Removes x t` states the guarantees, and `removes` proves them for every balanced binary search tree: the tree afterward is a balanced binary search tree, its keys are those of `t` without `x`, it stays as it is when `x` is not a key, and it is one level lower exactly when `deleteA` reports it, which happens only when `x` is a key of `t`.  `deleteA_of_searchA` states that a failed search leaves every tree as it is, and the specification records its choices for trees whose factors do not match their heights.  [The review](review.md) records the specification's two independent reviews.

## The program

[The program](Program.lean) follows the method of [the insertion](../Avl/README.md).  `descendDel` follows the path of comparisons to `x` and reverses each link that it passes.  At the node with `x`, when one subtree is empty, `descendDel` passes the other subtree to `ascendDel`, which restores the links on the way back, adjusting each node above a subtree that shrank with `shrinkLeft` or `shrinkRight`.  When the node with `x` has two subtrees, `minDel` follows the left links of its right subtree to the successor, reversing them as well, and carries the node with `x`, whose right field holds the path above it.  `ascendMin` restores those links and, at their end, gives the node with `x` the successor's key and passes it to `ascendDel`.  Each step takes apart the nodes that it builds, so the generated bound is 0.

## The module deletes with loops

`verified_compile compiled := [isLeaf, shrinkLeft, shrinkRight, ascendDel, ascendMin, minDel, descendDel, delete]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `delete` is function 9.  The caller hands the tree over as `Moved AvlTree`.  The theorems of the compilation have no call-depth premise, and the axiom reports of `delete_implements` and `delete_bound` name only `propext`, `Classical.choice`, and `Quot.sound`.  The statements bound the rise of `top` and do not relate the blocks of the result to those of the argument, so the program text and the compiler's charge for every allocation show the reuse of the nodes.

| Theorem | File | Statement |
|---|---|---|
| `shrinkLeft_eq`, `shrinkRight_eq` | [The proof](Proof.lean) | The program's adjustments give the nodes of `shrinkLeftA` and `shrinkRightA`. |
| `ascendDel_left`, `ascendDel_right`, `ascendMin_step`, `ascendMin_found` | [The proof](Proof.lean) | A step of each return loop with the flag set applies the adjustment of the specification to the node above, and a step with the flag clear rebuilds it. |
| `minDel_eq`, `descendDel_eq` | [The proof](Proof.lean) | The loops down return what the loops up return from the flag and the tree of `deleteMinA` and `deleteA`. |
| `delete_eq` | [The proof](Proof.lean) | `delete x t` is the tree of `deleteA x t`, for every tree. |
| `shrinkLeftA_props`, `shrinkRightA_props` | [The proof](Proof.lean) | The adjustment of a node above a subtree that shrank one level keeps the node balanced, and the node shrinks exactly when the flag says so. |
| `deleteMinA_props`, `deleteA_props` | [The proof](Proof.lean) | On a balanced tree, the removals keep the tree balanced and lower it one level exactly when they report it. |
| `keys_deleteMinA`, `keys_deleteA` | [The proof](Proof.lean) | `deleteMinA` takes the first key of a tree in symmetric order and leaves the rest, and on a binary search tree the keys afterward are those of `t` without `x`. |
| `deleteA_of_searchA`, `searchA_of_not_mem` | [The proof](Proof.lean) | A failed search, which every absent key gives, leaves every tree as it is. |
| `removes` | [The proof](Proof.lean) | `Removes x t` holds for every balanced binary search tree `t`. |
| `delete_export` | [The compilation](Compiled.lean) | Export `delete` of `compiled.module` is function 9. |
| `delete_implements` | [The compilation](Compiled.lean) | Function 9, called with a key and a tree that the caller hands over, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.delete.bound`, returns without a trap the tree of `deleteA` and raises `top` by at most the bound. |
| `delete_bound` | [The compilation](Compiled.lean) | `compiled.delete.bound` is 0, so a call does not raise `top`. |
| `avlDelete_file`, `avlDelete_file_decode` | [The file theorems](File.lean) | `build/verified/avlDelete.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Trees.AvlDelete.Compiled
tests/verified/run.sh --cases avlDelete
tests/native/verified.sh --module avlDelete
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `deleteInputs` in [the case inputs](../../../tests/TestSupport/Modules/AvlDelete.lean): the trees of the insertion's cases, twelve balanced trees, which with them hold every case of a shrunk subtree at every location and depth, and six trees whose factors do not match their heights or whose keys repeat.  Each tree of at most 40 nodes takes each of its keys and the words next to them, a larger tree its first, middle, and last keys, and every tree the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, sections 6.2.2 and 6.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
