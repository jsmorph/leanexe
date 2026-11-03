# Balanced trees: Algorithm A

## Request and specification

[The request](request.txt) asks for Knuth's Algorithm A, search and insertion in a balanced binary tree whose nodes hold the balance factor.  The search reports whether it finds a key and leaves the tree unchanged.  The insertion puts a new node where the search ends, restores the balance with the single and double rotations of steps A8 and A9, reuses the tree's nodes, allocates no node but the new one, and runs with a call stack that does not grow.  On a balanced binary search tree the search must succeed exactly when the key is present, and the insertion must give a balanced binary search tree with the old keys and the new one, one level higher only when the search failed.  [The specification](Spec.lean) states the insertion as `algorithmA x t`, a recursion that gives a flag and the tree afterward, where on a balanced tree the flag tells whether the tree grew one level, with `growLeft` and `growRight` for steps A6 to A9 at one node.  A node's balance factor is the height of its right subtree minus the height of its left subtree, as a word, with −1 written `2^64 - 1`, and `Balanced` states that at every node the heights differ by at most 1 and the factor is their difference.  `SearchTree x t` states the guarantees, and `searchTree` proves them for every balanced binary search tree: the search succeeds exactly when `x` is a key, the tree afterward is a balanced binary search tree, its keys are those of `t` with `x` inserted in order when the search fails, and it is one level higher exactly when `algorithmA` reports growth, which happens only when the search fails.  The specification extends Knuth's steps to the empty tree, and on a tree whose factors do not match its heights it applies the same steps to the stored factors, with two recorded choices where Knuth's steps define no result.  [The review](review.md) records the specification's two independent reviews.

## The program

[The program](Program.lean) defines `AvlTree`, whose node holds a left subtree, a key, the balance factor, and a right subtree, and [its encoding](Encoding.lean) gives each node a record of four slots.  `search` follows the comparisons from the root in a loop.  `insert` follows the path as [tree search and insertion](../Search/README.md) does: `descend` reverses the links on the search path and puts a new node with factor 0 at its end, step A5, and `ascend` restores the links on the way back.  While the subtree below a node has grown, `ascend` applies steps A6 and A7 at that node.  A node that leaned the other way becomes balanced, and the growth stops.  A balanced node leans toward the side that grew, and the growth continues.  A node that leaned the same way is rotated by `rotateRight` or `rotateLeft`, steps A8 and A9, which stops the growth.  Knuth finds the last node with a nonzero factor on the way down and adjusts the factors below it in step A6, while `ascend` adjusts them on the way up and stops the growth at that node, which gives the same tree.  Each step of `descend` and `ascend` takes apart one node and builds one node of the same layout, and each rotation takes apart the two or three nodes that it builds.  By the compiler's ownership rules each rebuilt node takes the block of a node that the step consumed, so the generated bound charges only the new node's block of 80 bytes.

## The module inserts with loops

`verified_compile compiled := [search, rotateRight, rotateLeft, ascend, descend, insert]` in [the verified compilation](Compiled.lean) compiles the program into a module whose exports `search` and `insert` are functions 2 and 7.  The caller lends the tree to `search` and hands it over to `insert` as `Moved AvlTree`.  The theorems of the compilation have no call-depth premise, and the axiom reports of `search_implements`, `insert_implements`, and `insert_bound` name only `propext`, `Classical.choice`, and `Quot.sound`.  The statements bound the rise of `top` and do not relate the blocks of the result to those of the argument, so the program text and the compiler's charge for every allocation show the reuse of the nodes.

| Theorem | File | Statement |
|---|---|---|
| `search_eq` | [The proof](Proof.lean) | `search x t` is `searchA x t`, for every tree. |
| `growLeft_rotate`, `growRight_rotate` | [The proof](Proof.lean) | The program's rotations of a node give the trees of `growLeft` and `growRight` when the node leaned toward the side that grew. |
| `ascend_left`, `ascend_right`, `descend_eq` | [The proof](Proof.lean) | A step of `ascend` with the flag set applies `growLeft` or `growRight` to the node above, and a step with the flag clear rebuilds it, so `descend x path t` returns what `ascend` returns from the flag and the tree of `algorithmA x t`. |
| `insert_eq` | [The proof](Proof.lean) | `insert x t` is the tree of `algorithmA x t`, for every tree. |
| `growLeft_props`, `growRight_props` | [The proof](Proof.lean) | Steps A6 to A9 at a node whose subtree grew one level and leans, unless the old subtree was empty, keep the node balanced, and the node grows exactly when the flag says so. |
| `algorithmA_props` | [The proof](Proof.lean) | On a balanced tree, Algorithm A gives a balanced tree that is one level higher exactly when it reports growth. |
| `keys_growLeft`, `keys_growRight`, `keys_algorithmA` | [The proof](Proof.lean) | Rotations keep the symmetric order, and on a binary search tree the keys afterward are the old keys with `x` inserted in order when the search fails. |
| `searchTree` | [The proof](Proof.lean) | `SearchTree x t` holds for every balanced binary search tree `t`. |
| `search_export`, `insert_export` | [The compilation](Compiled.lean) | Exports `search` and `insert` of `compiled.module` are functions 2 and 7. |
| `search_implements` | [The compilation](Compiled.lean) | Function 2, called with a key and a lent tree, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.search.bound`, returns without a trap `searchA x t` and raises `top` by at most the bound. |
| `insert_implements` | [The compilation](Compiled.lean) | Function 7, called with a key and a tree that the caller hands over, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.insert.bound`, returns without a trap the tree of `algorithmA` and raises `top` by at most the bound. |
| `search_bound`, `rotateRight_bound`, `rotateLeft_bound`, `ascend_bound` | [The compilation](Compiled.lean) | The generated bounds of the search, the rotations, and the return are 0. |
| `descend_bound`, `insert_bound` | [The compilation](Compiled.lean) | `compiled.insert.bound` is 0 when the search succeeds and 80 bytes, the block of one node, when it fails. |
| `avlTree_file`, `avlTree_file_decode` | [The file theorems](File.lean) | `build/verified/avlTree.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Trees.Avl.Compiled
tests/verified/run.sh --cases avlTree
tests/native/verified.sh --module avlTree
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `avlInputs` in [the case inputs](../../../tests/TestSupport/Modules/Avl.lean): the trees that Algorithm A builds from every order of one, two, four, five, and seven keys and from four longer sequences, which together hold every case of steps A7 to A9 at the root and one and two levels below it, a tree whose keys lie on both sides of `2^63`, balanced trees of 300, 3,000, and 5,000 keys, chains of 3,000 nodes and small trees whose factors do not match their heights, and two trees that are not search trees.  Each tree of at most 16 nodes takes its keys, and a larger tree its first, middle, and last keys, each with the words next to it, and every tree takes the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 6.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
