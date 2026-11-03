# Tree search and insertion: Algorithm T

## Request and specification

[The request](request.txt) asks for Knuth's Algorithm T on the library's `KeyTree`.  The search reports whether it finds a key and leaves the tree unchanged.  The insertion puts a new node with the key in place of the empty subtree where the search ends, changes no other link, reuses the tree's nodes, allocates no node but the new one, and runs with a call stack that does not grow.  On a binary search tree the search must succeed exactly when the key is in the tree, and the insertion must give a binary search tree with the old keys and the new one.  [The specification](Spec.lean) states Algorithm T as `algorithmT x t`, a recursion on the tree that gives whether the search succeeds and the tree afterward, with words compared as unsigned numbers.  It extends Knuth's steps, which assume a tree with at least one node, to the empty tree, and on a tree that is not a binary search tree it follows the same comparisons, so the search can miss a key off the path and the insertion then adds a second node with that key.  A binary search tree is a tree whose keys in symmetric order increase, so its keys are distinct.  `SearchTree x t` states the guarantees, and `searchTree` proves them for every binary search tree: the search succeeds exactly when `x` is a key, the tree afterward is a binary search tree, and its keys in symmetric order are those of `t` with `x` inserted in order when the search fails.  The specification reads the requirements on storage as a bound of one node's block on the rise of the heap's `top`, which counts no block that the allocator takes from its free list, so the program text and the compiler's charge for every allocation show the reuse of the nodes.  It reads the requirement on the call stack as theorems with no call-depth premise, by the compiler's rule that every recursive function other than a recognized tail recursion, and every caller of one, takes a call depth that its theorems carry as a premise.  [The review](review.md) records the specification's two independent reviews.

## The program

[The program](Program.lean) holds `search`, a loop that follows steps T1 to T4 down a borrowed tree, and `insert`, which follows the same path in a loop that reverses the links it passes and returns in a second loop that restores them.  `descend x path t` takes apart the node at the root of `t` and rebuilds it with `path`, the nodes above it, in place of the child that the search enters, which is the left child when `x` is less than the node's key and the right child when it is greater.  When the search reaches an empty subtree, `descend` builds the new node of step T5, and when it reaches the node that holds `x`, it keeps that node, and in both cases it passes the subtree to `ascend`.  `ascend x path t` takes apart the node at the top of `path`, finds the field that holds the rest of the path by the same comparison of `x` with the node's key, and rebuilds the node with `t` in that field.  Knuth's step T5 changes one link in place, while the program writes each link on the path twice, since a node of `KeyTree` holds no link to its parent and the program keeps no stack.  Schorr and Waite introduced this reversal of links for marking list structures without a stack.

The library's `KeyTree.insert` computes the same tree by recursion, and the compiler gives it a call depth, so its trap-free theorem has a premise on the depth and its code traps when the search passes 1,000 nodes, as it does for a key above all of 1,000 keys inserted in increasing order.  The compiler translates the tail recursions of `search`, `descend`, and `ascend` into loops.  Each step of `descend` and `ascend` takes apart one node and builds one node of the same layout, and the compiler's ownership rules rebuild it in the block of the node it took apart, so the only allocation is the new node.

## The module searches and inserts with loops

`verified_compile compiled := [search, ascend, descend, insert]` in [the verified compilation](Compiled.lean) compiles the program into a module whose exports `search` and `insert` are functions 2 and 5.  The caller lends the tree to `search` and hands it over to `insert` as `Moved KeyTree`.  The theorems of the compilation have no call-depth premise.

| Theorem | File | Statement |
|---|---|---|
| `search_eq` | [The proof](Proof.lean) | `search x t` is the flag of `algorithmT x t`, for every tree. |
| `descend_eq` | [The proof](Proof.lean) | `descend x path t` returns what `ascend x path` returns from the tree of `algorithmT x t`. |
| `insert_eq` | [The proof](Proof.lean) | `insert x t` is the tree of `algorithmT x t`, for every tree. |
| `algorithmT_snd` | [The proof](Proof.lean) | The tree of `algorithmT x t` is the library's `t.insert x`. |
| `mem_keys_algorithmT`, `mem_keys_insert` | [The proof](Proof.lean) | The keys after the insertion are those of `t` and `x`, for every tree. |
| `found_algorithmT` | [The proof](Proof.lean) | On a binary search tree the search succeeds exactly when `x` is a key. |
| `ordered_algorithmT`, `ordered_insert` | [The proof](Proof.lean) | On a binary search tree the tree afterward is a binary search tree. |
| `keys_algorithmT` | [The proof](Proof.lean) | On a binary search tree the keys afterward in symmetric order are those of `t`, with `x` inserted in order when the search fails. |
| `searchTree` | [The proof](Proof.lean) | `SearchTree x t` holds for every binary search tree `t`. |
| `search_export`, `insert_export` | [The compilation](Compiled.lean) | Exports `search` and `insert` of `compiled.module` are functions 2 and 5. |
| `search_implements` | [The compilation](Compiled.lean) | Function 2, called with a key and a borrowed tree, returns without a trap the flag of `algorithmT`, with `top` raised by at most `compiled.search.bound`. |
| `insert_implements` | [The compilation](Compiled.lean) | Function 5, called with a key and a tree that the caller hands over, returns without a trap the tree of `algorithmT`, with `top` raised by at most `compiled.insert.bound`. |
| `search_bound`, `ascend_bound` | [The compilation](Compiled.lean) | `compiled.search.bound` and `compiled.ascend.bound` are 0. |
| `descend_bound`, `insert_bound` | [The compilation](Compiled.lean) | `compiled.insert.bound` is 0 when the search succeeds and 72 bytes, the block of one node, when it fails. |
| `treeSearch_file`, `treeSearch_file_decode` | [The file theorems](File.lean) | `build/verified/treeSearch.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`descend_eq` proceeds by induction on `t` for every `path`: a step of `descend` into the left child pushes a node that `ascend` takes apart again with the left child replaced, which is the node of `algorithmT`, and the right child is symmetric.  `insert_eq` follows with the empty path, from which `ascend` returns its tree.  The properties of `SearchTree` follow by induction on the tree, with the keys of the left subtree below the root's key and those of the right subtree above it.  The generated bound of `descend` sums a charge for each state of the loop up to the loop's rank, and `descend_bound` evaluates the sum by induction on the tree with `Verified.Tail.costAt_rank_eq`: a state at a node is charged nothing, and the state at an empty subtree is charged the new node's block.  The axiom reports of `search_implements`, `insert_implements`, and `insert_bound` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Trees.Search.Compiled
tests/verified/run.sh --cases treeSearch
tests/native/verified.sh --module treeSearch
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `searchInputs` in [the case inputs](../../../tests/TestSupport/Modules/TreeSearch.lean): small search trees, a search tree whose keys lie on both sides of `2^63`, a search tree of 300 words, a chain of 1,000 keys and chains of 10,000 keys on either side, a search tree of 2,000 keys whose deepest path changes direction at every node, trees with equal keys, and trees that are not search trees.  Each tree takes its keys, or for a large tree its first, middle, and last keys, with the words next to them, and the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each case of both exports with `algorithmT`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that a search leaves the host's nodes live and allocates nothing, and that an insertion leaves live the nodes of its result and allocates nothing beyond the new node.  [The native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 3: Sorting and Searching, second edition, Addison-Wesley, 1998, section 6.2.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [H. Schorr and W. M. Waite, An efficient machine-independent procedure for garbage collection in various list structures, Communications of the ACM 10(8), 1967, 501–506](https://doi.org/10.1145/363534.363554)
