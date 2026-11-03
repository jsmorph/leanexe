# Equivalence classes: Algorithm E

## Request and specification

[The request](request.txt) asks for the equivalence classes of the elements 0 to `n - 1` under the least equivalence relation that relates the two elements of each given pair, with the least element of each element's class as the result.  The pairs come as two arrays of words, the first and the second elements, and a pair with an element of `n` or more relates nothing.  The request asks for Knuth's Algorithm E, which keeps each class as a tree of parent links in one array updated in place, with a call stack that does not grow.  [The specification](Spec.lean) states the relation of the pairs as `Paired`, its equivalence closure with Mathlib's `Relation.EqvGen` as `Equivalent`, and the result as `LeastLabels n js ks r`: `r` holds `n` words, and word `i` is the least element of the class of `i`, by Mathlib's `IsLeast`.  Pair `t` exists for `t` below the lengths of both arrays, so words past the length of the shorter array belong to no pair.  `LeastLabels` determines `r`, and it does not distinguish Algorithm E from other methods that find the classes, such as one that links the roots the other way, so the program text shows the method.  The specification reads "in place" as an update of the parent links in their own block and "a call stack that does not grow" as theorems with no call-depth premise, readings that rest on rules of the compiler which [the manual](../../../docs/verified-manual.md) states and no theorem states.  [The review](review.md) records the specification's two independent reviews.

## The program

[The program](Program.lean) marks a root as its own parent, where Knuth marks it with the parent 0 and numbers the elements from 1.  `forest` builds the array of parent links with every element a root, step E1, and takes the pairs in order, step E2.  For a pair `j ≡ k` with both elements below `n`, `merge` follows the links from `j` and from `k` to their roots with `root`, step E3, and when the roots differ, it makes the root of `j` a child of the root of `k`, step E4, by an update of the array.  `root` carries a count of steps so that the Lean function is total, and the proof shows that the count `n` never runs out.  `classes` then visits the elements in increasing order, records at each root the first element that reaches it, which is the least element of its class, and writes that element as the label of each element.  Algorithm E merges trees without regard to their sizes, so a path can pass every element, as it does after the pairs `(i, i + 1)` in increasing order, and the search for a root then takes up to `n - 1` steps.  A merge by size or path compression would shorten the paths, and the request asks for Algorithm E as Knuth states it, without either.

## The module labels the classes with loops

`verified_compile compiled := [root, merge, forest, classes]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `classes` is function 5.  The compiler translates the tail recursion of `root` into a loop and compiles the `LeanExe.loop` calls of `forest` and `classes` as loops, and the caller lends both arrays of pairs.  The axiom reports of `classes_call` and `classes_spec` name only `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | File | Statement |
|---|---|---|
| `exists_root` | [The proof](Proof.lean) | On a forest of `n` elements, fewer than `n` steps from an element reach a root. |
| `root_eq` | [The proof](Proof.lean) | `root` with a count of at least `n` returns `rootOf`, the root of the element's tree. |
| `forest_link`, `rootOf_link` | [The proof](Proof.lean) | A link from one root to another keeps a forest, and it gives the second root to every element of the first root's tree and keeps the root of every other element. |
| `merge_inv`, `forest_inv` | [The proof](Proof.lean) | After the pairs below `t`, the links form a forest, every link joins two equivalent elements, and the two elements of every pair taken whose elements are both below `n` have the same root. |
| `equivalent_iff` | [The proof](Proof.lean) | After all pairs, two elements below `n` are equivalent exactly when they have the same root. |
| `classes_spec` | [The proof](Proof.lean) | `LeastLabels n js ks (classes n js ks)` for arrays of fewer than `2^64` words. |
| `classes_export` | [The compilation](Compiled.lean) | Export `classes` of `compiled.module` is function 5. |
| `classes_call` | [The compilation](Compiled.lean) | Function 5, called with a count and two lent arrays from a ready store with room for `compiled.classes.bound`, returns without a trap the owned array `classes n js ks`. |
| `classes_bound` | [The compilation](Compiled.lean) | `compiled.classes.bound` is three blocks of `n` words, `3 * Verified.blockCost n`. |
| `unionFind_file`, `unionFind_file_decode` | [The file theorems](File.lean) | `build/verified/unionFind.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`Forest` states that a rank rises along the link of every element that is not a root, so the elements of a path are distinct, and `exists_root` follows by counting: a path of `n + 1` elements below `n` without a root would repeat one.  A link from the root `ra` to the root `rb` raises the ranks of every tree other than that of `ra` above the rank of `ra`, which keeps the ranks rising.  `classes_spec` turns the root of each element into its label: by `equivalent_iff`, the elements with the root of `i` form the class of `i`, and the loop of `classes` records the least of them.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Graphs.UnionFind.Compiled
tests/verified/run.sh --cases unionFind
tests/native/verified.sh --module unionFind
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `classInputs` in [the case inputs](../../../tests/TestSupport/Modules/UnionFind.lean): every list of at most two pairs over the elements 0 to 4 with `n = 4`, small inputs with `n = 0` and `n = 1`, arrays of different lengths, the elements `2^32`, `2^63`, and `2^64 - 1` beside elements other than 0, random pairs over 100 and 1,000 elements with some out of range, and chains and stars of 10,000 elements.  `leastLabels` computes each expected result by a search of the graph of the pairs, apart from the program.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 1: Fundamental Algorithms, third edition, Addison-Wesley, 1997, section 2.3.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
