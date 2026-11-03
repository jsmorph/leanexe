# Equivalence classes with path compression and union by size

## Request and specification

[The request](request.txt) asks for the least element of the class of each element `0` to `n - 1` under the least equivalence relation that relates the two elements of each pair, with the trees of parent links of Algorithm E of TAOCP §2.3.3, path compression, and union by size, with the parent links and the sizes updated in place and a call stack that does not grow.  The specification is `LeastLabels` of [the module of Algorithm E](../UnionFind/README.md), which [its specification](../UnionFind/Spec.lean) states: the result holds `n` words, and word `i` is the least element equivalent to `i`, where a pair with an element of `n` or more relates nothing.  The specification names the result and not the method, so this module and the module of Algorithm E use it, and [this module's specification file](Spec.lean) records its reading of the request: four arrays of `n` words, the parent links and the sizes updated in place, and the program text as the only statement of path compression and union by size.  [The review](review.md) records the specification's two independent reviews and the cases that they added.

## The program

[The program](Program.lean) keeps the parent links and the size of each tree at its root in two arrays of `n` words, with every element first a root of a tree of size 1.  For each pair `j ≡ k` whose elements are both below `n`, `unite` finds the roots `rj` and `rk` with `root`, the step of Algorithm E that follows the links, and `compress` gives every element on the path from `j` to `rj` the parent `rj`, and every element on the path from `k` to `rk` the parent `rk`.  When the roots differ, the root whose recorded size is smaller becomes a child of the other root, whose recorded size grows by the smaller one, and with equal sizes the root of `k` becomes a child of the root of `j`.  The recorded size at each root is the number of elements of its tree, which no theorem states.  `classes` then labels each element with the least element of its class by the loop of the module of Algorithm E, which records, at each root, the first element that reaches it.

Union by size keeps every tree of `k` elements at a height of at most `⌊lg k⌋`, and with path compression, as Tarjan showed in 1975, a sequence of `m ≥ n` finds and at most `n - 1` unions on `n` elements takes time proportional to `m α(m, n)`, where `α` is a functional inverse of Ackermann's function.  The proofs do not state either bound, since the specification states only the result.  `root` and `compress` take the count `n` as fuel, so they stop on every input, and on a forest of `n` elements a path never exhausts it.

## The module

`verified_compile compiled := [root, compress, unite, forest, classes]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `classes` is function 6.  The compiler translates the tail recursions of `root` and `compress` and the loops of `forest` and `classes` into loops, so no theorem of the module has a call-depth premise, and the generated `compiled.unite.bound_eq` states a bound of 0, since `unite` updates both arrays at their last use.  The caller lends both arrays of pairs, and the module builds four arrays of `n` words: the parent links, the sizes, the least element recorded at each root, and the result.

| Theorem | File | Statement |
|---|---|---|
| `rank_mono`, `rank_lt_root` | [The proof](Proof.lean) | Along the links of a forest the rank does not decrease, and an element that is not a root has a lower rank than its root. |
| `rootOf_eq_of` | [The proof](Proof.lean) | On a forest whose links keep a function `R` and whose roots `R` fixes, the root of every element is its value under `R`. |
| `link_root` | [The proof](Proof.lean) | A link from an element to its root keeps a forest and the root of every element. |
| `compress_spec` | [The proof](Proof.lean) | Path compression keeps a forest and the root of every element, and gives each element its old parent or its root. |
| `unite_inv`, `forest_inv` | [The proof](Proof.lean) | `unite` for pair `t` keeps `Inv` of the module of Algorithm E, so after all pairs the links satisfy it. |
| `classes_spec` | [The proof](Proof.lean) | `LeastLabels n js ks (classes n js ks)` for arrays of fewer than `2^64` words, by `labels_spec`. |
| `classes_export` | [The compilation](Compiled.lean) | Export `classes` of `compiled.module` is function 6. |
| `classes_call` | [The compilation](Compiled.lean) | Function 6, called with a count and two lent arrays from a ready store with room for `compiled.classes.bound`, returns without a trap the owned array `classes n js ks`. |
| `classes_bound` | [The compilation](Compiled.lean) | `compiled.classes.bound` is four blocks of `n` words, `4 * Verified.blockCost n`. |
| `weightedUnionFind_file`, `weightedUnionFind_file_decode` | [The file theorems](File.lean) | `build/verified/weightedUnionFind.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The proof uses the invariant `Inv` of the module of Algorithm E: the links form a forest, every element is equivalent to its parent, and the two elements of every pair taken so far that are both below `n` have the same root.  The rank function of a forest increases along the link of every element that is not a root, and so from such an element to its root, so a link from such an element to its root keeps the same rank function, and the root of every element is unchanged, which `rootOf_eq_of` shows with the old roots as `R`.  `unite` links one root to the other in either direction, which `link_inv` covers, and the sizes determine only the direction, so the proof does not use them.  The axiom reports of `classes_call` and `classes_spec` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Graphs.WeightedUnionFind.Compiled
tests/verified/run.sh --cases weightedUnionFind
tests/native/verified.sh --module weightedUnionFind
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases are `weightedInputs` of [the case inputs](../../../tests/TestSupport/Modules/WeightedUnionFind.lean): the inputs of [the cases of Algorithm E](../../../tests/TestSupport/Modules/UnionFind.lean), and binomial trees of 32 and 4,096 elements whose searches of up to 12 links compress their paths.  Each case expects the result of `leastLabels`, which finds the classes by a search of the graph of the pairs.  No case can observe a parent link or a size, so the cases test the result alone.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that a call leaves three blocks, the host's two arrays and the result, after at most six allocations, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 1: Fundamental Algorithms, third edition, Addison-Wesley, 1997, section 2.3.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Robert E. Tarjan, Efficiency of a good but not linear set union algorithm, Journal of the ACM 22(2), 1975](https://doi.org/10.1145/321879.321884)
