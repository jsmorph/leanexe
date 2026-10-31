# TopologicalSort: Algorithm T of TAOCP §2.2.3

## Request, specification, and program

[The request](request.txt) asks for topological sorting: the input is a vertex count `n` followed by pairs `j, k`, each stating that vertex `j` comes before vertex `k`, and the result is the `n` vertices in an order that respects every relation, or the empty array when the relations contain a cycle.  Many inputs have several such orders, so [the specification](Spec.lean) states a property of the result and not a function.  `IsTopologicalOrder xs order` holds when `order` lists every vertex below `n` exactly once and puts the first vertex of every relation before its second.  `Valid xs` states the input format: a count and whole pairs, every vertex of which is below the count.  When `n = 0` the empty array is the only topological order, and a relation of a vertex to itself, or any cycle, admits none.

[The program](Program.lean) follows Knuth's Algorithm T.  `countPredecessors` counts, for each vertex, the relations into it (steps T1 to T3).  `initialQueue` lists the vertices without predecessors in increasing order (step T4).  `process` then takes the vertices of the queue in turn: for the vertex at position `f`, it scans the relations that start at it, decreases the count of each relation's second vertex, and appends that vertex to the queue when its count reaches 0 (steps T5 to T7).  The queue is also the output.  Knuth keeps a list of successors for each vertex, and the program scans all the relations instead, so a sort takes time proportional to the number of vertices times the number of relations.  At most `n` vertices enter the queue, so `process` runs `n` steps, and a step whose position lies past the queue scans nothing.  `topoSort` returns the queue when it holds `n` vertices and the empty array otherwise (step T8).

## The module sorts the vertices

`verified_compile compiled := [countPredecessors, initialQueue, process, topoSort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `topoSort` is function 5.  The module allocates the array of counts and the growing queue, so its call needs room for the generated bound.

| Theorem | File | Statement |
|---|---|---|
| `countPredecessors_spec` | [The proof](Proof.lean) | The counts have one word per vertex, and each is the number of relations into its vertex. |
| `initialQueue_spec` | [The proof](Proof.lean) | The initial queue lists, in increasing order, the vertices whose count is 0. |
| `inner_step` | [The proof](Proof.lean) | One relation of the scan for the vertex at position `f` keeps the scan's invariant. |
| `outer_step`, `process_spec` | [The proof](Proof.lean) | Each step of the main loop keeps `OuterInv`, which holds at the end of the loop. |
| `topoSort_spec` | [The proof](Proof.lean) | On a valid input with fewer than `2^64` words, `topoSort xs` is a topological order, or it is the empty array and no topological order exists. |
| `topoSort_export` | [The compilation](Compiled.lean) | Export `topoSort` of `compiled.module` is function 5. |
| `topoSort_call` | [The compilation](Compiled.lean) | Function 5, called from a ready store with room for `compiled.topoSort.bound xs` bytes, returns without a trap the owned array `topoSort xs` and leaves a ready store. |
| `topoSort_file`, `topoSort_file_decode` | [The file theorems](File.lean) | `build/verified/topoSort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`OuterInv` states the invariant of the main loop after `f` steps.  The queue holds distinct vertices below `n`, and every relation into a queued vertex starts at an earlier queued vertex.  The count of each vertex is the number of relations into it from vertices outside the first `f` entries of the queue, and a vertex is in the queue exactly when its count is 0.  The scan keeps the same facts with the decreases made so far, and the same count shows that the program never decreases a count below 1, so no word wraps.  At the end, a queue of `n` vertices is a topological order.  A shorter queue leaves every vertex outside it with a predecessor outside it, and in any order the first vertex outside the queue would follow that predecessor, so no topological order exists.  `topoSort_call` and `topoSort_spec` together state what the module returns.  The axiom reports of both name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Graphs.TopologicalSort.Compiled
tests/verified/run.sh --cases topoSort
tests/native/verified.sh --module topoSort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `topoInputs` in [the case inputs](../../../tests/TestSupport/Modules/TopologicalSort.lean): no vertices, vertices without relations, chains in both directions, a diamond, repeated relations, a relation of a vertex to itself, cycles of two and three vertices, a cycle reachable from an acyclic part, and arbitrary relations among 20 and 40 vertices.  [The review](review.md) records the specification's independent reviews and the classes of input that the cases leave out.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with the result of the Lean function `topoSort`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 1: Fundamental Algorithms, third edition, section 2.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [A. B. Kahn, Topological sorting of large networks, Communications of the ACM 5 (1962)](https://doi.org/10.1145/368996.369025)
- [Verified Compiler Manual](../../../docs/verified-manual.md)
