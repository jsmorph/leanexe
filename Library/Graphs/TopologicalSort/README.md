# TopologicalSort: Algorithm T of TAOCP §2.2.3

## Request and specification

[The request](request.txt) asks for topological sorting: the input is a vertex count `n` followed by pairs `j, k`, each stating that vertex `j` comes before vertex `k`, and the result is the `n` vertices in an order that respects every relation, or the empty array when the relations contain a cycle.  Many inputs have several such orders, so [the specification](Spec.lean) states a property of the result.  `IsTopologicalOrder xs order` holds when `order` lists every vertex below `n` exactly once and puts the first vertex of every relation before its second.  `Valid xs` states the input format: a count and whole pairs, every vertex of which is below the count, with no bound on the count.  When `n = 0` the empty array is the only topological order, a relation of a vertex to itself or any cycle admits none, and a repeated relation means the same as one copy.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) follows Knuth's Algorithm T, with the vertices numbered from 0, where Knuth numbers the objects from 1 to `n`.  `countPredecessors` performs steps T1 to T3 without the successor lists: it holds Knuth's COUNT in an array of `n` words, whose word `k` is the number of relations into vertex `k`.  `initialQueue` performs step T4: it lists the vertices whose count is 0 in increasing order.  `process` performs steps T5 to T7: step `f` of its loop takes the vertex at position `f` of the queue, scans every relation for those that start at that vertex, decreases the count of each such relation's second vertex, and appends that vertex to the queue when its count reaches 0.  `topoSort` performs step T8: it returns the queue when the queue holds `n` vertices and the empty array otherwise.

Knuth links his queue through the field QLINK and keeps, for each vertex `j`, a list of its successors that starts at TOP[j].  The program holds the queue in an array that grows at its end, with position `f` as Knuth's front F, and the queue is also the output.  A scan of the input's relations replaces the successor lists, so the loop's state holds only the counts and the queue.  At most `n` vertices are appended to the queue, so `process` runs `n` steps, and a step whose position is at least the length of the queue scans nothing.  Knuth's step T3 adds each relation at the front of its first vertex's list, so step T6 visits the successors of a vertex in the reverse of the input's order, where the program visits them in the input's order and can return a different topological order.

The main loop keeps `OuterInv` after `f` steps: the queue holds distinct vertices below `n`, every relation into a queued vertex starts at an earlier queued vertex, the count of each vertex is the number of relations into it from vertices outside the first `f` entries of the queue, and a vertex is in the queue exactly when its count is 0.  The scan keeps `InnerInv`, the same facts with the decreases made so far.  For `m` relations, the program makes `m` passes in `countPredecessors`, `n` in `initialQueue`, and `n` steps of `process`, of which only the first `L` scan, where `L ≤ n` is the final length of the queue, so the scans make `m·L` passes, `m·n` when an order exists.  Each relation is in one of Knuth's lists and each vertex is removed from his queue at most once, so step T6 visits each relation at most once, and Algorithm T takes time proportional to `m + n`.

## The module sorts the vertices

`verified_compile compiled := [countPredecessors, initialQueue, process, topoSort]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `topoSort` is function 5.  The module allocates the array of counts and the growing queue, so its call needs room for the generated bound, which the [verified compiler manual](../../../docs/verified-manual.md#bounds-and-total-execution) describes.  The call theorem states the result as the Lean function `topoSort xs`, since an input can have several correct results, and `topoSort_spec` states the property of that function.

| Theorem | File | Statement |
|---|---|---|
| `countPredecessors_spec` | [The proof](Proof.lean) | The counts have one word per vertex, and each is the number of relations into its vertex. |
| `initialQueue_spec` | [The proof](Proof.lean) | The initial queue lists, in increasing order, the vertices whose count is 0. |
| `inner_step` | [The proof](Proof.lean) | One relation of the scan for the vertex at position `f` keeps the scan's invariant. |
| `outer_init`, `outer_step`, `process_spec` | [The proof](Proof.lean) | The counts and the initial queue meet `OuterInv`, each step of the main loop keeps it, and it holds at the end of the loop. |
| `topoSort_spec` | [The proof](Proof.lean) | On a valid input with fewer than `2^64` words, `topoSort xs` is a topological order, or it is the empty array and no topological order exists. |
| `topoSort_export` | [The compilation](Compiled.lean) | Export `topoSort` of `compiled.module` is function 5. |
| `topoSort_call` | [The compilation](Compiled.lean) | Function 5, called from a ready store with room for `compiled.topoSort.bound xs` bytes, returns without a trap the owned array `topoSort xs` and leaves a ready store. |
| `topoSort_file`, `topoSort_file_decode` | [The file theorems](File.lean) | `build/verified/topoSort.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The equation of `InnerInv` shows that a count is at least 1 whenever the scan decreases it, so the subtraction, which the program applies only to counts other than 1, does not wrap.  At the end, a queue of `n` vertices is a topological order.  A shorter queue leaves every vertex outside it with a predecessor outside it, and in any order the first vertex outside the queue has such a predecessor, which the order must put before it, so no topological order exists.  The axiom reports of `topoSort_call` and `topoSort_spec` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Graphs.TopologicalSort.Compiled
tests/verified/run.sh --cases topoSort
tests/native/verified.sh --module topoSort
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../README.md#commands).  The cases come from `topoInputs` in [the case inputs](../../../tests/TestSupport/Modules/TopologicalSort.lean): no vertices, vertices without relations, 1,000 vertices without relations, chains in both directions, a diamond, repeated relations, relations of a vertex to itself, cycles of two, three, and 40 vertices, a cycle reachable from an acyclic part, arbitrary relations among 20 and 40 vertices, and invalid inputs, on which the module computes the Lean function: the empty array, an even number of words, a vertex at or above the count, and a relation with the count 0.  [The verified library cases](../../../tests/TestSupport/LibraryCases.lean) print each input with the result of the Lean function `topoSort`.  [The verified driver](../../../tests/verified/run.sh) runs the cases in Wasmtime and checks the file theorems, and [the native driver](../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 1: Fundamental Algorithms, third edition, Addison-Wesley, 1997, section 2.2.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
