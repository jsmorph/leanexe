# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the case inputs](../../../tests/TestSupport/Modules/TopologicalSort.lean) against [the request](request.txt), from the files alone.

The first review found no disagreement between the specification and the request.  It confirmed that `IsTopologicalOrder` makes the result a permutation of the vertices below `n` that respects every relation, that a relation of a vertex to itself admits no order, and that for `n = 0` the theorem forces the empty array.  It found that the comment did not state that a repeated relation means the same as one copy, which the comment now states.  It found the arbitrary samples repetitive and the docstring wrong about them: the samples in arbitrary directions all admitted an order although the docstring said they might not, and one sample went undescribed.  The generator of arbitrary vertices now takes the high bits of each word, the samples changed, and the docstring describes each sample.  It named classes without inputs: invalid inputs, a cycle with a repeated relation, a relation of vertex 0 to itself as the only vertex, a relation of a vertex to itself among other relations, a long cycle, a count much larger than the number of relations, and many relations.  The inputs now include an input of each class, the last two as 1,000 vertices without relations and 400 relations among 40 vertices.

The second review found no disagreement.  It found two omissions.  The comment did not state that `Valid` puts no bound on `n`, so that `[2^64 - 1]` is well formed and its only orders hold `2^64 - 1` words.  The docstring did not state which samples in arbitrary directions admit an order.  Both now state these facts.  The module cannot allocate such an order, and `topoSort_call` assumes room for `compiled.topoSort.bound xs` bytes, which excludes these inputs.  It recorded these classes without inputs:

| Class | Why the cases leave it out |
|---|---|
| Relations on vertices above 39 | The 1,000-vertex input has no relations. |
| A vertex count far larger than the input | Such an input needs memory for `n` words.  `topoSort_spec` covers it. |
| Long paths among relations in arbitrary directions | In the 40-vertex samples every relation goes from a vertex without predecessors to a vertex without successors.  Long paths appear in the chains and the forward samples. |
| A vertex reachable from a cycle but outside it | No input has one.  The algorithm never releases such a vertex, and the result is empty in either case. |
| Arbitrary relations with varied residues | `vertexOf` keeps residues modulo 4 nearly constant over runs of indices, so each arbitrary sample uses half of the residues, and many relations repeat. |
