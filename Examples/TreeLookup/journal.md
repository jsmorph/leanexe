# Tree lookup: journal

This is the first run of the verified-executable skill, on main's Demo 3 request (2026-10-05).

The specification states the request's traversal as a recursive `search` over breadth-first node
numbers, with node `j`'s key at `2j + 1`, its value at `2j + 2`, its children at `2j + 1` and
`2j + 2`, and nodes 3 to 6 as leaves.  The request decides every input, including keys out of
search-tree order, so the specification adds no decisions.  The samples cover each of the seven
keys of one search tree, four misses, a tree out of order, a tree with a key in both subtrees, and
inputs of 0, 1, 14, and 16 words.  The user approved the specification and the 17 samples.

The user then replaced approval by an independent review.  A fresh agent, given only the request,
the specification, and the samples with their outputs, found no disagreement and named five
uncovered input classes, and the run added one sample for each.  A second fresh agent found no
disagreement in the 22 samples and named further classes, recorded in [`review.md`](review.md), and the
specification was frozen.  The skill now ends the review at the first review that finds no
disagreement, after the samples for the named classes are added once.

The program follows the lookup example: a loop of one step per level whose state carries the node
number, a found flag, and the value, so the search needs no early exit, and a two-word literal for
the result.  The samples passed in Wasmtime at the first compilation.  `compute_eq` first failed
in two ways.  The program compared `key == query` and the specification `query = key`, so after a
match was substituted the leaf goals held the same equality in both orientations, and `simp_all`
looped between the hypotheses.  Writing `query == key` in the program and closing each leaf with
`subst` for a match and `simp` with the named comparisons for a miss fixed both.  The
`Implements` proof was the lookup example's with three state locals instead of two, and it
compiled after one change: `simp [State.Holds, Scalar.values] at hHolds` splits the facts of a
three-component state, where `simp only` with `List.forall₂_cons` left an `append`.  The lookup
example's proof served as a template that needed only its indices changed, which suggests a
general rule for a loop with a tuple state followed by an array literal.
