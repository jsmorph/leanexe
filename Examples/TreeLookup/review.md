# Tree lookup: review of the specification

Two fresh agents reviewed [`Examples/TreeLookup/Spec.lean`](Spec.lean) and `Samples.lean` against the request.
Each saw only the request, the two files, and the samples with the outputs of `expected`.

The first review found no disagreement between `expected` and the request.  It checked the index
arithmetic of every node, the order of the tests, where the search stops, unsigned comparison,
and the lengths, agreed that the request leaves no case open, and computed all 17 samples by hand
with the same outputs.  It named five input classes the samples did not cover: a key of 2^63 or
more, which separates unsigned from signed comparison; a matched value of 0; the query equal to two
keys on one search path; words of 2^32 or more; and a miss at the left subtree's right leaf.  One
sample for each class was added.

The second review, of the 22 samples, again found no disagreement and computed every output by
hand with the same results.  It noted that the comment of the second tree out of search order
names the key 40 in the right subtree but not the key 40 at the left subtree's left leaf, where
the search finds it.  The comment is correct but incomplete.  It named further classes without
samples: a matched key or value of 0 below the root, a repeated key at node 1 or 2 with a match
below it, out-of-order keys on a right-subtree path that ends in a match, values of 2^63 or more,
and lengths far from 15.  The stage ends with these notes, since neither review found a
disagreement with the request.  After the second review, one line of `Samples.lean` was wrapped
to 100 columns with no other change, and the specification was frozen.

On 2026-10-05 the reorganization of the branch moved the specification and samples to
`Examples/TreeLookup/` and renamed their namespace from `Project.TreeLookup` to
`Examples.TreeLookup`, and changed the request's path in the specification's comment, with no
other change.  `tools/demo-check --freeze` then recorded the hashes
of the renamed files.
