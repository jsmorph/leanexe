# Word trees

[The native type](WordTree/Program.lean), `KeyTree`, has an empty constructor and a node with two
children and a word key.  Its functions count nodes, sum keys, compute height, increment keys,
replace a root key, insert a key by binary-search-tree comparisons, select the left child, and
split the root into its children.  Word results wrap modulo `2^64`.

[The encoding](WordTree/Encoding.lean) represents an empty tree by null and a node by a record with
fixed word and child fields.  [The compiled module](WordTree/Compiled.lean) proves execution under
the verified compiler's representation, ownership, memory, and recursion premises.  [The
derivation](WordTree/Reflected.lean) runs `verified_recursive_type` for `KeyTree` in a module apart
from the encoding, so that the verified compiler's programs over the type share one set of
conversions and lemmas.

[Tree search and insertion](Search/README.md) states Knuth's Algorithm T on `KeyTree` and proves
that the library's `insert` gives the tree of Algorithm T, keeps a binary search tree a binary
search tree, and adds the new key to the keys of any tree.  Its module compiles a search and an
insertion that run as loops, so a tree of any depth needs no call-depth premise.

[The tree example](../../Examples/Trees/README.md) adds operations of its own over `KeyTree`, which
its verified compilation compiles, with the library's `size`, `sum`, `incr`, and `insert`, into the
module `exampleTrees`.  Its test support constructs and renders arbitrary trees, including
trees that exceed the guarded recursion limit.  [The recursive-type
cases](../../Verified/Examples/RecursiveTypesCases.lean) use that support to test `size`, `incr`,
`setKey`, `leftChild`, and `splitRoot` on chains of up to 4,096 nodes and on arbitrary trees, and
`tests/verified/run.sh` runs those cases on the library's module as well, as
`tests/verified/library-cases.txt` maps them.
