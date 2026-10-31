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
conversions and lemmas.  Ordering and membership proofs for search-tree insertion remain future
work.

[The tree example](../../Examples/Trees/README.md) adds operations of its own over `KeyTree`, which
no verified module compiles.  Its test support constructs and renders arbitrary trees, including
trees that exceed the guarded recursion limit.  [The recursive-type
cases](../../Verified/Examples/RecursiveTypesCases.lean) use that support to test the library's