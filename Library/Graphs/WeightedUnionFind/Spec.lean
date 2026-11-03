import Library.Graphs.UnionFind.Spec

/-! The specification of equivalence classes with path compression and union by size is
`LeastLabels` of the module of Algorithm E, which `Library.Graphs.UnionFind.Spec` defines: `r` holds
`n` words, and word `i` is the least element of the class of `i`, where pair `t`, for `t` below the
lengths of both arrays, relates its elements when both are below `n`.  The specification names the
result and not the method, so it does not distinguish path compression, union by size, the sizes
kept at the roots, or the direction of a link, and the program text shows them.  The theorems
require room in memory for four arrays of `n` words: the parent links, the sizes, the least element
recorded at each root, and the result.  The specification reads "in place" as the update of the
parent links and the sizes in their own blocks, which rests on the compiler's rule that the code
updates an owned array at its last use in place, a rule that the verified compiler's manual states
and no theorem states, and the generated bound of four arrays for any number of pairs supports it.
It reads "a call stack that does not grow" as theorems with no call-depth premise, which rests on
the manual's rule that the compiler translates recognized tail recursion into loops and gives every
other recursive function and its callers a call depth, which their theorems carry as a premise. -/
