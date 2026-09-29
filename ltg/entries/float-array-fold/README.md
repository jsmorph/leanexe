# Float array folds

Use this entry when an `array-fold-loop` hint's source folds over an `Array Float`.  `Represent (Array Float)` stores an `Array Float` as the `Array UInt64` of its elements' bit patterns, so a borrowed argument gives `heap.Borrowed initial ptr (xs.map Float.toBits)`, and `Heap.Borrowed.values` gives the layout `Stmt.fold_spec` needs.  Choose the fold function `g` on bit patterns so that each step of the source fold maps to it, for example `g a e = IEEE64.add a (IEEE64.mul e e)` for `fun acc x => acc + x * x`.

Core's `Array.foldl_map` turns `(xs.map Float.toBits).foldl g (h init)` into a fold over `xs`, and `Array.foldl_hom h hg` finishes with `h (xs.foldl f init)`.  Take `h = Float.toBits` for a `Float` accumulator and `h = id` for a `UInt64` accumulator, and prove the step premise `hg` with `simp` and the `F64Bits.toBits_*` lemmas.  A literal starting value such as `0.0` needs its bits first: `(0.0 : Float).toBits = 0` holds by `decide`.

Close the result equation with `congrArg` and the conversion lemma, not with `simp`.  `simp` rewrites `(xs.map Float.toBits).size` to `xs.size` inside `Array.foldl`'s default `stop` argument, after which the conversion lemma no longer matches.  `Project.SumSquares.sumSquares_implements` is the worked example: 21 lines including the statement, and a 7-line lemma for the conversion.
