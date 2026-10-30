# LTG knowledge base

This directory holds lemmas, tactics, and proof guidance for the LeanExe compiler and the shared
pipeline, and its name LTG abbreviates lemmas, tactics, and guidance.  The verified compiler's general correctness theorem covers its source constructs.
Each entry is a directory under [`entries/`](entries).  `entry.json` names the entry's
modules, declarations, premises, result, and the hint rules (`annotationKinds`)
that select it, and `README.md` explains when and how to apply it.

A prover finds entries by searching this directory, for example for a hint's
rule name or a declaration it needs.  The check below imports every module the
entries list and reports each listed declaration that does not exist.  Run it
from the repository root:

```sh
tools/leanrun --timeout 10m lake env lean --run ltg/Check.lean ltg/entries
```

A compiler-rule entry is proved for every function its rule
produces, and a proof applies the entry's rule lemma where a hint names the rule.  A lemma entry
holds general facts that rule proofs and hand proofs use, and the library entry is a proved
function that any module can compile and call.

| Entry | Use |
|---|---|
| [Straight-line evaluation](entries/straight-line-run/README.md) | Proves a statement triple by computing assignments, reads, and conditionals. |
| [Binary64 operations](entries/float-arithmetic/README.md) | Relates float operations, comparisons, and sign changes to their raw-word semantics. |
| [Binary32 operations](entries/binary32-arithmetic/README.md) | Follows `Float32` arithmetic and conversions through the `f32` expressions. |
| [Array reads](entries/array-read/README.md) | Proves a bounds-checked read, including the default after the array's end. |
| [Array size](entries/array-size/README.md) | Recovers the array length from its stored header. |
| [Array literals](entries/array-literal/README.md) | Proves allocation, length storage, and element initialization for a word-array literal. |
| [Copying array builds](entries/array-build/README.md) | Proves copying implementations of builds, updates, insertions, and removals. |
| [Array-fold loop](entries/array-fold-loop/README.md) | Applies the fold template's accumulator invariant. |
| [Float-array folds](entries/float-array-fold/README.md) | Connects the stored bit-pattern array with a fold over Lean floats. |
| [Fold-prefix equations](entries/array-fold-prefix/README.md) | Advances an invariant stated over the first `index` elements. |
| [Array-valued loop state](entries/array-state-loop/README.md) | Proves an `Array Float` loop whose step calls consume and return the array. |
| [In-place updates](entries/in-place-update/README.md) | Proves updates and capacity growth for an owned array at its last use. |
| [Temporary-array release](entries/release-temporary/README.md) | Proves release of a temporary while preserving the caller's other arrays and regions. |
| [Record-array reads](entries/record-read/README.md) | Recovers typed components from a flat array of multiword elements. |
| [Record-array builds](entries/record-build/README.md) | Proves a build whose loop body supplies each element's component words. |
| [Calls returning one array](entries/one-array-call/README.md) | Composes calls whose result combines scalars with one owned array. |
| [Index loops](entries/index-loop/README.md) | Proves loops with scalar or tuple state and an explicit index. |
| [Conditional loops with step calls](entries/repeat-while/README.md) | Carries ownership through a condition and a call that replaces the state. |
| [Scalar tail recursion](entries/tail-recursion-loop/README.md) | Reduces a tail-recursive function proof to one iteration and a decreasing measure. |
| [Represented tail arguments](entries/tail-recursion-records/README.md) | Applies the tail-loop rule to borrowed recursive values. |
| [Guarded recursive calls](entries/recursive-calls/README.md) | Proves internal recursion and its depth-zero exported entry. |
| [Consumed recursive values](entries/consumed-recursion/README.md) | Proves a recursive rebuild that consumes an input tree and owns the rebuilt result. |
| [Calls between compiled functions](entries/function-call/README.md) | Uses a callee's execution theorem inside another function. |
| [List cells](entries/list-cell/README.md) | Represents empty lists and allocated cons cells. |
| [List folds](entries/list-fold-loop/README.md) | Proves traversal of borrowed list cells with a scalar accumulator. |
| [List and tree release](entries/release-list/README.md) | Proves release of a call's list or tree result, preserving the caller's heap regions. |
| [Recursive-value matches](entries/node-match/README.md) | Splits null and record cases and recovers their fields. |
| [Record reuse](entries/record-reuse/README.md) | Proves a word-slot update that retains a consumed record's pointer and storage. |
| [Partial tree release](entries/partial-release/README.md) | Proves release of the record and children left behind when a branch moves other children. |
| [Tree copying](entries/tree-copy/README.md) | Proves the recursive copy used when a borrowed tree enters an owned position. |
| [Array memory framing](entries/array-memory-framing/README.md) | Preserves an array representation across disjoint writes. |
| [Memory-write intervals](entries/memory-write-range/README.md) | States which bytes and store fields a write leaves unchanged. |
| [Region preservation](entries/region-frame/README.md) | Composes preservation of the caller's heap regions through calls and releases. |
| [Local-frame projections](entries/local-frame-projection/README.md) | Reads raw Talos locals through frame equalities in low-level runtime proofs. |
| [Retained stack operands](entries/direct-call-stack-tail/README.md) | Extends a call theorem while keeping the operands below its arguments. |
| [WGSL kernels](entries/wgsl-kernel/README.md) | Derives a dispatch theorem from the compiled array-build body. |
| [SplitMix64](entries/splitmix64/README.md) | Reuses the generator and word-to-float proofs inside another module. |

No entry yet describes the abort-flag rules and heap budgets of complete execution (`ImplementsA`,
`Heap.Budget`, and `Heap.Bounded`).  [`Demos/Euler/Total.lean`](../Demos/Euler/Total.lean),
[`Demos/Drone/Total.lean`](../Demos/Drone/Total.lean), and
[`Examples/Increment/Verify.lean`](../Examples/Increment/Verify.lean) show their use.

## Internal References

- [LeanExe Compiler Manual: Proving](../docs/leanexe-manual.md#proving)
