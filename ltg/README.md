# LTG knowledge base

This directory holds proof knowledge for the pipeline: lemmas, tactics, and
guidelines that a prover can use on a compiled program.  Each entry is a
directory under `entries/` with two files.  `entry.json` names the entry's
modules, declarations, premises, result, and the hint rules (`annotationKinds`)
that select it, and `README.md` explains when and how to apply it.

A prover finds entries by searching this directory, for example for a hint's
rule name or a declaration it needs.  The check below imports every module the
entries list and reports each listed declaration that does not exist.  Run it
from the repository root:

```sh
tools/leanrun --timeout 10m lake env lean --run Project/LTG/Check.lean ltg/entries
```

The 37 entries fall into four groups.  The compiler-rule entries are proved for every function
their rules produce; a proof applies the entry's rule lemma where the hint names the rule.  The
lemma entries hold general facts that rule proofs and hand proofs use, and the library entry is a
proved function that any module can compile and call.

| Group | Entries |
|---|---|
| Words and floats | `straight-line-run`, `float-arithmetic`, `binary32-arithmetic` |
| Arrays | `array-read`, `array-size`, `array-literal`, `array-build`, `array-fold-loop`, `float-array-fold`, `array-fold-prefix`, `array-state-loop`, `in-place-update`, `release-temporary` |
| Records | `record-read`, `record-build`, `one-array-call` |
| Loops and recursion | `index-loop`, `repeat-while`, `tail-recursion-loop`, `tail-recursion-records`, `recursive-calls`, `consumed-recursion` |
| Calls | `function-call` |
| Lists and trees | `list-cell`, `list-fold-loop`, `release-list`, `node-match`, `record-reuse`, `partial-release`, `tree-copy` |
| General lemmas | `array-memory-framing`, `memory-write-range`, `region-frame`, `local-frame-projection`, `direct-call-stack-tail` |
| Kernels and library | `wgsl-kernel`, `splitmix64` |

No entry yet describes the abort-flag rules and heap budgets of complete execution
(`ImplementsA`, `Heap.Budget`, and `Heap.Bounded`); `Project/Euler/Total.lean`,
`Project/Drone/Total.lean`, and `Project/Increment/Verify.lean` show their use.
