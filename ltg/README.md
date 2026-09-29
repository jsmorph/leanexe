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

`tail-recursion-loop` and `array-fold-loop` cover compiler rules and are proved
for every function those rules produce.  The other five entries describe general
lemmas from the earlier proof library.  `array-fold-prefix` supports
`array-fold-loop`, and the rest cover memory framing, calls, and raw WASM locals
for the next iterations.
