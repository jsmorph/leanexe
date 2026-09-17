# GPT numerical audit

This audit separates sensitivity of the specified real function, rounding
introduced by the implemented algorithm, and overestimation in the proof.
It retains the single cap of 4 on all parameters. Checkpoint observations
are diagnostics rather than replacements for that universal contract.

The implementation under audit is width 4 with a binary64 hidden computation,
binary32 WGSL head and binary64 bias addition. It is not an all-binary32 GPT-2.
No Wasm or WGSL artifact is changed by these diagnostic tools.

## Baseline evidence

`node tools/wgsl/audit/baseline.js` checks six cases: the three recorded
checkpoint contexts, opposite-sign adversarial position embeddings, and their
zero-position control. It verifies 24 hidden words against the existing
hash-identified Wasm, memory preservation, and 768 mixed logits against the
recorded native execution. An independent BigInt reference evaluates the real
formulas at 80 and 120 decimal places. Its precision agreement is a diagnostic,
not a rigorous interval enclosure or a new Lean theorem.

The checkpoint hidden errors are at most 1.87e-15 and its recorded mixed-logit
errors at most 7.62e-7. Opposite adversarial parameters yield ideal logits
approximately +59.9258 and -59.9196 while both native hidden rows are zero.
The [counterexample argument](counterexample.md) states the exact scope and
the strict mathematical separation. `node tools/wgsl/audit/inequalities.js`
checks its rational inequalities.

The detailed sensitivity, stage-rounding and bound-propagation audits are in
progress. No optimality claim is made for the existing estimates or algorithms.

## Concurrent parent work

Parent `main` at `9fb277da` adds checked runtime-weight inference and caps
its binary64 error theorem by `1260 + 12*B^2 + B` (1456 at B=4).
That is a sound coarse magnitude cap, not an accuracy certificate. The WGSL
checkout was fast-forwarded to the notes commit `385b05d3`; the separate
parent implementation and artifact additions were inspected without changing
the artifacts measured by this audit.
