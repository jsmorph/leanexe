# Binary Boolean helper declarations in loop steps

Preserve six fixed probes that declare two-UInt64-input Boolean helpers directly
in for-loop bodies. Cover captured accumulator/index values, break, continue,
retained result annotations, nested/repeated helper calls, unused helpers and
saved call results. Keep declarations around whole loops as a separate increment.

Reuse BooleanBinaryHelper's exact declaration syntax and the distinct scalar
binary predicate kind. Loop-step source and compiled environments already wrap
scalar values, so add a step declaration rule without another function-kind
representation. Check unused helper bodies with two typed placeholders. Function
closures use the scalar Boolean conversion checker and capture the current step
values. Compile the continuation with a scalar binary predicate binding.

Prove step source totality, extraction equations, evaluation preservation,
admission, source reconstruction and IR invariants in bounded modules. Keep all
existing step function kinds distinct. Complete fixed probes, native/malformed
syntax tests, source-to-WASM proofs and independent V8 execution before advancing.
Update task.md, archive source/module hashes and logs, commit and push frequently.
