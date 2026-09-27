# General predicate bodies in loop steps

The fixed loop probes show that scalar-only word updates, unused word helpers and
a continue example already compile after the scalar word-continuation change.
The Boolean-input helper before break still fails. Both outer-loop helper probes
also fail, but belong to a separate subsequent capability.

Generalize only Step.Eval/Supported letPredicateFn and letBooleanPredicateFn body
parameters from BooleanLocal to Lean.Expr. Their premises already use scalar
EvalWith/SupportedWith of Bool.toUInt64(body), so the scalar theorem supplies the
required Boolean encoding, totality and invariant. Remove the redundant body
parse in extractScalarStepWith and preserve exact domain/result annotation
checks and the mandatory zero-input validation. Preserve loop result/done flags.

Update ScalarStepEquations, Supported, Correctness and Invariant where they refer
to the raw body. Inspect the generated functional induction signature. These two parsers use an
Option bind, so case numbers should stay unchanged while the body-parse argument
to each continuation hypothesis disappears. Check both input kinds, breaks,
continues, dependent branches, captures and unused helpers, including malformed
unused bodies. Keep step semantics separate from scalar word continuations and
from outer-loop helper declarations. Do not claim the latter until their own
proof and WASM checks pass.
