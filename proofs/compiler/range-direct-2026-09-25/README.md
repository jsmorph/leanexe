# Direct range-step constructors

Candidate `37cef9bf` adds direct `ForInStep.done` and `ForInStep.yield`
expressions in bounded range callbacks and local continuations. Both ordinary
unary functions and Unit-prefixed functions can return the unwrapped step type.
The source grammar, totality, acceptance, successful-admission, paired result
preservation and scalar-invariant proofs cover the new constructor forms.
The existing four-local early-exit loop and WebAssembly proofs are reused.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: complete general source-to-module theorem,
  validation and exported execution, with all nine permitted-axiom audits.
- `tools/arithmetic-check.js range-engine`: source admission, reserved exports,
  and 673 matching native Lean/V8 results across twenty-nine range declarations.

The three added fixtures cover direct callback constructors and both local
continuation shapes. They include yielding before done, updated return values,
zero iterations, captures, high-bit values and wrapping arithmetic. An unused
direct-returning function with an unsupported body remains rejected. The
focused native/IR test also passed all 216 comparisons across nine declarations.

All twenty-nine modules and native expected results are retained here, with
sizes and SHA-256 hashes in `verification.json`. The twenty-six existing range
modules are byte-for-byte identical to the preceding break milestone. The full
sixty-three-declaration suite is configured for 1,110 results; this increment
ran the focused range group. The fixed arithmetic source archive and unrelated
independent runtime/type-safety suite were not rebuilt; affected proof
modules, including general type validation, used cached dependencies.
