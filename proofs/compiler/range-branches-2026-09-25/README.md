# Yielding branch continuations and continue

Candidate `1cfb4228` admits branching continuations inside a yielding range
step. The independent source YieldType relation removes the ForInStep result
wrapper through function types while preserving domains, names and binder
information. Yield syntax conversion transforms continuation definitions and
both branches together; calls retain their argument expressions and binding
positions. The existing scalar grammar checks the full transformed term,
including comparison/Id evidence, function arities and unused bodies.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general correctness, complete module
  validation/invocation and all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: source admission, reserved exports,
  and 385 matching native Lean/V8 results across seventeen range declarations.

The four new modules cover the conditional monadic join rejected during the
previous increment, mutable branch updates followed by computation, continue,
and nested branch continuations. Native expected results and the new modules
are retained here. Continue yields the current accumulator and advances the
range index, so the existing finite-iteration execution proof applies unchanged.

Breaks still reject, as do unused done-returning functions and custom comparison
evidence. The recognizer checks all branch and continuation bodies. This
increment changes source syntax handling; it reuses the existing scalar IR,
Wasm loop layout, validator and execution proof.

Only affected proof dependencies and the fixed range execution group were
checked. Unchanged arithmetic fixtures, the fixed source archive and independent
runtime/type-safety suites were not rebuilt.
