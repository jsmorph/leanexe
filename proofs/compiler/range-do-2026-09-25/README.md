# Monadic bindings inside yielding range steps

Candidate `728098c4` admits standard Id monadic UInt64 bindings inside a yielding
range body. The syntax relation changes the continuation result from
ForInStep UInt64 to UInt64 while retaining the exact standard Bind instance,
bound computation, binder and scalar continuation. The scalar extractor checks
the complete result, including unused values. No backend representation changed.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general correctness, complete module
  validation/invocation and all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: source admission, reserved exports,
  and 289 matching native Lean/V8 results across thirteen range declarations.

Three new modules cover consecutive binds, conditional scalar values inside
pure, nested do computations, captures through local functions and unused
monadic values. Custom Bind evidence and a break following a bind are rejection
cases. Native expected results and the new modules are retained here.

The first attempt used a conditional monadic computation whose elaboration
introduces a local continuation returning Id (ForInStep UInt64). That separate
branching form was rejected; the failed log is retained and the following
increment will cover it. This checkpoint supports straight-line Id binds,
including `pure (if … then … else …)`, without claiming general body branching.

Only affected proof dependencies and the fixed range execution group were
checked. Unchanged arithmetic fixtures, the fixed source archive and independent
runtime/type-safety suites were not rebuilt.
