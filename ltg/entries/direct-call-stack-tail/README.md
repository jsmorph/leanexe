# Direct calls with retained stack operands

`Wasm.TerminatesWith.append_args` extends a callee theorem on `args` to a
call on `args ++ rest`.  Its postcondition supplies `out`, the equation
`values = out ++ rest`, and the original callee postcondition on `out`.
`Wasm.wp_call_tw` then composes this theorem with the caller continuation.
The internal-function lookup and exact argument count are required premises.
The theorem preserves the original termination threshold and store relation.

The stack lists place the top operand first.  A caller may stage a comparison
operand before it stages and calls a helper.  That earlier operand is the
suffix `rest`.  Reading the decoded instruction sequence identifies its value
and order.  The direct-call annotation identifies the call but supplies no
proof that the caller stack has the required decomposition.

The Euler outward-division proof uses `append_args` with suffix `[.i64 0]`
for an absolute-value call followed by an unsigned positivity test.  Its
checked proof then destructures the existential result before continuing.
If a continuation tactic also executes the following branch, the branch
hypotheses must be available before applying that tactic.

Both shared declarations and the division execution theorem check with the
standard logical axioms.  The complete speed source-driven and independent
exact-byte gates pass.  The reconstruction minmod proof also uses the
theorem, preserving the first absolute value across the second call.
That generated-WASM component checks with standard axioms.  The complete reconstruction source-driven and independent exact-byte
gates pass.  The entry remains
provisional, with measured proof-agent retrieval still open.
