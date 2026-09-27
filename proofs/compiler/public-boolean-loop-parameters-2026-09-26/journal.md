# Boolean public inputs in bounded loops

The range fallbacks now use the same typed public bindings as pure scalar
functions. Source support records the actual argument kinds. The common argument
matching theorem applies to every loop state because Boolean normalization reads
only the captured parameter slots. Public lambda annotations remain checked.
Word accumulators and word results are retained in this increment.

The source application proofs for both yielding and early-exit ranges derive
source body evaluation at decoded public values, then apply the original typed
lambdas. They reuse the existing range iteration and state proofs. Extraction
acceptance and source/IR correctness pass on the first focused build.

The descriptor, arithmetic-membership and read-bound proofs now share one
ScalarArithmeticBounded invariant. Its constructors cover literals, locals,
primitives and comparison choices; Boolean normalization uses the same choice
case. Both range admission proofs accept typed bindings satisfying that invariant,
with public-parameter and existing word-local specializations. This removes
repeated descriptor proof code while keeping the existing emitter and validator.
The first helper name used Lean's reserved word public; renaming it to bindings
resolved that syntax error. All three focused backend admission targets pass.

Ten original native functions pass 240 native/IR comparisons. They cover ordinary
loops, break, continue, both argument orders, both Boolean arguments, captured
helpers before and inside loops, aliases, Id binds, bounds and final expressions.
Counts derived from arbitrary word fixtures are reduced modulo seventeen.

The raw matrix varies argument order, negations, aliases, yielding/early-exit/skip
steps, all binder metadata kinds, nested Id results and let dependency flags.
It passes 8,064 native/IR comparisons and 4,032 invalid-input checks. The first
matrix elaboration required explicit Nat annotations on its counters. Rejections
cover Boolean/word confusion, malformed lambda domains, unused invalid bindings,
unexecuted invalid branches and unsupported source terms.

The general compiler theorem and nineteen audits pass. Native Lean/V8 agree on 529 inputs across 28 declarations, including fifteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1096 declarations.
